//! Control flow decompilation.
//!
//! Recognizes various control flow structures in decompiled code and uses them to make
//! the output more expressive.

use std::collections::{BTreeMap, HashMap};
use crate::error::SimpleError;
use crate::ast::{self, VisitMut};
use crate::ident::Ident;
use crate::pos::Sp;

/// Decompiles `if { ... } else if { ... } else { ... }` chains.
pub fn decompile_if_else<V: ast::Visitable>(ast: &mut V) -> Result<(), SimpleError> {
    let mut visitor = IfElseVisitor { label_refcounts_stack: vec![] };
    ast.visit_mut_with(&mut visitor);
    Ok(())
}

/// Decompiles `loop { ... }` and `do { ... } while (<cond>)`.
pub fn decompile_loop<V: ast::Visitable>(ast: &mut V) -> Result<(), SimpleError> {
    let mut visitor = LoopVisitor { label_refcounts_stack: vec![] };
    ast.visit_mut_with(&mut visitor);
    Ok(())
}

// =============================================================================
// if-else decompilation

struct IfElseVisitor {
    // whole-function-body label refcounts at the beginning of the procedure
    label_refcounts_stack: Vec<HashMap<Ident, u32>>,
}

impl VisitMut for IfElseVisitor {
    fn visit_root_block(&mut self, block: &mut ast::Block) {
        self.label_refcounts_stack.push(get_label_refcounts(&block.0));
        self.visit_block(block);
        self.label_refcounts_stack.pop();
    }

    fn visit_block(&mut self, outer_block: &mut ast::Block) {
        let mut new_stmts = Vec::with_capacity(outer_block.0.len());

        let context = BlockContext::from_block(outer_block, self.label_refcounts_stack.last().expect("must use on a function body!"));

        let original_len = outer_block.0.len();

        // FIXME: temporary hack (we probably should put more time info in BlockContext);
        //        I plan to get rid of the stmt.time field and turns time labels into statements,
        //        so this should become unnecessary then.
        let stmt_times = outer_block.0.iter().map(|stmt| stmt.time).collect::<Vec<_>>();
        let mut index = 0;
        let mut stmt_iter = outer_block.0.drain(..);
        while index < original_len {
            match gather_cond_chain(index, &stmt_times, &context) {
                Err(NoCondChain) => {
                    new_stmts.push(stmt_iter.next().unwrap()); index += 1;
                },

                Ok(CondChainInfo { chain, else_start_index, end_label_index }) => {
                    let mut cond_block_asts = vec![];
                    for cond_block in chain {
                        // read all of the statements from the jump to the label (inclusive of both)
                        assert_eq!(index, cond_block.if_index);

                        let inner_block_len = cond_block.label_index + 1 - cond_block.if_index;
                        let mut inner_block = ast::Block(stmt_iter.by_ref().take(inner_block_len).collect());
                        index += inner_block_len;

                        let cond_block_span = inner_block.start_span().merge(inner_block.end_span());

                        // get rid of the original jumps and the label
                        assert!(matches!(inner_block.0.pop().unwrap().value.body, ast::StmtBody::Label { .. }));  // remove label
                        let last_stmt = inner_block.0.last_mut().unwrap();
                        last_stmt.body = ast::StmtBody::NoInstruction;  // replace unconditional jump with bookend
                        last_stmt.span = cond_block_span.start_span();
                        inner_block.0[0].body = ast::StmtBody::NoInstruction;  // replace conditional jump with bookend
                        inner_block.0[0].span = cond_block_span.end_span();

                        cond_block_asts.push(sp!(cond_block_span => ast::CondBlock {
                            keyword: cond_block.keyword,
                            cond: cond_block.cond,
                            block: inner_block,
                        }));
                    }

                    let else_block;

                    assert_eq!(index, else_start_index);
                    if else_start_index <= end_label_index {
                        let inner_block_len = end_label_index - else_start_index;
                        let inner_block = ast::Block(stmt_iter.by_ref().take(inner_block_len).collect());
                        assert_eq!(inner_block.0.len(), inner_block_len);
                        index += inner_block_len;

                        else_block = Some(inner_block);
                    } else {
                        else_block = None;
                    }
                    assert_eq!(index, end_label_index);

                    let cond_chain = ast::StmtCondChain { cond_blocks: cond_block_asts, else_block };
                    let span = cond_chain.cond_blocks[0].block.0[0].span.merge(cond_chain.last_block().end_span());
                    new_stmts.push(sp!(span => ast::Stmt {
                        time: cond_chain.cond_blocks[0].block.0[0].time,
                        body: ast::StmtBody::CondChain(cond_chain),
                    }));
                },
            }
        }
        drop(stmt_iter);

        outer_block.0 = new_stmts;

        ast::walk_block_mut(self, outer_block);
    }
}

#[derive(Debug)]
struct CondChainInfo {
    chain: Vec<CondBlockInfo>,
    else_start_index: usize,  // body of else after label
    end_label_index: usize,
}
#[derive(Debug)]
struct CondBlockInfo {
    keyword: Sp<ast::CondKeyword>,
    cond: Sp<ast::Cond>,
    if_index: usize,
    label_index: usize,
}

struct NoCondChain;

fn gather_cond_chain(start: usize, stmt_times: &[i32], context: &BlockContext) -> Result<CondChainInfo, NoCondChain> {
    let mut chain = vec![];
    let mut src = start;
    let mut known_end = None;
    loop {
        // check for 'if (a <binop> b) goto <forward label>;'
        //
        // this .get() will fail if this stmt isn't a jump, or if the target label is
        // at a different block nesting level I guess
        let if_jmp = &context.jmp_info.get(&src).ok_or(NoCondChain)?;
        if if_jmp.time_arg.is_some() {
            return Err(NoCondChain);
        }
        if if_jmp.direction_given_src(src) == Direction::Backwards {
            return Err(NoCondChain);
        }
        let (if_keyword, if_binop_expr) = if_jmp.kind.as_binop_cond().ok_or(NoCondChain)?;  // screw predecrement

        // make sure there's only one reference to the dest label,
        // because for 'else if' there will be no place for us to put it
        if if_jmp.dest_refcount > 1 {
            return Err(NoCondChain);
        }

        // see integration test 'anm10_if_elseif_time_impossible_1'
        if stmt_times[if_jmp.dest] != stmt_times[if_jmp.dest - 1] {
            return Err(NoCondChain);
        }

        // see integration test 'anm10_if_elseif_time_sorta_possible'
        if stmt_times[if_jmp.dest] != stmt_times[if_jmp.dest + 1] {
            return Err(NoCondChain);
        }

        // just before the label, there should be an unconditional jump to the end of the construction.
        let uncond_src = if_jmp.dest - 1;
        let uncond_jmp = &context.jmp_info.get(&uncond_src).ok_or(NoCondChain)?;
        if uncond_jmp.time_arg.is_some() {
            return Err(NoCondChain);
        }
        if !matches!(uncond_jmp.kind, JmpKind::Uncond) {
            return Err(NoCondChain);
        }
        if uncond_jmp.direction_given_src(uncond_src) == Direction::Backwards {
            return Err(NoCondChain);
        }
        // all "jumps to end" must go to the same point, or else something's wrong.
        if *known_end.get_or_insert(uncond_jmp.dest) != uncond_jmp.dest {
            return Err(NoCondChain);
        }

        chain.push({
            // 'if (<expr>) goto skip' becomes 'if (!<expr>) { <block> }'
            //
            // Expect a simple comparison expression that is easy to negate.
            // (this is what we should expect from decompiled code)
            let sp_pat!(expr_span => (a, binop, b)) = if_binop_expr;
            let negated_binop = sp!(binop.span => binop.negate_comparison().ok_or(NoCondChain)?);
            CondBlockInfo {
                keyword: if_keyword,
                cond: sp!(expr_span => expr_binop!(#(a.clone()) #negated_binop #(b.clone()))).into(),
                if_index: src,
                label_index: if_jmp.dest,
            }
        });

        // is there another 'if' or was that it?
        src = if_jmp.dest + 1;
        if !matches!(context.jmp_info.get(&src), Some(JmpInfo { kind: JmpKind::Cond { .. }, .. })) {
            break;
        }
    }

    // now we find ourselves after the destination label of an 'if' with no 'else if'.
    // this could potentially be the body of an 'else' block.
    let else_start_index = src;
    let end_label_index = known_end.expect("we found at least one block so this was set");
    if end_label_index < else_start_index {
        return Err(NoCondChain);
    }

    // abort if there's an interrupt label anywhere in the chain (it would look confusing)
    let stmt_range = chain[0].if_index..end_label_index;
    if context.interrupt_label_indices.iter().any(|&i| stmt_range.contains(&i)) {
        return Err(NoCondChain);
    }

    Ok(CondChainInfo { chain, else_start_index, end_label_index })
}


// =============================================================================

// Get the number of jumps to each label.  Please be sure to only call this on the
// largest, outermost block of a function, or some jumps may be missed!
fn get_label_refcounts(block: &[Sp<ast::Stmt>]) -> HashMap<Ident, u32> {
    use ast::Visit;

    struct Visitor(HashMap<Ident, u32>);
    impl ast::Visit for Visitor {
        fn visit_goto(&mut self, goto: &ast::StmtGoto) {
            *self.0.entry(goto.destination.value.clone()).or_insert(0) += 1;
        }
        fn visit_root_block(&mut self, _: &ast::Block) {}  // ignore inner functions
    }

    let mut visitor = Visitor(HashMap::new());
    for stmt in block {
        visitor.visit_stmt(stmt);
    }
    visitor.0
}

// Records information about all of the jumps in a block that go to labels within the same block.
struct BlockContext {
    // key is index of jump statement
    jmp_info: BTreeMap<usize, JmpInfo>,
    interrupt_label_indices: Vec<usize>,
}

impl BlockContext {
    fn from_block(block: &ast::Block, refcounts: &HashMap<Ident, u32>) -> Self {
        let label_info = get_label_info(&block.0, &refcounts);
        let interrupt_label_indices = get_interrupt_label_indices(&block.0);
        let jmp_info = {
            block.0.iter().enumerate()
                .filter_map(|(i, stmt)| JmpInfo::from_stmt(stmt, &label_info).map(|x| (i, x)))
                .collect()
        };
        BlockContext { jmp_info, interrupt_label_indices }
    }
}

struct LabelInfo {
    stmt_index: usize,
    refcount: u32,  // number of jumps to this label
    time: i32,
}

/// For each label, get the index of its statement.
fn get_label_info(stmts: &[Sp<ast::Stmt>], refcounts: &HashMap<Ident, u32>) -> HashMap<Ident, LabelInfo> {
    stmts.iter().enumerate()
        .filter_map(|(stmt_index, stmt)| match &stmt.body {
            ast::StmtBody::Label(ident) => {
                let refcount = refcounts.get(&ident.value).copied().unwrap_or(0);
                Some((ident.value.clone(), LabelInfo { stmt_index, refcount, time: stmt.time }))
            },
            _ => None,
        }).collect()
}

/// Get a list of statement indices that are interrupt labels.
fn get_interrupt_label_indices(stmts: &[Sp<ast::Stmt>]) -> Vec<usize> {
    stmts.iter().enumerate()
        .filter_map(|(index, stmt)| match stmt.body {
            ast::StmtBody::InterruptLabel { .. } => Some(index),
            _ => None,
        }).collect()
}

// =============================================================================

struct LoopVisitor {
    // whole-function-body label refcounts at the beginning of the procedure
    label_refcounts_stack: Vec<HashMap<Ident, u32>>,
}

impl VisitMut for LoopVisitor {
    fn visit_root_block(&mut self, block: &mut ast::Block) {
        self.label_refcounts_stack.push(get_label_refcounts(&block.0));
        self.visit_block(block);
        self.label_refcounts_stack.pop();
    }

    fn visit_block(&mut self, outer_stmts: &mut ast::Block) {
        let mut reversed_out = vec![];

        let label_info = get_label_info(&outer_stmts.0, self.label_refcounts_stack.last().expect("must use on a function body!"));
        let interrupt_label_indices = get_interrupt_label_indices(&outer_stmts.0);

        // Dumb strategy: We just greedily replace the first backwards jump we find.
        while let Some(last_stmt) = outer_stmts.0.last() {
            match JmpInfo::from_stmt(&last_stmt, &label_info) {
                Some(JmpInfo { kind: jmp_kind, dest, time_arg: None, .. }) => {
                    let did_decompile = maybe_decompile_jump(outer_stmts, &mut reversed_out, &interrupt_label_indices, dest, jmp_kind);
                    if did_decompile { continue; }
                },
                _ => {},
            };
            // doesn't match what we're looking for
            reversed_out.push(outer_stmts.0.pop().unwrap());
        }
        // put them in the right order
        reversed_out.reverse();
        outer_stmts.0 = reversed_out;

        ast::walk_block_mut(self, outer_stmts);
    }
}

fn maybe_decompile_jump(
    outer_stmts: &mut ast::Block,
    reversed_out: &mut Vec<Sp<ast::Stmt>>,
    interrupt_label_indices: &[usize],
    dest_index: usize,
    jmp_kind: JmpKind,
) -> bool {
    // Is the label before the jump?
    let src_index = outer_stmts.0.len() - 1;
    if src_index < dest_index {
        return false;
    }
    // Don't let a loop contain an interrupt label because it's confusing to read.
    if interrupt_label_indices.iter().any(|&interrupt_i| {
        dest_index <= interrupt_i && interrupt_i < src_index
    }) {
        return false;
    }

    // replace the goto with an EndOfBlock, preserving its time
    outer_stmts.0.last_mut().unwrap().body = ast::StmtBody::NoInstruction;

    let new_block = ast::Block(outer_stmts.0.drain(dest_index..).collect());
    let inner_span = new_block.start_span().merge(new_block.end_span());

    reversed_out.push(sp!(inner_span => ast::Stmt {
        time: new_block.start_time(),
        body: jmp_kind.make_loop(new_block),
    }));
    // suppress the default behavior of popping the next item
    true
}

// =============================================================================

// Information about a jump from one statement in a block to another in the same block.
struct JmpInfo {
    dest: usize,
    dest_refcount: u32,
    time_arg: Option<Sp<i32>>,
    kind: JmpKind,
}

#[derive(Debug, PartialEq)]
enum Direction { Forwards, Backwards }

impl JmpInfo {
    fn from_stmt(ast: &ast::Stmt, label_info: &HashMap<Ident, LabelInfo>) -> Option<Self> {
        let (goto, kind) = match ast.body {
            ast::StmtBody::Jump(ref goto) => (goto, JmpKind::Uncond),

            ast::StmtBody::CondJump { keyword, ref cond, ref jump } => match keyword.value {
                ast::CondKeyword::If => (jump, JmpKind::Cond { keyword, cond: cond.clone() }),
                ast::CondKeyword::Unless => unimplemented!(),  // not present in decompiled code
            }

            _ => return None,
        };

        let label_entry = &label_info.get(&goto.destination.value)?;
        Some(JmpInfo {
            dest: label_entry.stmt_index,
            dest_refcount: label_entry.refcount,
            time_arg: goto.time.filter(|&x| x != label_entry.time),
            kind
        })
    }

    /// Direction of jump, given the index of the statement containing this jump.
    fn direction_given_src(&self, src: usize) -> Direction {
        if src < self.dest { Direction::Forwards }
        else { Direction::Backwards }
    }
}

enum JmpKind {
    Uncond,
    Cond { keyword: Sp<ast::CondKeyword>, cond: Sp<ast::Cond> },
}

type ExprBinopRef<'a> = (&'a Sp<ast::Expr>, Sp<ast::BinopKind>, &'a Sp<ast::Expr>);

impl JmpKind {
    fn as_binop_cond(&self) -> Option<(Sp<ast::CondKeyword>, Sp<ExprBinopRef<'_>>)> {
        match *self {
            JmpKind::Cond { keyword, cond: sp_pat!(ast::Cond::Expr(sp_pat!(span => ast::Expr::Binop(ref a, op, ref b)))) }
                => Some((keyword, sp!(span => (a, op, b)))),

            _ => None,
        }
    }

    fn make_loop(&self, block: ast::Block) -> ast::StmtBody {
        match *self {
            JmpKind::Uncond => ast::StmtBody::Loop { block, keyword: sp!(()) },

            JmpKind::Cond { keyword: sp_pat![token![unless]], .. } => unimplemented!(),  // not present in decompiled code
            JmpKind::Cond { keyword: sp_pat![kw_span => token![if]], ref cond } => ast::StmtBody::While {
                do_keyword: Some(sp!(kw_span => ())),
                while_keyword: sp!(kw_span => ()),
                cond: cond.clone(),
                block,
            },
        }
    }
}
