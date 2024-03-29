//! Control flow decompilation.
//!
//! Recognizes various control flow structures in decompiled code and uses them to make
//! the output more expressive.

use std::collections::{BTreeMap, HashMap};
use crate::error::ErrorReported;
use crate::ast::{self, VisitMut, Visit};
use crate::ident::Ident;
use crate::pos::Sp;
use crate::context::CompilerContext;
use crate::resolve::LoopId;
use crate::passes::resolution::LexicalLoopTracker;
use crate::passes::unused_labels::get_label_refcounts;

/// Decompiles `if { ... } else if { ... } else { ... }` chains.
pub fn decompile_if_else<V: ast::Visitable>(ast: &mut V, ctx: &mut CompilerContext<'_>) -> Result<(), ErrorReported> {
    let mut visitor = IfElseVisitor { label_refcounts_stack: vec![], ctx };
    ast.visit_mut_with(&mut visitor);
    Ok(())
}

/// Decompiles `loop { ... }` and `do { ... } while (<cond>)`.
pub fn decompile_loop<V: ast::Visitable>(ast: &mut V, ctx: &mut CompilerContext<'_>) -> Result<(), ErrorReported> {
    let mut visitor = LoopVisitor { label_refcounts_stack: vec![], ctx };
    ast.visit_mut_with(&mut visitor);
    Ok(())
}

/// Decompiles `break`s inside of existing loops.
pub fn decompile_break<V: ast::Visitable>(ast: &mut V, _ctx: &mut CompilerContext<'_>) -> Result<(), ErrorReported> {
    let mut visitor = MakeBreakVisitor { loop_tracker: LexicalLoopTracker::new(), loop_ids_by_end_label: vec![] };
    ast.visit_mut_with(&mut visitor);
    Ok(())
}

// =============================================================================
// if-else decompilation

struct IfElseVisitor<'a, 'ctx> {
    // whole-function-body label refcounts at the beginning of the procedure
    label_refcounts_stack: Vec<HashMap<Ident, u32>>,
    ctx: &'a mut CompilerContext<'ctx>,
}

impl VisitMut for IfElseVisitor<'_, '_> {
    fn visit_root_block(&mut self, block: &mut ast::Block) {
        self.label_refcounts_stack.push(get_label_refcounts(&block.0));
        self.visit_block(block);
        self.label_refcounts_stack.pop();
    }

    fn visit_block(&mut self, outer_block: &mut ast::Block) {
        let mut new_stmts = Vec::with_capacity(outer_block.0.len());

        let context = BlockContext::from_block(outer_block, self.label_refcounts_stack.last().expect("must use on a function body!"));

        let original_len = outer_block.0.len();

        let mut index = 0;
        let mut stmt_iter = outer_block.0.drain(..);
        while index < original_len {
            match gather_cond_chain(index, &context) {
                Err(NoCondChain) => {
                    new_stmts.push(stmt_iter.next().unwrap()); index += 1;
                },

                Ok(CondChainInfo { chain, else_start_index, end_label_index }) => {
                    let make_bookend = || ast::Stmt {
                        node_id: Some(self.ctx.next_node_id()),
                        diff_label: None,
                        kind: ast::StmtKind::NoInstruction,
                    };

                    let mut cond_block_asts = vec![];
                    for cond_block in chain {
                        // read all of the statements from the jump (inclusive) to the label (exclusive).
                        assert_eq!(index, cond_block.if_index);

                        let inner_block_len = cond_block.label_index - cond_block.if_index;
                        let mut inner_block = ast::Block(stmt_iter.by_ref().take(inner_block_len).collect());
                        index += inner_block_len;

                        let cond_block_span = inner_block.start_span().merge(inner_block.end_span());

                        // eliminate unconditional jumps to end
                        if cond_block.label_index != end_label_index {
                            let removed = inner_block.0.pop().unwrap();
                            assert!(matches!(removed.kind, ast::StmtKind::Jump { .. }));
                        }

                        // After the block body comes the conditional jump target label.  Handle this carefully!
                        let label_stmt = stmt_iter.next().unwrap();
                        index += 1;
                        assert!(matches!(label_stmt.kind, ast::StmtKind::Label { .. }));
                        if cond_block.label_index == end_label_index {
                            // This label is the end label.  This happens when there is no final `else`.
                            // We want to keep this label because other things may also use it.
                            //
                            // Because we decompile things from the outside-inwards, we get better
                            // results for nested if/elses if we put this label INSIDE the final block.
                            inner_block.0.push(label_stmt);
                        } else {
                            // There is another block after this one. (else or else if)
                            //
                            // For `else if` there is nowhere valid to put this label, but we already
                            // checked its refcount earlier so it is safe to just ignore it.
                            drop(label_stmt);
                        }

                        // surround with bookends;
                        // we can replace the conditional jump at the start
                        assert!(matches!(inner_block.0[0].kind, ast::StmtKind::CondJump { .. }));
                        inner_block.0[0] = sp!(cond_block_span.start_span() => make_bookend());
                        inner_block.0.push(sp!(cond_block_span.end_span() => make_bookend()));

                        cond_block_asts.push(ast::CondBlock {
                            keyword: cond_block.keyword,
                            cond: cond_block.cond,
                            block: inner_block,
                        });
                    }

                    let else_block;

                    if let Some(else_start_index) = else_start_index {
                        assert_eq!(index, else_start_index);
                        let inner_block_len = end_label_index - else_start_index;
                        let mut inner_block = ast::Block(stmt_iter.by_ref().take(inner_block_len).collect());
                        assert_eq!(inner_block.0.len(), inner_block_len);
                        index += inner_block_len;

                        // as above, better results for putting the final label INSIDE the else instead of after
                        let label_stmt = stmt_iter.next().unwrap();
                        assert!(matches!(label_stmt.kind, ast::StmtKind::Label { .. }));
                        inner_block.0.push(label_stmt);
                        index += 1;

                        // add bookends
                        inner_block.0.insert(0, sp!(inner_block.start_span() => make_bookend()));
                        inner_block.0.push(sp!(inner_block.end_span() => make_bookend()));

                        else_block = Some(inner_block);
                    } else {
                        else_block = None;
                    }
                    // The final label should be inside the last block, so we should be after it now.
                    assert_eq!(index, end_label_index + 1);

                    let cond_chain = ast::StmtCondChain { cond_blocks: cond_block_asts, else_block };
                    let span = cond_chain.cond_blocks[0].block.0[0].span.merge(cond_chain.last_block().end_span());
                    new_stmts.push(sp!(span => ast::Stmt {
                        node_id: Some(self.ctx.next_node_id()),
                        diff_label: None,
                        kind: ast::StmtKind::CondChain(cond_chain),
                    }));
                },
            }
        }
        drop(stmt_iter);

        outer_block.0 = new_stmts;

        ast::walk_block_mut(self, outer_block);
    }
}

#[derive(Debug, Clone)]
struct CondChainInfo {
    chain: Vec<CondBlockInfo>,
    else_start_index: Option<usize>,  // body of else after label
    end_label_index: usize,
}
#[derive(Debug, Clone)]
struct CondBlockInfo {
    keyword: Sp<ast::CondKeyword>,
    cond: Sp<ast::Expr>,
    if_index: usize,
    // Target label of the conditional jump.
    // NOTE: any block where label_index != end_label_index will have an unconditional jump
    //       to the end label as its final statement
    label_index: usize,
}

struct NoCondChain;

fn gather_cond_chain(start: usize, context: &BlockContext) -> Result<CondChainInfo, NoCondChain> {
    let cond_chain = _gather_cond_chain(start, context)?;
    reject_potentially_confusing_cond_chain(&cond_chain, context)?;
    Ok(cond_chain)
}

fn _gather_cond_chain(start: usize, context: &BlockContext) -> Result<CondChainInfo, NoCondChain> {
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

        // Now we find out what's coming up; an `else if`, an `else`, nothing?
        // right before each conditional target label there will be an unconditional
        // jump to the end of the entire construction.
        //
        // (except for the final block, when there is no `else`.)
        let uncond_src = if_jmp.dest - 1;
        let uncond_jmp = match context.jmp_info.get(&uncond_src) {
            // Note: The if guard is checking for a silly edge case where there's an empty if
            //       not followed by an else.  In this case the original conditional jump is at
            //       the index we're checking now, and we want to take the "no else" branch instead.
            Some(jmp) if src != uncond_src => jmp,

            _ => {
                // This is a chain with no `else`.
                //
                // If there has been at least one `else if` so far, we already know the
                // end label.  Validate that the conditional jump goes directly there.
                if let Some(expected_end) = known_end {
                    if if_jmp.dest != expected_end {
                        return Err(NoCondChain);
                    }
                }
                return Ok(CondChainInfo {
                    chain,
                    else_start_index: None,
                    end_label_index: if_jmp.dest,
                });
            },
        };
        // There is an unconditional jump, so SOMETHING is coming up (either an `else` or `else if`)

        // make sure there's only one reference to the dest label,
        // because for 'else if' there will be no place for us to put it
        if if_jmp.dest_refcount > 1 {
            return Err(NoCondChain);
        }

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

        // is there another 'if' or was that it?
        src = if_jmp.dest + 1;
        if !matches!(context.jmp_info.get(&src), Some(JmpInfo { kind: JmpKind::Cond { .. }, .. })) {
            break;  // the next thing is an `else`
        }
    }

    // now we find ourselves at an 'else' block.
    let else_start_index = src;
    let end_label_index = known_end.expect("we found at least one block so this was set");
    if end_label_index < else_start_index {
        return Err(NoCondChain);
    }

    Ok(CondChainInfo { chain, else_start_index: Some(else_start_index), end_label_index })
}

fn reject_potentially_confusing_cond_chain(cond_chain: &CondChainInfo, context: &BlockContext) -> Result<(), NoCondChain> {
    // don't decompile if there's an interrupt label anywhere in the chain
    let stmt_range = cond_chain.chain[0].if_index..cond_chain.end_label_index;
    if context.interrupt_label_indices.iter().any(|&i| stmt_range.contains(&i)) {
        return Err(NoCondChain);
    }
    Ok(())
}

// =============================================================================

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

#[derive(Debug)]
struct LabelInfo {
    stmt_index: usize,
    refcount: u32,  // number of jumps to this label
}

/// For each label, get the index of its statement.
fn get_label_info(stmts: &[Sp<ast::Stmt>], refcounts: &HashMap<Ident, u32>) -> HashMap<Ident, LabelInfo> {
    stmts.iter().enumerate()
        .filter_map(|(stmt_index, stmt)| match &stmt.kind {
            ast::StmtKind::Label(ident) => {
                let refcount = refcounts.get(&ident.value).copied().unwrap_or(0);
                Some((ident.value.clone(), LabelInfo { stmt_index, refcount }))
            },
            _ => None,
        }).collect()
}

/// Get a list of statement indices that are interrupt labels.
fn get_interrupt_label_indices(stmts: &[Sp<ast::Stmt>]) -> Vec<usize> {
    stmts.iter().enumerate()
        .filter_map(|(index, stmt)| match stmt.kind {
            ast::StmtKind::InterruptLabel { .. } => Some(index),
            _ => None,
        }).collect()
}

// =============================================================================

struct LoopVisitor<'a, 'ctx> {
    // whole-function-body label refcounts at the beginning of the procedure
    label_refcounts_stack: Vec<HashMap<Ident, u32>>,
    ctx: &'a mut CompilerContext<'ctx>,
}

impl VisitMut for LoopVisitor<'_, '_> {
    fn visit_root_block(&mut self, block: &mut ast::Block) {
        self.label_refcounts_stack.push(get_label_refcounts(&block.0));
        self.visit_block(block);
        self.label_refcounts_stack.pop();
    }

    fn visit_block(&mut self, outer_block: &mut ast::Block) {
        ast::walk_block_mut(self, outer_block);  // do inner blocks

        let label_info = get_label_info(&outer_block.0, self.label_refcounts_stack.last().expect("must use on a function body!"));
        let interrupt_label_indices = get_interrupt_label_indices(&outer_block.0);

        // We get best results for nested loops and mixed if/else/loop structures if we decompile
        // innermost loops before outer loops.  However, decompiling things in this order will
        // invalidate our indices, so we track the original index of each statement.
        let mut out_stmts = vec![];
        let mut out_indices = vec![];

        // Read statements in forward order.
        // An iterator is used to avoid O(n^2) cost of repeated removals from the middle of a vector.
        for (scan_index, scan_stmt) in outer_block.0.drain(..).enumerate() {
            // Perform the "fallback" behavior now of simply adding the statement to the output,
            // so that we can simply 'continue' or do nothing if we don't want to decompile a loop.
            out_indices.push(scan_index);
            out_stmts.push(scan_stmt);
            assert_eq!(out_indices.len(), out_stmts.len());

            match JmpInfo::from_stmt(&out_stmts.last().expect("we just pushed it!"), &label_info) {
                None => continue,  // not a jump
                Some(jmp) => match should_decompile_loop(&interrupt_label_indices, &out_indices, scan_index, &jmp) {
                    ShouldDecompileLoop::No => continue,  // the stars have not aligned
                    ShouldDecompileLoop::Yes { label_pos_in_current_output } => {
                        // consolidate everything after the label into a loop
                        let trim_from = label_pos_in_current_output + 1;

                        let mut new_block = ast::Block(out_stmts.drain(trim_from..).collect());

                        // (the loop jump guarantees we have at least one statement so this won't panic)
                        let inner_span = new_block.start_span().merge(new_block.end_span());

                        // Don't need the jump anymore.
                        new_block.0.pop().unwrap();

                        // Construct the loop statement.
                        out_stmts.push(sp!(inner_span => ast::Stmt {
                            node_id: Some(self.ctx.next_node_id()),
                            diff_label: None,
                            kind: jmp.kind.make_loop(new_block, self.ctx.next_loop_id()),
                        }));

                        // Give it the index of the jump since that uniquely represents it.
                        out_indices.truncate(trim_from);
                        out_indices.push(scan_index);
                    },
                },
            };
        }

        outer_block.0 = out_stmts;
    }
}

enum ShouldDecompileLoop {
    No,
    Yes { label_pos_in_current_output: usize },
}

fn should_decompile_loop(
    interrupt_label_indices: &[usize],
    // for each statement in the current loop decompilation output, its original index
    out_stmt_indices: &[usize],
    jmp_src_index: usize,
    jmp: &JmpInfo,
) -> ShouldDecompileLoop {
    if jmp.time_arg.is_some() {
        return ShouldDecompileLoop::No;
    }

    // is it backwards?
    if jmp.direction_given_src(jmp_src_index) != Direction::Backwards {
        return ShouldDecompileLoop::No;
    }
    // does the destination label still exist at this nesting level?
    let label_pos_in_current_output = match out_stmt_indices.binary_search(&jmp.dest) {
        Ok(pos) => pos,
        Err(_) => {
            // The destination label was already moved into the body of another loop.
            // This happens when multiple backwards jumps overlap.
            return ShouldDecompileLoop::No;
        },
    };

    // don't let a loop contain an interrupt label because it's confusing to read.
    if interrupt_label_indices.iter().any(|&interrupt_i| {
        jmp.dest <= interrupt_i && interrupt_i < jmp_src_index
    }) {
        return ShouldDecompileLoop::No;
    }

    ShouldDecompileLoop::Yes { label_pos_in_current_output }
}

// =============================================================================
// Visitor for generating break/continue

struct MakeBreakVisitor {
    loop_tracker: LexicalLoopTracker,
    loop_ids_by_end_label: Vec<HashMap<Ident, LoopId>>,  // stack is for nested functions
}

impl VisitMut for MakeBreakVisitor {
    fn visit_root_block(&mut self, block: &mut ast::Block) {
        self.loop_tracker.enter_function();
        self.loop_ids_by_end_label.push(gather_loop_end_labels(block));
        self.visit_block(block);
        self.loop_ids_by_end_label.pop().expect("unbalanced stack usage!");
        self.loop_tracker.exit_function();
    }

    fn visit_loop_begin(&mut self, loop_id: &mut Option<LoopId>) {
        self.loop_tracker.enter_loop(loop_id.expect("loop has no loop id"));
    }

    fn visit_loop_end(&mut self, loop_id: &mut Option<LoopId>) {
        assert_eq!(self.loop_tracker.exit_loop(), loop_id.expect("loop has no loop id"));
    }

    fn visit_jump(&mut self, jump: &mut ast::StmtJumpKind) {
        // are we in a loop right now?
        if let Some(cur_loop_id) = self.loop_tracker.current_loop() {

            // does this jump go to the end of a loop?
            if let ast::StmtJumpKind::Goto(ast::StmtGoto { destination, time: None }) = jump {
                let loop_ids_by_end_label = self.loop_ids_by_end_label.last().expect("not in function?!");
                if let Some(&jump_end_loop_id) = loop_ids_by_end_label.get(&destination.value) {

                    // Fantastic! ...are they the same loop?
                    if cur_loop_id == jump_end_loop_id {
                        // convert to 'break'
                        *jump = ast::StmtJumpKind::BreakContinue {
                            keyword: sp!(token!(break)),
                            loop_id: Some(cur_loop_id),
                        };
                    }
                }
            }
        }
    }
}

/// Find all labels that could be the destination of a `break`.
fn gather_loop_end_labels(root_block: &ast::Block) -> HashMap<Ident, LoopId> {
    struct Visitor {
        end_label_loop_ids: HashMap<Ident, LoopId>,
    }

    impl Visit for Visitor {
        fn visit_root_block(&mut self, _: &ast::Block) {}  // ignore inner functions

        fn visit_block(&mut self, block: &ast::Block) {
            // look for loops
            for loop_stmt_index in 0..block.0.len() {
                if let Some(loop_id) = ast::Stmt::get_loop_id(&block.0[loop_stmt_index]) {
                    // gather all labels that appear immediately after the loop
                    for stmt in &block.0[loop_stmt_index + 1..] {
                        if let ast::Stmt { kind: ast::StmtKind::Label(label), .. } = &stmt.value {
                            self.end_label_loop_ids.insert(label.value.clone(), loop_id);
                        } else {
                            break;
                        }
                    }
                }
            }
            ast::walk_block(self, block);  // look for more inside nested blocks
        }
    }

    let mut visitor = Visitor { end_label_loop_ids: Default::default() };
    visitor.visit_block(root_block);
    visitor.end_label_loop_ids
}

// =============================================================================

// Information about a jump from one statement in a block to another in the same block.
#[derive(Debug)]
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
        if ast.diff_label.is_some() {
            return None;  // we don't want to decompile any control flow where the jumps have difficulty labels
        }

        let (jump, kind) = match ast.kind {
            ast::StmtKind::Jump(ref goto) => (goto, JmpKind::Uncond),

            ast::StmtKind::CondJump { keyword, ref cond, ref jump } => match keyword.value {
                ast::CondKeyword::If => (jump, JmpKind::Cond { keyword, cond: cond.clone() }),
                ast::CondKeyword::Unless => unimplemented!(),  // not present in decompiled code
            }

            _ => return None,
        };

        let goto = match jump {
            ast::StmtJumpKind::Goto(goto) => goto,
            ast::StmtJumpKind::BreakContinue { .. } => unimplemented!(), // not present at this stage of decompilation
        };

        let label_entry = &label_info.get(&goto.destination.value)?;
        Some(JmpInfo {
            dest: label_entry.stmt_index,
            dest_refcount: label_entry.refcount,
            time_arg: goto.time,
            kind
        })
    }

    /// Direction of jump, given the index of the statement containing this jump.
    fn direction_given_src(&self, src: usize) -> Direction {
        if src < self.dest { Direction::Forwards }
        else { Direction::Backwards }
    }
}

#[derive(Debug)]
enum JmpKind {
    Uncond,
    Cond { keyword: Sp<ast::CondKeyword>, cond: Sp<ast::Expr> },
}

type ExprBinOpRef<'a> = (&'a Sp<ast::Expr>, Sp<ast::BinOpKind>, &'a Sp<ast::Expr>);

impl JmpKind {
    fn as_binop_cond(&self) -> Option<(Sp<ast::CondKeyword>, Sp<ExprBinOpRef<'_>>)> {
        match *self {
            JmpKind::Cond { keyword, cond: sp_pat!(span => ast::Expr::BinOp(ref a, op, ref b)) }
                => Some((keyword, sp!(span => (a, op, b)))),

            _ => None,
        }
    }

    fn make_loop(&self, block: ast::Block, loop_id: LoopId) -> ast::StmtKind {
        match *self {
            JmpKind::Uncond => ast::StmtKind::Loop { loop_id: Some(loop_id), block, keyword: sp!(()) },

            JmpKind::Cond { keyword: sp_pat![token![unless]], .. } => unimplemented!(),  // not present in decompiled code
            JmpKind::Cond { keyword: sp_pat![kw_span => token![if]], ref cond } => ast::StmtKind::While {
                loop_id: Some(loop_id),
                do_keyword: Some(sp!(kw_span => ())),
                while_keyword: sp!(kw_span => ()),
                cond: cond.clone(),
                block,
            },
        }
    }
}
