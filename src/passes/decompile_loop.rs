//! Loop compilation.
//!
//! This identifies usage of `goto` that can be transformed into `loop { ... }` blocks.
//!
//! It currently does this directly to the AST.  Which doesn't seem like a
//! viable strategy long-term, but we'll see where things go...

use std::collections::HashMap;
use crate::error::SimpleError;
use crate::ast::{self, VisitMut};
use crate::ident::Ident;
use crate::pos::Sp;

/// Visitor for loop compilation.
///
/// See the [the module-level documentation][self] for more details.
pub struct Visitor {
    _priv: ()
}

impl Visitor {
    pub fn new() -> Self {
        Visitor { _priv: () }
    }

    pub fn finish(self) -> Result<(), SimpleError> { Ok(()) }
}

impl VisitMut for Visitor {
    fn visit_block(&mut self, outer_stmts: &mut ast::Block) {
        let mut reversed_out = vec![];

        let label_indices = get_label_indices(&outer_stmts.0);
        let interrupt_label_indices = get_interrupt_label_indices(&outer_stmts.0);

        // Dumb strategy: We just greedily replace the first backwards jump we find.
        while let Some(last_stmt) = outer_stmts.0.last() {
            match JmpKind::from_jump(&last_stmt.body) {
                Some((goto, jmp_kind)) => {
                    let did_decompile = maybe_decompile_jump(outer_stmts, &mut reversed_out, &label_indices, &interrupt_label_indices, &goto, jmp_kind);
                    if did_decompile { continue; }
                },
                None => {},
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


enum JmpKind {
    Unconditional,
    Conditional(Sp<ast::Cond>),
}

impl JmpKind {
    fn from_jump(ast: &ast::StmtBody) -> Option<(ast::StmtGoto, JmpKind)> {
        match ast {
            ast::StmtBody::Jump(goto) => Some((goto.clone(), JmpKind::Unconditional)),

            ast::StmtBody::CondJump { keyword, cond, jump } => match keyword.value {
                ast::CondKeyword::If => Some((jump.clone(), JmpKind::Conditional(cond.clone()))),
                ast::CondKeyword::Unless => unimplemented!(),  // you won't see 'unless' in decompiled code
            }

            _ => None,
        }
    }

    fn make_loop(&self, block: ast::Block) -> ast::StmtBody {
        match self {
            JmpKind::Unconditional => ast::StmtBody::Loop { block },
            JmpKind::Conditional(cond) => ast::StmtBody::While {
                is_do_while: true,
                cond: cond.clone(),
                block,
            },
        }
    }
}

/// For each label, get the index of its statement.
fn get_label_indices(stmts: &[Sp<ast::Stmt>]) -> HashMap<Ident, usize> {
    stmts.iter().enumerate()
        .filter_map(|(index, stmt)| match &stmt.body {
            ast::StmtBody::Label(ident) => Some((ident.value.clone(), index)),
            _ => None,
        }).collect()
}

/// Get a list of statment indices that are interrupt labels.
fn get_interrupt_label_indices(stmts: &[Sp<ast::Stmt>]) -> Vec<usize> {
    stmts.iter().enumerate()
        .filter_map(|(index, stmt)| match stmt.body {
            ast::StmtBody::InterruptLabel { .. } => Some(index),
            _ => None,
        }).collect()
}

fn maybe_decompile_jump(
    outer_stmts: &mut ast::Block,
    reversed_out: &mut Vec<Sp<ast::Stmt>>,
    label_indices: &HashMap<Ident, usize>,
    interrupt_label_indices: &[usize],
    goto: &ast::StmtGoto,
    jmp_kind: JmpKind,
) -> bool {
    // Does it jump to a label in the same block?
    let dest_index = match label_indices.get(&goto.destination.value) {
        Some(&index) => index,
        None => return false,
    };

    // Is the label before the jump?
    let src_index = outer_stmts.0.len() - 1;
    if src_index < dest_index {
        return false;
    }

    // Does it jump to timeof(label) or lower?
    let time_of_label = outer_stmts.0[dest_index].time;
    let goto_time = goto.time.unwrap_or(time_of_label);
    if time_of_label < goto_time {
        return false;
    }

    // Don't let a loop contain an interrupt label because it's confusing to read.
    if interrupt_label_indices.iter().any(|&interrupt_i| {
        dest_index <= interrupt_i && interrupt_i < src_index
    }) {
        return false;
    }

    // replace the goto with an EndOfBlock, preserving its time
    let block_end = outer_stmts.0.last_mut().unwrap();
    let block_end_span = block_end.span;
    block_end.body = ast::StmtBody::NoInstruction;

    let mut inner_stmts: Vec<_> = outer_stmts.0.drain(dest_index..).collect();
    let inner_span = inner_stmts[0].span.merge(block_end_span);

    if goto_time < time_of_label {
        // loop body begins with a `+n:` time label.
        // Insert a bookend just to be safe.
        inner_stmts.insert(0, sp!(inner_span.start_span() => ast::Stmt {
            time: goto_time,
            body: ast::StmtBody::NoInstruction,
        }));
    }

    reversed_out.push(sp!(inner_span => ast::Stmt {
        time: goto_time,
        body: jmp_kind.make_loop(ast::Block(inner_stmts)),
    }));
    // suppress the default behavior of popping the next item
    true
}
