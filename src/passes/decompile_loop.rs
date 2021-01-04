//! Loop compilation.
//!
//! This identifies usage of `goto` that can be transformed into `loop { ... }` blocks.
//!
//! It currently does this directly to the AST.  Which doesn't seem like a
//! viable strategy long-term, but we'll see where things go...

use std::collections::HashMap;
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
}

impl VisitMut for Visitor {
    fn visit_block(&mut self, outer_stmts: &mut ast::Block) {
        let mut reversed_out = vec![];

        let label_indices = get_label_indices(&outer_stmts.0);
        let interrupt_label_indices = get_interrupt_label_indices(&outer_stmts.0);

        // Dumb strategy: We just greedily replace the first backwards jump we find.
        while let Some(last_stmt) = outer_stmts.0.last() {
            // Is this a goto?
            if let Some((goto, jmp_kind)) = JmpKind::from_jump(&last_stmt.body.value) {
                // Does it jump to a label in the same block?
                if let Some(&dest_index) = label_indices.get(&goto.destination.value) {

                    // Is the label before the jump, and does it jump to timeof(label)?
                    let src_index = outer_stmts.0.len() - 1;
                    let can_transform = {
                        if dest_index <= src_index {
                            let time_of_label = outer_stmts.0[dest_index].time;
                            let goto_time = goto.time.unwrap_or(time_of_label);
                            goto_time == time_of_label
                        } else { false }
                    };

                    // Don't let a loop contain an interrupt label because it's confusing to read.
                    let is_confusing = || {
                        interrupt_label_indices.iter().any(|&interrupt_i| {
                            dest_index <= interrupt_i && interrupt_i < src_index
                        })
                    };

                    if can_transform && !is_confusing() {
                        // replace the goto with an EndOfBlock, preserving its time
                        let block_end = outer_stmts.0.last_mut().unwrap();
                        let block_end_span = block_end.span;
                        block_end.body.value = ast::StmtBody::NoInstruction;

                        let inner_stmts: Vec<_> = outer_stmts.0.drain(dest_index..).collect();
                        let inner_span = inner_stmts[0].span.merge(block_end_span);

                        reversed_out.push(sp!(inner_span => ast::Stmt {
                            time: inner_stmts[0].time,
                            labels: vec![],
                            body: sp!(inner_span => jmp_kind.make_loop(ast::Block(inner_stmts))),
                        }));
                        // suppress the default behavior of popping the next item
                        continue;
                    }
                }
            }
            // doesn't match what we're looking for
            reversed_out.push(outer_stmts.0.pop().unwrap());
        }
        // put them in the right order
        reversed_out.reverse();
        outer_stmts.0 = reversed_out;

        ast::walk_mut_block(self, outer_stmts);
    }
}

enum JmpKind {
    Unconditional,
    Conditional(Sp<ast::Cond>),
}

impl JmpKind {
    fn from_jump(ast: &ast::StmtBody) -> Option<(&ast::StmtGoto, JmpKind)> {
        match ast {
            ast::StmtBody::Jump(goto) => Some((goto, JmpKind::Unconditional)),

            ast::StmtBody::CondJump { keyword, cond, jump } => match keyword.value {
                ast::CondKeyword::If => Some((jump, JmpKind::Conditional(cond.clone()))),
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

/// For each label, get the index of its instruction.
fn get_label_indices(stmts: &[Sp<ast::Stmt>]) -> HashMap<Ident, usize> {
    stmts.iter().enumerate()
        .flat_map(|(index, stmt)| stmt.labels.iter().filter_map(move |label| match &label.value {
            ast::StmtLabel::Label(ident) => Some((ident.value.clone(), index)),
            ast::StmtLabel::Difficulty { .. } => None,
        })).collect()
}

/// Get a list of instruction indices that are interrupt labels.
fn get_interrupt_label_indices(stmts: &[Sp<ast::Stmt>]) -> Vec<usize> {
    stmts.iter().enumerate()
        .filter_map(|(index, stmt)| match stmt.body.value {
            ast::StmtBody::InterruptLabel { .. } => Some(index),
            _ => None,
        }).collect()
}
