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

        // Dumb strategy: We just greedily replace the first backwards jump we find.
        while let Some(last_stmt) = outer_stmts.0.last() {
            // Is this a goto?
            if let ast::StmtBody::Jump(goto) = &last_stmt.body.value {
                // Does it jump to a label in the same block?
                if let Some(&dest_index) = label_indices.get(&goto.destination.value) {

                    // Is the label before the jump, and does it jump to timeof(label)?
                    let src_index = outer_stmts.0.len() - 1;
                    let time_of_label = outer_stmts.0[dest_index].time;
                    let goto_time = goto.time.unwrap_or(time_of_label);
                    if dest_index <= src_index && goto_time == time_of_label {

                        // replace the goto with an EndOfBlock, preserving its time
                        let block_end = outer_stmts.0.last_mut().unwrap();
                        let block_end_span = block_end.span;
                        block_end.body.value = ast::StmtBody::EndOfBlock;

                        let inner_stmts: Vec<_> = outer_stmts.0.drain(dest_index..).collect();
                        let inner_span = inner_stmts[0].span.merge(block_end_span);

                        reversed_out.push(Sp {
                            span: inner_span,
                            value: ast::Stmt {
                                time: inner_stmts[0].time,
                                labels: vec![],
                                body: Sp {
                                    span: inner_span,
                                    value: ast::StmtBody::Loop { block: ast::Block(inner_stmts) },
                                },
                            },
                        });
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
