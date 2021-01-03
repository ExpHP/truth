//! Loop compilation.
//!
//! This transforms `loop { ... }` syntax in STD to use a label and `goto`.
//!
//! It currently does this directly to the AST.  Which doesn't seem like a
//! viable strategy long-term, but we'll see where things go...

use crate::ast::{self, VisitMut};
use crate::ident;

/// Visitor for loop compilation.
///
/// See the [the module-level documentation][self] for more details.
pub struct Visitor<'a> {
    gensym_ctx: &'a ident::GensymContext,
}

impl<'a> Visitor<'a> {
    pub fn new(gensym_ctx: &'a ident::GensymContext) -> Self {
        Visitor { gensym_ctx }
    }
}

impl VisitMut for Visitor<'_> {
    fn visit_block(&mut self, outer_stmts: &mut ast::Block) {
        // traverse depth-first
        ast::walk_mut_block(self, outer_stmts);

        let mut new_stmts = Vec::with_capacity(outer_stmts.0.len());
        for outer_stmt in outer_stmts.0.drain(..) {
            match outer_stmt.value.body.value {
                ast::StmtBody::Loop { block: mut inner_block } => {
                    let end_time = inner_block.0.last().map(|s| s.time).unwrap_or(outer_stmt.value.time);
                    let label_ident = self.gensym_ctx.gensym("@loop#");
                    inner_block.0.push(sp!(ast::Stmt {
                        labels: vec![],
                        time: end_time,
                        body: sp!(ast::StmtBody::Jump(ast::StmtGoto {
                            destination: sp!(label_ident.clone()),
                            time: None,
                        }))
                    }));
                    inner_block.0[0].labels.push(sp!(ast::StmtLabel::Label(sp!(label_ident))));

                    new_stmts.append(&mut inner_block.0);
                },
                _ => new_stmts.push(outer_stmt),
            }
        }

        outer_stmts.0 = new_stmts;
    }
}
