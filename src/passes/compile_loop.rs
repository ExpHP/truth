//! Loop compilation.
//!
//! This transforms `loop { ... }` syntax in STD to use a label and `goto`.
//!
//! It currently does this directly to the AST.  Which doesn't seem like a
//! viable strategy long-term, but we'll see where things go...

use crate::error::CompileError;
use crate::ast::{self, VisitMut};
use crate::pos::Sp;
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

    pub fn finish(self) -> Result<(), CompileError> { Ok(()) }
}

impl VisitMut for Visitor<'_> {
    fn visit_block(&mut self, outer_stmts: &mut ast::Block) {
        // traverse depth-first
        ast::walk_mut_block(self, outer_stmts);

        let mut new_stmts = Vec::with_capacity(outer_stmts.0.len());
        for outer_stmt in outer_stmts.0.drain(..) {
            match JmpKind::from_loop(outer_stmt) {
                Ok((mut inner_block, jmp_kind)) => {
                    let end_time = inner_block.end_time();
                    let label_ident = self.gensym_ctx.gensym("@loop#");
                    inner_block.0.push(sp!(ast::Stmt {
                        labels: vec![],
                        time: end_time,
                        body: sp!(jmp_kind.make_jump(ast::StmtGoto {
                            destination: sp!(label_ident.clone()),
                            time: None,
                        })),
                    }));
                    inner_block.0[0].labels.push(sp!(ast::StmtLabel::Label(sp!(label_ident))));

                    new_stmts.append(&mut inner_block.0);
                },
                Err(outer_stmt) => new_stmts.push(outer_stmt),
            }
        }

        outer_stmts.0 = new_stmts;
    }
}

enum JmpKind {
    Unconditional,
    Conditional(Sp<ast::Cond>),
}

impl JmpKind {
    fn from_loop(ast: Sp<ast::Stmt>) -> Result<(ast::Block, JmpKind), Sp<ast::Stmt>> {
        match ast.value.body.value {
            ast::StmtBody::Loop { block } => Ok((block, JmpKind::Unconditional)),

            ast::StmtBody::While { is_do_while: true, cond, block } => {
                Ok((block, JmpKind::Conditional(cond.clone())))
            }

            _ => Err(ast),
        }
    }

    fn make_jump(&self, jump: ast::StmtGoto) -> ast::StmtBody {
        match self {
            JmpKind::Unconditional => ast::StmtBody::Jump(jump),
            JmpKind::Conditional(cond) => ast::StmtBody::CondJump {
                keyword: sp!(ast::CondKeyword::If),
                cond: cond.clone(),
                jump,
            },
        }
    }
}
