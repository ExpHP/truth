//! Structured code desugaring.
//!
//! This desugars all block structures in the code, reducing everything into a single block.

use crate::error::CompileError;
use crate::ast::{self, VisitMut};
use crate::pos::{Sp, Span};
use crate::ident::{Ident};
use crate::type_system::{ScalarType, TypeSystem};

pub struct Visitor<'a> {
    ty_ctx: &'a mut TypeSystem,
}

impl<'a> Visitor<'a> {
    pub fn new(ty_ctx: &'a mut TypeSystem) -> Self {
        Visitor { ty_ctx }
    }

    pub fn finish(self) -> Result<(), CompileError> { Ok(()) }
}

impl VisitMut for Visitor<'_> {
    fn visit_block(&mut self, block: &mut ast::Block) {
        let mut desugarer = Desugarer { out: vec![], ty_ctx: self.ty_ctx };

        desugarer.desugar_block(std::mem::replace(block, ast::Block(vec![])));
        block.0 = desugarer.out;

        // for inner functions
        ast::walk_block_mut(self, block);
    }
}


struct Desugarer<'a> {
    out: Vec<Sp<ast::Stmt>>,
    ty_ctx: &'a mut TypeSystem,
}

impl<'a> Desugarer<'a> {
    pub fn desugar_block(&mut self, mut outer_block: ast::Block) {
        for outer_stmt in outer_block.0.drain(..) {
            let outer_time = outer_stmt.time;
            match outer_stmt.value.body {
                ast::StmtBody::Loop { block } => {
                    self.desugar_loop_body(block, None)
                },

                ast::StmtBody::While { is_do_while: true, cond, block } => {
                    let keyword = sp!(cond.span => token![if]);
                    self.desugar_loop_body(block, Some((keyword, cond.value)))
                },

                ast::StmtBody::While { is_do_while: false, cond, block } => {
                    let keyword = sp!(cond.span => token![if]);
                    self.desugar_conditional_region(cond.span, outer_time, keyword, cond.clone(), |self_| {
                        self_.desugar_loop_body(block, Some((keyword, cond.value)));
                    });
                },

                ast::StmtBody::Times { clobber, count, mut block } => {
                    let clobber = match clobber {
                        Some(var) => var,
                        None => {
                            let local_id = self.ty_ctx.variables.declare_temporary(Some(ScalarType::Int));
                            let var = sp!(count.span => ast::Var::Resolved { var_id: local_id.into(), ty_sigil: None });

                            block.0.push(sp!(block.end_span() => ast::Stmt {
                                time: block.end_time(),
                                body: ast::StmtBody::ScopeEnd(local_id),
                            }));
                            var
                        },
                    };

                    self.desugar_times(outer_time, clobber, count, block);
                },

                ast::StmtBody::CondChain(chain) => {
                    let veryend = self.ty_ctx.gensym.gensym("@cond_veryend#");

                    let mut prev_end_time = outer_time;
                    for cond_block in chain.cond_blocks {
                        let ast::CondBlock { keyword, cond, block } = cond_block.value;

                        let (end_span, end_time) = (block.end_span(), block.end_time());
                        self.desugar_conditional_region(cond.span, prev_end_time, sp!(cond.span => keyword), cond, |self_| {
                            self_.desugar_block(block);
                            self_.make_goto(end_span, end_time, None, veryend.clone());
                        });

                        prev_end_time = end_time;
                    }
                    if let Some(block) = chain.else_block {
                        self.desugar_block(block);
                    }

                    self.make_label_after_block(veryend);
                },

                _ => self.out.push(outer_stmt),
            }
        }
    }

    /// Desugar code that conditionally executes.
    ///
    /// ```text
    ///     unless (<cond>) goto skip;
    ///     <stuff written by callback>
    /// skip:
    /// ```
    fn desugar_conditional_region(
        &mut self,
        condjmp_span: Span,
        condjmp_time: i32,
        keyword: Sp<ast::CondKeyword>,
        cond: Sp<ast::Cond>,
        inner: impl FnOnce(&mut Self),
    ) {
        let skip_label = self.ty_ctx.gensym.gensym("@cond#");
        self.out.push(rec_sp!(condjmp_span =>
            stmt_cond_goto!(at #condjmp_time, #(keyword.negate()) #cond goto #(skip_label.clone()))
        ));

        inner(self);

        self.make_label_after_block(skip_label);
    }

    fn desugar_times(&mut self, init_time: i32, clobber: Sp<ast::Var>, count: Sp<ast::Expr>, block: ast::Block) {
        let span = count.span;
        let count_as_const = count.as_const_int();

        self.out.push(rec_sp!(span =>
            stmt_assign!(at #init_time, #(clobber.clone()) = #count)
        ));

        // unless count is statically known to be nonzero, we need an initial zero test
        let skip_label = self.ty_ctx.gensym.gensym("@times_zero#");
        if let None | Some(0) = count_as_const {
            self.out.push(rec_sp!(span =>
                stmt_cond_goto!(at #init_time, if expr_binop![#(clobber.clone()) == #(0)] goto #(skip_label.clone()))
            ));
        };

        let keyword = sp!(span => token![if]);
        let cond = ast::Cond::PreDecrement(clobber.clone());
        self.desugar_loop_body(block, Some((keyword, cond)));

        self.make_label_after_block(skip_label);
    }

    // desugars a `loop { .. }` or `do { ... } while (<cond>);`
    fn desugar_loop_body(&mut self, block: ast::Block, cond: JumpInfo) {
        let label = self.ty_ctx.gensym.gensym("@loop#");
        self.make_label(block.start_span(), block.start_time(), label.clone());
        self.desugar_block(block);
        self.make_goto_after_block(cond, label);
    }

    fn make_label(&mut self, span: Span, time: i32, ident: Ident) {
        self.out.push(rec_sp!(span => stmt_label!(at #time, #ident)));
    }

    fn make_goto(&mut self, span: Span, time: i32, cond: JumpInfo, ident: Ident) {
        self.out.push(match cond {
            None => rec_sp!(span => stmt_goto!(at #time, goto #ident)),
            Some((kw, cond))
                => rec_sp!(span => stmt_cond_goto!(at #time, #kw #cond goto #ident)),
        })
    }

    // Make a label after desugaring a block.
    // (this exists for convenience since the block will be destroyed and you can't call block.end_span())
    fn make_label_after_block(&mut self, ident: Ident) {
        let last_written_stmt = self.out.last().expect("no written statements?!");
        let (last_span, last_time) = (last_written_stmt.span.end_span(), last_written_stmt.time);

        self.make_label(last_span, last_time, ident);
    }

    // Make a goto after desugaring a block.
    // (this exists for convenience since the block will be destroyed and you can't call block.end_span())
    fn make_goto_after_block(&mut self, cond: JumpInfo, label: Ident) {
        let last_written_stmt = self.out.last().expect("no written statements?!");
        let (last_span, last_time) = (last_written_stmt.span.end_span(), last_written_stmt.time);

        self.make_goto(last_span, last_time, cond, label);
    }
}

// Distinguishes `if (...) goto` vs `unless (...) goto` vs unconditional `goto`.
type JumpInfo = Option<(Sp<ast::CondKeyword>, ast::Cond)>;
