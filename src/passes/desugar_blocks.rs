//! See [`run`].

use crate::error::ErrorReported;
use crate::ast::{self, Visit, VisitMut};
use crate::pos::{Sp, Span};
use crate::ident::Ident;
use crate::resolve::{DefId, NodeId, LoopId, Resolutions, UnusedIds};
use crate::value::ScalarType;
use crate::context::CompilerContext;
use crate::passes::semantics::time_and_difficulty::DEFAULT_DIFFICULTY_MASK;

/// Structured code desugaring.
///
/// This desugars all block structures in the code (conditional blocks, loops), reducing everything
/// into a single block.
///
/// This pass is not idempotent, because it inserts [`ast::StmtKind::ScopeEnd`] statements.
pub fn run<V: ast::Visitable + core::fmt::Debug>(ast: &mut V, ctx: &mut CompilerContext<'_>) -> Result<(), ErrorReported> {
    insert_scope_ends(ast, ctx)?;
    convert_continue_and_break(ast, ctx)?;

    let mut visitor = Visitor { ctx };
    ast.visit_mut_with(&mut visitor);

    // FIXME: currently needed because the macros leave out a bunch of NodeIds, but once we get rid of
    //        Stmt.time we might not need those macros
    crate::passes::resolution::fill_missing_node_ids(ast, &ctx.unused_node_ids)?;

    Ok(())
}

fn insert_scope_ends<A: ast::Visitable>(ast: &mut A, ctx: &mut CompilerContext<'_>) -> Result<(), ErrorReported> {
    let mut v = InsertLocalScopeEndsVisitor { resolutions: &ctx.resolutions, stack: vec![], unused_node_ids: &ctx.unused_node_ids };
    ast.visit_mut_with(&mut v);
    Ok(())
}

fn convert_continue_and_break<A: ast::Visitable>(ast: &mut A, ctx: &mut CompilerContext<'_>) -> Result<(), ErrorReported> {
    let mut v = BreakContinueToGotoVisitor { unused_node_ids: &ctx.unused_node_ids };
    ast.visit_mut_with(&mut v);
    Ok(())
}

// =============================================================================

/// Inserts [`ast::StmtKind::ScopeEnd`] statements for locals declared in each block.  These allow the
/// compiler to continue to take advantage of lexical scope information (to e.g. free registers) even
/// after block desugaring.
struct InsertLocalScopeEndsVisitor<'a> {
    resolutions: &'a Resolutions,
    unused_node_ids: &'a UnusedIds<NodeId>,
    stack: Vec<BlockState>,
}

pub struct BlockState {
    /// List of local variables whose scope end at the end of this block.
    locals_declared_at_this_level: Vec<DefId>,
}

impl VisitMut for InsertLocalScopeEndsVisitor<'_> {
    fn visit_block(&mut self, x: &mut ast::Block) {
        self.stack.push(BlockState {
            locals_declared_at_this_level: vec![],
        });

        ast::walk_block_mut(self, x);

        let popped = self.stack.pop().expect("(BUG!) unbalanced scope_stack usage!");

        // emit statements that will free resources during lowering
        for def_id in popped.locals_declared_at_this_level {
            let span = x.last_stmt().span.end_span();
            x.0.push(sp!(span => ast::Stmt {
                node_id: Some(self.unused_node_ids.next()),
                diff_label: None,
                kind: ast::StmtKind::ScopeEnd(def_id),
            }));
        }
    }

    fn visit_stmt(&mut self, x: &mut Sp<ast::Stmt>) {
        match &x.kind {
            ast::StmtKind::Declaration { ty_keyword: _, vars } => {
                for pair in vars {
                    let (var, _) = &pair.value;
                    if let ast::VarName::Normal { ident, .. } = &var.value.name {
                        let def_id = self.resolutions.expect_def(ident);
                        self.stack.last_mut().expect("(bug?) empty stack?")
                            .locals_declared_at_this_level.push(def_id);

                    } else {
                        unreachable!("impossible var name in declaration {:?}", var.value.name);
                    }
                }
            },
            _ => ast::walk_stmt_mut(self, x),
        }
    }
}

// =============================================================================

struct BreakContinueToGotoVisitor<'a> {
    unused_node_ids: &'a UnusedIds<NodeId>,
}

impl BreakContinueToGotoVisitor<'_> {
    // this process is simple: since all loops already have unique IDs, we just use those to generate label names
    fn loop_end_label_name(&self, loop_id: LoopId) -> Ident {
        format!("@loop_end#{}", loop_id).parse::<Ident>().unwrap()
    }
}

impl VisitMut for BreakContinueToGotoVisitor<'_> {
    fn visit_jump(&mut self, jump: &mut ast::StmtJumpKind) {
        // replace 'continue' with a 'goto'
        if let ast::StmtJumpKind::BreakContinue { keyword: sp_pat![kw_span => token![break]], loop_id } = *jump {
            let loop_id = loop_id.expect("missing loop ID");
            *jump = ast::StmtJumpKind::Goto(ast::StmtGoto {
                destination: sp!(kw_span => self.loop_end_label_name(loop_id)),
                time: None,
            });
        }
    }

    fn visit_block(&mut self, block: &mut ast::Block) {
        // Identify all loops in this block.
        let loop_id_indices = {
            block.0.iter().enumerate()
                .filter_map(|(index, stmt)| ast::Stmt::get_loop_id(stmt).map(|loop_id| (index, loop_id)))
                .rev()  // back to front for safe insertion order
                .collect::<Vec<_>>()  // stop borrowing the block
        };

        // Insert a label after every loop.
        for (loop_stmt_index, loop_id) in loop_id_indices {
            let insertion_index = loop_stmt_index + 1;
            let loop_end_span = block.0[loop_stmt_index].span.end_span();
            block.0.insert(insertion_index, sp!(loop_end_span => ast::Stmt {
                node_id: Some(self.unused_node_ids.next()),
                diff_label: None,
                kind: ast::StmtKind::Label(sp!(loop_end_span => self.loop_end_label_name(loop_id))),
            }));
        }

        ast::walk_block_mut(self, block);  // recurse
    }
}

impl ast::Stmt {
    pub fn get_loop_id(stmt: &Sp<ast::Stmt>) -> Option<LoopId> {
        // An obscenely silly visitor that uses the visitor API to determine if a statement is a loop.
        // (so that we don't need to repeat the matching logic for all the different loop types...)
        struct GetStmtLoopIdVisitor {
            loop_id: Option<LoopId>,
            used: bool,
        }

        impl Visit for GetStmtLoopIdVisitor {
            fn visit_stmt(&mut self, stmt: &Sp<ast::Stmt>) {
                // make sure we haven't recursed into anything; don't want to accidentally read
                // a loop id from a child statement.
                assert!(!self.used, "(bug!) StmtIsALoopVisitor looked at more than one statement!");
                self.used = true;

                // this will call visit_loop_end if and only if the current statement is a loop
                ast::walk_stmt(self, stmt);
            }

            fn visit_loop_end(&mut self, loop_id: &Option<LoopId>) {
                assert!(self.loop_id.is_none());
                self.loop_id = Some(loop_id.expect("missing loop id on loop body"));
            }

            // dummy these out to prevent walk_stmt from recursing into anything, ideally this
            // whole thing should mostly compile down to a single match?
            fn visit_block(&mut self, _: &ast::Block) {}
            fn visit_expr(&mut self, _: &Sp<ast::Expr>) {}
            fn visit_item(&mut self, _: &Sp<ast::Item>) {}
        }

        let mut visitor = GetStmtLoopIdVisitor { loop_id: None, used: false };
        visitor.visit_stmt(stmt);
        visitor.loop_id
    }
}

// =============================================================================

struct Visitor<'a, 'ctx> {
    ctx: &'a mut CompilerContext<'ctx>,
}

impl VisitMut for Visitor<'_, '_> {
    fn visit_block(&mut self, block: &mut ast::Block) {
        let mut desugarer = Desugarer { out: vec![], ctx: self.ctx };

        desugarer.desugar_block(None, std::mem::replace(block, ast::Block(vec![])));
        block.0 = desugarer.out;

        // for inner functions
        ast::walk_block_mut(self, block);
    }
}


struct Desugarer<'a, 'ctx> {
    out: Vec<Sp<ast::Stmt>>,
    ctx: &'a mut CompilerContext<'ctx>,
}

impl Desugarer<'_, '_> {
    pub fn desugar_block(&mut self, outer_diff_label: Option<&Sp<ast::DiffLabel>>, mut outer_block: ast::Block) {
        for mut outer_stmt in outer_block.0.drain(..) {
            let diff_label = {
                outer_stmt.value.diff_label.as_ref().or(outer_diff_label)
                    .filter(|label| label.mask != Some(DEFAULT_DIFFICULTY_MASK))
            };
            match outer_stmt.value.kind {
                ast::StmtKind::Block(block) => {
                    self.desugar_block(diff_label, block)
                },

                ast::StmtKind::Loop { block, .. } => {
                    self.desugar_loop_body(diff_label, block, None)
                },

                ast::StmtKind::While { do_keyword: Some(_), while_keyword, cond, block, .. } => {
                    let if_keyword = sp!(while_keyword.span => token![if]);
                    self.desugar_loop_body(diff_label, block, Some((if_keyword, cond.value)))
                },

                ast::StmtKind::While { do_keyword: None, while_keyword, cond, block, .. } => {
                    let if_keyword = sp!(while_keyword.span => token![if]);
                    self.desugar_conditional_region(diff_label, cond.span, if_keyword, cond.clone(), |self_| {
                        self_.desugar_loop_body(diff_label, block, Some((if_keyword, cond.value)));
                    });
                },

                ast::StmtKind::Times { clobber, count, block, .. } => {
                    let (clobber, temp_def) = match clobber {
                        Some(var) => (var, None),
                        None => {
                            let ident = self.ctx.gensym.gensym("count");
                            let ident = sp!(count.span => self.ctx.resolutions.attach_fresh_res(ident));
                            let def_id = self.ctx.define_local(ident.clone(), ScalarType::Int.into());
                            let var = sp!(count.span => ast::Var { ty_sigil: None, name: ast::VarName::new_non_reg(ident.value) });

                            self.make_stmt(diff_label, count.span, ast::StmtKind::Declaration {
                                ty_keyword: sp!(count.span => token![int]),
                                vars: vec![sp!(count.span => (var.clone(), None))],
                            });

                            (var, Some(def_id))
                        },
                    };
                    let end_span = block.end_span();

                    self.desugar_times(diff_label, clobber, count, block);

                    if let Some(def_id) = temp_def {
                        self.make_stmt(diff_label, end_span, ast::StmtKind::ScopeEnd(def_id));
                    }
                },

                ast::StmtKind::CondChain(ast::StmtCondChain { cond_blocks, else_block }) => {
                    let veryend = self.ctx.gensym.gensym("@cond_veryend#");

                    let num_blocks = cond_blocks.len();
                    for (index, ast::CondBlock { keyword, cond, block }) in cond_blocks.into_iter().enumerate() {
                        let is_final_if = index == num_blocks - 1;

                        let end_span = block.end_span();
                        self.desugar_conditional_region(diff_label, cond.span, keyword, cond, |self_| {
                            self_.desugar_block(diff_label, block);

                            // an unconditional jump over the rest of the blocks, if necessary
                            if !(is_final_if && else_block.is_none()) {
                                self_.make_goto(diff_label, end_span, None, veryend.clone());
                            }
                        });
                    }
                    if let Some(block) = else_block {
                        self.desugar_block(diff_label, block);
                    }

                    self.make_label_after_block(diff_label, veryend);
                },

                _ => {
                    outer_stmt.diff_label = diff_label.cloned();
                    self.out.push(outer_stmt)
                },
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
        diff_label: Option<&Sp<ast::DiffLabel>>,
        condjmp_span: Span,
        keyword: Sp<ast::CondKeyword>,
        cond: Sp<ast::Cond>,
        inner: impl FnOnce(&mut Self),
    ) {
        let skip_label = self.ctx.gensym.gensym("@cond#");
        self.out.push(rec_sp!(condjmp_span =>
            stmt_cond_goto!(#(keyword.negate()) #cond goto #(skip_label.clone()))
        ));

        inner(self);

        self.make_label_after_block(diff_label, skip_label);
    }

    fn desugar_times(
        &mut self,
        diff_label: Option<&Sp<ast::DiffLabel>>,
        clobber: Sp<ast::Var>,
        count: Sp<ast::Expr>,
        block: ast::Block,
    ) {
        let span = count.span;
        let count_as_const = count.as_const_int();

        self.make_stmt(diff_label, span, stmt_assign!(rec_sp!(span => as kind, #(clobber.clone()) = #count)));

        // unless count is statically known to be nonzero, we need an initial zero test
        let skip_label = self.ctx.gensym.gensym("@times_zero#");
        if let None | Some(0) = count_as_const {
            self.make_stmt(diff_label, span, stmt_cond_goto!(rec_sp!(span => as kind,
                if expr_binop![#(clobber.clone()) == #(0)] goto #(skip_label.clone())
            )));
        };

        let keyword = sp!(span => token![if]);
        let cond = ast::Cond::PreDecrement(clobber.clone());
        self.desugar_loop_body(diff_label, block, Some((keyword, cond)));

        self.make_label_after_block(diff_label, skip_label);
    }

    // desugars a `loop { .. }` or `do { ... } while (<cond>);`
    fn desugar_loop_body(&mut self, diff_label: Option<&Sp<ast::DiffLabel>>, block: ast::Block, cond: JumpInfo) {
        let label = self.ctx.gensym.gensym("@loop#");
        self.make_label(diff_label, block.start_span(), label.clone());
        self.desugar_block(diff_label, block);
        self.make_goto_after_block(diff_label, cond, label);
    }

    fn make_label(&mut self, diff_label: Option<&Sp<ast::DiffLabel>>, span: Span, ident: Ident) {
        self.make_stmt(diff_label, span, stmt_label!(rec_sp!(span => as kind, #ident)));
    }

    fn make_goto(&mut self, diff_label: Option<&Sp<ast::DiffLabel>>, span: Span, cond: JumpInfo, ident: Ident) {
        self.make_stmt(diff_label, span, match cond {
            None => stmt_goto!(rec_sp!(span => as kind, goto #ident)),
            Some((kw, cond))
                => stmt_cond_goto!(rec_sp!(span => as kind, #kw #cond goto #ident)),
        })
    }

    // Make a label after desugaring a block.
    // (this exists for convenience since the block will be destroyed and you can't call block.end_span())
    fn make_label_after_block(&mut self, diff_label: Option<&Sp<ast::DiffLabel>>, ident: Ident) {
        let last_written_stmt = self.out.last().expect("no written statements?!");
        let last_span = last_written_stmt.span.end_span();

        self.make_label(diff_label, last_span, ident);
    }

    // Make a goto after desugaring a block.
    // (this exists for convenience since the block will be destroyed and you can't call block.end_span())
    fn make_goto_after_block(&mut self, diff_label: Option<&Sp<ast::DiffLabel>>, cond: JumpInfo, label: Ident) {
        let last_written_stmt = self.out.last().expect("no written statements?!");
        let last_span = last_written_stmt.span.end_span();

        self.make_goto(diff_label, last_span, cond, label);
    }

    fn make_stmt(&mut self, diff_label: Option<&Sp<ast::DiffLabel>>, span: Span, kind: ast::StmtKind) {
        self.out.push(sp!(span => ast::Stmt {
            node_id: Some(self.ctx.next_node_id()),
            diff_label: diff_label.cloned(),
            kind,
        }))
    }
}

// Distinguishes `if (...) goto` vs `unless (...) goto` vs unconditional `goto`.
type JumpInfo = Option<(Sp<ast::CondKeyword>, ast::Cond)>;

#[cfg(test)]
mod tests {
    use crate::ast;
    use crate::resolve::RegId;
    use crate::vm::{AstVm, LoggedCall};
    use crate::value::{ScalarValue::{Int}, ScalarType as Ty};
    use crate::game::LanguageKey::Dummy;

    struct TestSpec<S> {
        globals: Vec<(&'static str, RegId, Ty)>,
        source: S,
    }

    impl<S: AsRef<[u8]>> TestSpec<S> {
        fn run(self) -> AstVm {
            let mut scope = crate::Builder::new().build();
            let mut truth = scope.truth();
            let mut ast = truth.parse::<ast::Block>("<input>", self.source.as_ref()).unwrap();

            let mut ctx = truth.ctx();
            for &(name, reg, ty) in &self.globals {
                ctx.define_global_reg_alias(Dummy, reg, sp!(name.parse().unwrap()));
                ctx.set_reg_ty(Dummy, reg, ty.into());
            }
            crate::passes::resolution::assign_languages(&mut ast.value, Dummy, &mut ctx).unwrap();
            crate::passes::resolution::resolve_names(&ast.value, &mut ctx).unwrap();
            crate::passes::resolution::aliases_to_raw(&mut ast.value, &mut ctx).unwrap();

            println!("{:#?}", ast.0);

            let mut vm_before = AstVm::new().with_max_iterations(1000);
            vm_before.run(&ast.0, &ctx);

            crate::passes::desugar_blocks::run(&mut ast.value, &mut ctx).unwrap();

            let mut vm_after = AstVm::new().with_max_iterations(1000);
            vm_after.run(&ast.0, &ctx);

            assert_eq!(vm_before.time, vm_after.time, "{}\n{}", vm_before, vm_after);
            assert_eq!(vm_before.real_time, vm_after.real_time, "{}\n{}", vm_before, vm_after);
            assert_eq!(vm_before.instr_log, vm_after.instr_log, "{}\n{}", vm_before, vm_after);
            for &(_, reg, _) in &self.globals {
                assert_eq!(vm_before.get_reg(reg), vm_after.get_reg(reg), "{}\n{}", vm_before, vm_after);
            }

            vm_after
        }
    }

    #[test]
    fn r#loop() {
        TestSpec {
            globals: vec![("X", RegId(20), Ty::Int)],
            source: r#"{
                X = 1;
                loop {
                    X *= 3;
                  +1:
                    if (X == 27) goto end;
                }
            +2:
            end:
            }"#,
        }.run();
    }

    #[test]
    fn times() {
        for ntimes in vec![11, 1, 0] {
            let vm = TestSpec {
                globals: vec![("X", RegId(20), Ty::Int)],
                source: format!(r#"{{
                    X = 1;
                    times({ntimes}) {{
                      +2:
                        ins_10(X);
                      +2:
                    }}
                }}"#, ntimes=ntimes),
            }.run();
            assert_eq!(vm.time, 4);
            assert_eq!(vm.real_time, ntimes * 4);
        }
    }

    #[test]
    fn times_clobber() {
        for ntimes in vec![11, 1, 0] {
            let vm = TestSpec {
                globals: vec![("X", RegId(20), Ty::Int)],
                source: format!(r#"{{
                    times(X = {ntimes}) {{
                      +2:
                        ins_10(X);
                      +2:
                    }}
                    ins_200(X);
                }}"#, ntimes=ntimes),
            }.run();
            assert_eq!(vm.time, 4);
            assert_eq!(vm.real_time, ntimes * 4);
            assert_eq!(vm.get_reg(RegId(20)).unwrap(), Int(0));
        }
    }

    #[test]
    fn do_while() {
        for mult in vec![4, 1, 0] {
            let vm = TestSpec {
                globals: vec![("X", RegId(20), Ty::Float)],
                source: format!(r#"{{
                    X = 0.33333333333333333333;
                    do {{
                      +2:
                        X += 5.0;
                        ins_10(X);
                      +2:
                    }} while (X < {stop_val});
                    ins_200(X);
                }}"#, stop_val = 0.1 + 5.0 * (mult as f32)),
            }.run();

            let expected_niter = match mult {
                0 => 1,
                n => n,
            };
            assert_eq!(vm.time, 4);
            assert_eq!(vm.instr_log.len(), expected_niter + 1);
        }
    }

    #[test]
    fn r#while() {
        for niter in vec![4, 1, 0] {
            let vm = TestSpec {
                globals: vec![("X", RegId(20), Ty::Float)],
                source: format!(r#"{{
                    X = 0.33333333333333333333;
                    while (X < {stop_val}) {{
                      +2:
                        X += 5.0;
                        ins_10(X);
                      +2:
                    }}
                    ins_200(X);
                }}"#, stop_val = 0.1 + 5.0 * (niter as f32)),
            }.run();

            assert_eq!(vm.time, 4);
            assert_eq!(vm.instr_log.len(), niter + 1);
        }
    }

    #[test]
    fn cond_chain() {
        let get_vm = |x| TestSpec {
            globals: vec![("X", RegId(20), Ty::Int)],
            source: format!(r#"{{
                X = {x};
                if (X == 2) {{
                  +2:
                    ins_2(X);
                  +3:  // 5
                }} else if (X >= 10) {{
                  +4:  // 9
                    ins_22(X);
                  +6:  // 15
                }} else {{
                  +1:  // 16
                    ins_6(X);
                  +4:  // 20
                }}
                +5: // 25
                ins_44(X);
            }}"#, x=x),
        }.run();

        let vm = get_vm(2);
        assert_eq!(vm.time, 25);
        assert_eq!(vm.instr_log, vec![
            LoggedCall { real_time: 2, opcode: 2, args: vec![Int(2)] },
            LoggedCall { real_time: 10, opcode: 44, args: vec![Int(2)] },
        ]);

        let vm = get_vm(12);
        assert_eq!(vm.time, 25);
        assert_eq!(vm.instr_log, vec![
            LoggedCall { real_time: 4, opcode: 22, args: vec![Int(12)] },
            LoggedCall { real_time: 15, opcode: 44, args: vec![Int(12)] },
        ]);

        let vm = get_vm(8);
        assert_eq!(vm.time, 25);
        assert_eq!(vm.instr_log, vec![
            LoggedCall { real_time: 1, opcode: 6, args: vec![Int(8)] },
            LoggedCall { real_time: 10, opcode: 44, args: vec![Int(8)] },
        ]);
    }
}
