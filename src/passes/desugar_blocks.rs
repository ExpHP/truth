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

#[cfg(test)]
mod tests {
    use crate::ast::{self, VisitMut};
    use crate::pos::Files;
    use crate::type_system::TypeSystem;
    use crate::var::RegId;
    use crate::vm::{AstVm, LoggedCall};
    use crate::value::ScalarValue::{Int};

    struct TestSpec<S> {
        globals: Vec<(&'static str, RegId)>,
        source: S,
    }

    impl<S: AsRef<[u8]>> TestSpec<S> {
        fn run(self) -> AstVm {
            let mut files = Files::new();
            let mut ast = files.parse::<ast::Block>("<input>", self.source.as_ref()).unwrap();

            let mut ty_ctx = TypeSystem::new();
            for &(name, reg) in &self.globals {
                ty_ctx.variables.declare_global_register_alias(name.parse().unwrap(), reg);
            }
            ty_ctx.resolve_names(&mut ast.value).unwrap();

            let mut vm_before = AstVm::new().with_max_iterations(1000);
            vm_before.run(&ast.0);

            let mut visitor = crate::passes::desugar_blocks::Visitor::new(&mut ty_ctx);
            visitor.visit_func_body(&mut ast);
            visitor.finish().unwrap();

            let mut vm_after = AstVm::new().with_max_iterations(1000);
            vm_after.run(&ast.0);

            assert_eq!(vm_before.time, vm_after.time, "{}\n{}", vm_before, vm_after);
            assert_eq!(vm_before.real_time, vm_after.real_time, "{}\n{}", vm_before, vm_after);
            assert_eq!(vm_before.call_log, vm_after.call_log, "{}\n{}", vm_before, vm_after);
            for &(_, reg) in &self.globals {
                assert_eq!(vm_before.get_reg(reg), vm_after.get_reg(reg), "{}\n{}", vm_before, vm_after);
            }
            vm_after
        }
    }

    #[test]
    fn r#loop() {
        TestSpec {
            globals: vec![("X", RegId(20))],
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
                globals: vec![("X", RegId(20))],
                source: format!(r#"{{
                    X = 1;
                    times({ntimes}) {{
                      +2:
                        foo(X);
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
                globals: vec![("X", RegId(20))],
                source: format!(r#"{{
                    times(X = {ntimes}) {{
                      +2:
                        foo(X);
                      +2:
                    }}
                    final(X);
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
                globals: vec![("X", RegId(20))],
                source: format!(r#"{{
                    X = 0.33333333333333333333;
                    do {{
                      +2:
                        X += 5.0;
                        foo(X);
                      +2:
                    }} while (X < {stop_val});
                    final(X);
                }}"#, stop_val = 0.1 + 5.0 * (mult as f32)),
            }.run();

            let expected_niter = match mult {
                0 => 1,
                n => n,
            };
            assert_eq!(vm.time, 4);
            assert_eq!(vm.call_log.len(), expected_niter + 1);
        }
    }

    #[test]
    fn r#while() {
        for niter in vec![4, 1, 0] {
            let vm = TestSpec {
                globals: vec![("X", RegId(20))],
                source: format!(r#"{{
                    X = 0.33333333333333333333;
                    while (X < {stop_val}) {{
                      +2:
                        X += 5.0;
                        foo(X);
                      +2:
                    }}
                    final(X);
                }}"#, stop_val = 0.1 + 5.0 * (niter as f32)),
            }.run();

            assert_eq!(vm.time, 4);
            assert_eq!(vm.call_log.len(), niter + 1);
        }
    }

    #[test]
    fn cond_chain() {
        let get_vm = |x| TestSpec {
            globals: vec![("X", RegId(20))],
            source: format!(r#"{{
                X = {x};
                if (X == 2) {{
                  +2:
                    two(X);
                  +3:  // 5
                }} else if (X >= 10) {{
                  +4:  // 9
                    two_digit(X);
                  +6:  // 15
                }} else {{
                  +1:  // 16
                    other(X);
                  +4:  // 20
                }}
                +5: // 25
                final(X);
            }}"#, x=x),
        }.run();

        let vm = get_vm(2);
        assert_eq!(vm.time, 25);
        assert_eq!(vm.call_log, vec![
            LoggedCall { real_time: 2, name: "two".parse().unwrap(), args: vec![Int(2)] },
            LoggedCall { real_time: 10, name: "final".parse().unwrap(), args: vec![Int(2)] },
        ]);

        let vm = get_vm(12);
        assert_eq!(vm.time, 25);
        assert_eq!(vm.call_log, vec![
            LoggedCall { real_time: 4, name: "two_digit".parse().unwrap(), args: vec![Int(12)] },
            LoggedCall { real_time: 15, name: "final".parse().unwrap(), args: vec![Int(12)] },
        ]);

        let vm = get_vm(8);
        assert_eq!(vm.time, 25);
        assert_eq!(vm.call_log, vec![
            LoggedCall { real_time: 1, name: "other".parse().unwrap(), args: vec![Int(8)] },
            LoggedCall { real_time: 10, name: "final".parse().unwrap(), args: vec![Int(8)] },
        ]);
    }
}
