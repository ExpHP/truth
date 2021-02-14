//! Lowering for languages without a stack.
//!
//! Responsible for compilation of expressions into instructions that use temporary registers.

use std::collections::{HashMap, BTreeSet};

use super::{unsupported, LowerStmt, LowerInstr, LowerArg};
use crate::llir::{InstrFormat, IntrinsicInstrKind, IntrinsicInstrs, SimpleArg};
use crate::error::{GatherErrorIteratorExt, CompileError};
use crate::pos::{Sp, Span};
use crate::ast::{self, Expr};
use crate::resolve::{ResolveId, RegId};
use crate::type_system::{TypeSystem, ScalarType};

use IntrinsicInstrKind as IKind;

/// Helper responsible for converting an AST into [`LowLevelStmt`]s.
pub (in crate::llir::lower) struct Lowerer<'ts> {
    pub out: Vec<LowerStmt>,
    pub intrinsic_instrs: IntrinsicInstrs,
    pub instr_format: &'ts dyn InstrFormat,
    pub ty_ctx: &'ts mut TypeSystem,
}

impl Lowerer<'_> {
    pub fn lower_sub_ast(
        &mut self,
        code: &[Sp<ast::Stmt>],
    ) -> Result<(), CompileError> {
        let mut th06_anm_end_span = None;
        code.iter().map(|stmt| {
            if let Some(end) = th06_anm_end_span {
                if !matches!(&stmt.body, ast::StmtBody::NoInstruction) { return Err(error!(
                    message("statement after end of script"),
                    primary(&stmt, "forbidden statement"),
                    secondary(&end, "marks the end of the script"),
                    note("In EoSD ANM, every script must have a single exit point (opcode 0 or 15), as the final instruction."),
                ))}
            }

            match &stmt.body {
                ast::StmtBody::Jump(goto) => {
                    self.lower_uncond_jump(stmt.span, stmt.time, goto)?;
                },


                ast::StmtBody::Assignment { var, op, value } => {
                    self.lower_assign_op(stmt.span, stmt.time, var, op, value)?;
                },


                ast::StmtBody::InterruptLabel(interrupt_id) => {
                    self.out.push(LowerStmt::Instr(LowerInstr {
                        time: stmt.time,
                        opcode: self.get_opcode(IKind::InterruptLabel, stmt.span, "interrupt label")?,
                        args: vec![sp!(interrupt_id.span => LowerArg::Raw(interrupt_id.value.into()))],
                    }));
                },


                ast::StmtBody::CondJump { keyword, cond, jump } => {
                    self.lower_cond_jump(stmt.span, stmt.time, keyword, cond, jump)?;
                },


                ast::StmtBody::Declaration { keyword, vars } => {
                    self.lower_var_declaration(stmt.span, stmt.time, keyword, vars)?;
                },


                ast::StmtBody::Expr(expr) => match &expr.value {
                    ast::Expr::Call { name, args } => {
                        let opcode = self.lower_func_stmt(stmt, name, args)?;
                        if self.instr_format.is_th06_anm_terminating_instr(opcode) {
                            th06_anm_end_span = Some(name);
                        }
                    },
                    _ => return Err(unsupported(&stmt.span, &format!("{} in {}", expr.descr(), stmt.body.descr()))),
                }, // match expr

                ast::StmtBody::Label(ident) => self.out.push(LowerStmt::Label { time: stmt.time, label: ident.clone() }),

                &ast::StmtBody::ScopeEnd(res) => self.out.push(LowerStmt::RegFree { res }),

                ast::StmtBody::NoInstruction => {}

                _ => return Err(unsupported(&stmt.span, stmt.body.descr())),
            }
            Ok(())
        }).collect_with_recovery()
    }

    // ------------------
    // Methods for lowering specific types of statement bodies.

    /// Lowers `func(<ARG1>, <ARG2>, <...>);`
    fn lower_func_stmt<'a>(
        &mut self,
        stmt: &Sp<ast::Stmt>,
        name: &Sp<ast::CallableName>,
        args: &[Sp<Expr>],
    ) -> Result<u16, CompileError> {
        // all function statements currently refer to single instructions
        let opcode = self.ty_ctx.func_opcode_from_ast(name).expect("non-instr func still present at lowering!");

        self.lower_instruction(stmt, opcode as _, args)
    }

    /// Lowers `func(<ARG1>, <ARG2>, <...>);` where `func` is an instruction alias.
    fn lower_instruction(
        &mut self,
        stmt: &Sp<ast::Stmt>,
        opcode: u16,
        args: &[Sp<Expr>],
    ) -> Result<u16, CompileError> {
        let mut temp_reses = vec![];
        let low_level_args = args.iter().map(|expr| {
            let lowered = match classify_expr(expr, self.ty_ctx)? {
                ExprClass::Simple(data) => data.lowered,
                ExprClass::NeedsTemp(data) => {
                    // Save this expression to a temporary
                    let (res, _) = self.define_temporary(stmt.time, &data)?;
                    let lowered = sp!(expr.span => LowerArg::Local { res, read_ty: data.read_ty });

                    temp_reses.push(res); // so we can free the register later
                    lowered
                },
            };
            Ok::<_, CompileError>(lowered)
        }).collect_with_recovery()?;

        self.out.push(LowerStmt::Instr(LowerInstr {
            time: stmt.time,
            opcode: opcode as _,
            args: low_level_args,
        }));

        for id in temp_reses.into_iter().rev() {
            self.undefine_temporary(id)?;
        }

        Ok(opcode)
    }

    /// Lowers `int x, y = 3, z;`
    fn lower_var_declaration(
        &mut self,
        _stmt_span: Span,
        stmt_time: i32,
        keyword: &Sp<ast::VarDeclKeyword>,
        vars: &[Sp<(Sp<ast::Var>, Option<Sp<ast::Expr>>)>],
    ) -> Result<(), CompileError>{
        if keyword.value == token![var] {
            return Err(unsupported(&keyword.span, "untyped variables"));
        }

        for pair in vars {
            let (var, expr) = &pair.value;
            match var.value {
                ast::Var::Reg { .. } => panic!("(bug?) declared var somehow resolved as register!"),
                ast::Var::Named { ref ident, .. } => {
                    let res = ident.expect_res();
                    self.out.push(LowerStmt::RegAlloc { res, cause: var.span });

                    if let Some(expr) = expr {
                        let assign_op = sp!(pair.span => token![=]);
                        self.lower_assign_op(pair.span, stmt_time, var, &assign_op, expr)?;
                    }
                },
            };
        }
        Ok(())
    }

    /// Lowers `a = <B>;`  or  `a *= <B>;`
    fn lower_assign_op(
        &mut self,
        span: Span,
        time: i32,
        var: &Sp<ast::Var>,
        assign_op: &Sp<ast::AssignOpKind>,
        rhs: &Sp<ast::Expr>,
    ) -> Result<(), CompileError> {
        let (lowered_var, ty_var) = lower_var_to_arg(var, self.ty_ctx)?;

        let data_rhs = match classify_expr(rhs, self.ty_ctx)? {
            // a = <atom>;
            // a += <atom>;
            ExprClass::Simple(SimpleExpr { lowered: lowered_rhs, ty: ty_rhs }) => {
                assert_eq!(ty_var, ty_rhs, "already type-checked");
                self.out.push(LowerStmt::Instr(LowerInstr {
                    time,
                    opcode: self.get_opcode(IKind::AssignOp(assign_op.value, ty_var), span, "update assignment with this operation")?,
                    args: vec![lowered_var, lowered_rhs],
                }));
                return Ok(());
            },
            ExprClass::NeedsTemp(data) => data,
        };

        // a = _f(<expr>);
        // a *= _f(<expr>);
        if data_rhs.read_ty != data_rhs.tmp_ty {
            // Regardless of what the expression contains, assign it to a temporary.
            // (i.e.:    `float tmp = <expr>;  a = $tmp;`
            let (tmp_res, tmp_as_expr) = self.define_temporary(time, &data_rhs)?;
            self.lower_assign_op(span, time, var, assign_op, &tmp_as_expr)?;
            self.undefine_temporary(tmp_res)?;
            return Ok(());
        }

        // complex expressions without a cast
        match (assign_op.value, &data_rhs.tmp_expr.value) {
            // a = <expr> + <expr>;
            (ast::AssignOpKind::Assign, Expr::Binop(a, binop, b)) => {
                self.lower_assign_direct_binop(span, time, var, assign_op, rhs.span, a, binop, b)
            },

            // a = -<expr>;
            // a = sin(<expr>);
            (ast::AssignOpKind::Assign, Expr::Unop(unop, b)) => {
                self.lower_assign_direct_unop(span, time, var, assign_op, rhs.span, unop, b)
            },

            // a = <any other expr>;
            // a += <expr>;
            (_, _) => {
                match assign_op.value {
                    // a = <big expr>
                    // if none of the other branches handled it yet, we can't do it
                    ast::AssignOpKind::Assign => Err(unsupported(&rhs.span, "this expression")),

                    // a += <expr>;
                    // split out to: `tmp = <expr>;  a += tmp;`
                    _ => {
                        let (tmp_res, tmp_var_expr) = self.define_temporary(time, &data_rhs)?;
                        self.lower_assign_op(span, time, var, assign_op, &tmp_var_expr)?;
                        self.undefine_temporary(tmp_res)?;
                        Ok(())
                    },
                }
            },
        }
    }

    /// Lowers `a = <B> * <C>;`
    fn lower_assign_direct_binop(
        &mut self,
        span: Span,
        time: i32,
        var: &Sp<ast::Var>,
        eq_sign: &Sp<ast::AssignOpKind>,
        rhs_span: Span,
        a: &Sp<Expr>,
        binop: &Sp<ast::BinopKind>,
        b: &Sp<Expr>,
    ) -> Result<(), CompileError> {
        // So right here, we have something like `v = <A> * <B>`. If <A> and <B> are both simple arguments (literals or
        // variables), we can emit this as one instruction. Otherwise, we need to break it up.  In the general case this
        // would mean producing
        //
        //     int tmp;
        //     tmp = <A>;      // recursive call
        //     v = tmp * <B>;  // recursive call
        //
        // but sometimes it's possible to do this without a temporary by reusing the destination variable `v`, such as:
        //
        //     v = <A>;        // recursive call
        //     v = tmp * <B>;  // recursive call

        // Evaluate the first subexpression if necessary.
        let simple_a = match classify_expr(a, self.ty_ctx)? {
            ExprClass::NeedsTemp(data_a) => {
                if data_a.tmp_ty == data_a.read_ty && !expr_uses_var(b, var) {
                    // we can reuse the output variable!
                    let var_as_expr = self.compute_temporary_expr(time, var, &data_a)?;
                    self.lower_assign_direct_binop(span, time, var, eq_sign, rhs_span, &var_as_expr, binop, b)?;
                } else {
                    // we need a temporary, either due to the type cast or to avoid invalidating the other subexpression
                    let (tmp_res, tmp_as_expr) = self.define_temporary(time, &data_a)?;
                    self.lower_assign_direct_binop(span, time, var, eq_sign, rhs_span, &tmp_as_expr, binop, b)?;
                    self.undefine_temporary(tmp_res)?;
                }
                return Ok(());
            },
            ExprClass::Simple(simple) => simple,
        };

        // FIXME: This is somewhat copy-pasta-y.  It's possible to write this and the above into a loop with two
        //        iterations, but the end result looked pretty awkward last time I tried.
        // First guy is simple.  Evaluate the second subexpression if necessary.
        let simple_b = match classify_expr(b, self.ty_ctx)? {
            ExprClass::NeedsTemp(data_b) => {
                // similar conditions apply...
                if data_b.tmp_ty == data_b.read_ty && !expr_uses_var(a, var) {
                    // we can reuse the output variable!
                    let var_as_expr = self.compute_temporary_expr(time, var, &data_b)?;
                    self.lower_assign_direct_binop(span, time, var, eq_sign, rhs_span, a, binop, &var_as_expr)?;
                } else {
                    // we need a temporary, either due to the type cast or to avoid invalidating the other subexpression
                    let (tmp_res, tmp_as_expr) = self.define_temporary(time, &data_b)?;
                    self.lower_assign_direct_binop(span, time, var, eq_sign, rhs_span, a, binop, &tmp_as_expr)?;
                    self.undefine_temporary(tmp_res)?;
                }
                return Ok(());
            },
            ExprClass::Simple(simple) => simple,
        };

        // They're both simple.  Emit a primitive instruction.
        let (lowered_var, ty_var) = lower_var_to_arg(var, self.ty_ctx)?;
        let ty_rhs = ast::Expr::binop_ty(binop.value, &a.value, self.ty_ctx);
        assert_eq!(ty_var, ty_rhs, "already type-checked");

        self.out.push(LowerStmt::Instr(LowerInstr {
            time,
            opcode: self.get_opcode(IKind::Binop(binop.value, ty_var), span, "this binary operation")?,
            args: vec![lowered_var, simple_a.lowered, simple_b.lowered],
        }));
        Ok(())
    }

    /// Lowers `a = -<B>;`
    fn lower_assign_direct_unop(
        &mut self,
        span: Span,
        time: i32,
        var: &Sp<ast::Var>,
        eq_sign: &Sp<ast::AssignOpKind>,
        rhs_span: Span,
        unop: &Sp<ast::UnopKind>,
        b: &Sp<Expr>,
    ) -> Result<(), CompileError> {
        // `a = -b;` is not a native instruction.  Just treat it as `a = 0 - b;`
        if unop.value == token![-] {
            let ty = b.compute_ty(self.ty_ctx).expect("type-checked so not void");
            let zero = sp!(unop.span => ast::Expr::zero(ty));
            let minus = sp!(unop.span => token![-]);
            self.lower_assign_direct_binop(span, time, var, eq_sign, rhs_span, &zero, &minus, b)?;
            return Ok(());
        }

        match classify_expr(b, self.ty_ctx)? {
            ExprClass::NeedsTemp(data_b) => {
                // Unary operations can reuse their destination register as long as it's the same type.
                if data_b.tmp_ty == data_b.read_ty {
                    // compile to:   a = <B>;
                    //               a = sin(a);
                    let var_as_expr = self.compute_temporary_expr(time, var, &data_b)?;
                    self.lower_assign_direct_unop(span, time, var, eq_sign, rhs_span, unop, &var_as_expr)?;
                } else {
                    // compile to:   temp = <B>;
                    //               a = sin(temp);
                    let (tmp_res, tmp_as_expr) = self.define_temporary(time, &data_b)?;
                    self.lower_assign_direct_unop(span, time, var, eq_sign, rhs_span, unop, &tmp_as_expr)?;
                    self.undefine_temporary(tmp_res)?;
                }
                Ok(())
            },

            ExprClass::Simple(data_b) => {
                let (lowered_var, ty_var) = lower_var_to_arg(var, self.ty_ctx)?;
                let ty_rhs = ast::Expr::unop_ty(unop.value, b, self.ty_ctx);
                assert_eq!(ty_var, ty_rhs, "already type-checked");
                let ty = ty_var;

                match unop.value {
                    // These are all handled other ways
                    token![_S] |
                    token![_f] |
                    token![unop -] => unreachable!(),

                    // TODO: we *could* polyfill this with some conditional jumps but bleccccch
                    token![!] => return Err(unsupported(&span, "logical not operator")),

                    token![sin] |
                    token![cos] |
                    token![sqrt] => self.out.push(LowerStmt::Instr(LowerInstr {
                        time,
                        opcode: self.get_opcode(IKind::Unop(unop.value, ty), span, "this unary operation")?,
                        args: vec![lowered_var, data_b.lowered],
                    })),
                }
                Ok(())
            },
        }
    }

    fn lower_uncond_jump(&mut self, stmt_span: Span, stmt_time: i32, goto: &ast::StmtGoto) -> Result<(), CompileError> {
        if goto.time.is_some() && !self.instr_format.jump_has_time_arg() {
            return Err(unsupported(&stmt_span, "goto @ time"));
        }

        let (label_arg, time_arg) = lower_goto_args(goto);

        self.out.push(LowerStmt::Instr(LowerInstr {
            time: stmt_time,
            opcode: self.get_opcode(IKind::Jmp, stmt_span, "'goto'")?,
            args: vec![label_arg, time_arg],
        }));
        Ok(())
    }

    /// Lowers `if (<cond>) goto label @ time;`
    fn lower_cond_jump(
        &mut self,
        stmt_span: Span,
        stmt_time: i32,
        keyword: &Sp<ast::CondKeyword>,
        cond: &Sp<ast::Cond>,
        goto: &ast::StmtGoto,
    ) -> Result<(), CompileError>{
        match &cond.value {
            ast::Cond::PreDecrement(var) => self.lower_cond_jump_predecrement(stmt_span, stmt_time, keyword, var, goto),
            ast::Cond::Expr(expr) => self.lower_cond_jump_expr(stmt_span, stmt_time, keyword, expr, goto),
        }
    }

    fn lower_cond_jump_predecrement(
        &mut self,
        stmt_span: Span,
        stmt_time: i32,
        keyword: &Sp<ast::CondKeyword>,
        var: &Sp<ast::Var>,
        goto: &ast::StmtGoto,
    ) -> Result<(), CompileError>{
        match keyword.value {
            // 'if (--var) goto label'
            token![if] => {
                let (arg_var, ty_var) = lower_var_to_arg(var, self.ty_ctx)?;
                let (arg_label, arg_time) = lower_goto_args(goto);
                if ty_var != ScalarType::Int {
                    return Err(error!(
                        message("type error"),
                        primary(var, "expected an int, got {}", ty_var.descr()),
                        secondary(keyword, "required by this"),
                    ));
                }

                self.out.push(LowerStmt::Instr(LowerInstr {
                    time: stmt_time,
                    opcode: self.get_opcode(IKind::CountJmp, stmt_span, "decrement jump")?,
                    args: vec![arg_var, arg_label, arg_time],
                }));
                Ok(())
            },

            // 'unless (--var) goto label'
            token![unless] => {
                // compile to:
                //
                //        if (--var) goto skip:
                //        goto label
                //     skip:

                let skip_label = sp!(keyword.span => self.ty_ctx.gensym("@unless_predec_skip#"));
                let if_keyword = sp!(keyword.span => token![if]);
                let if_goto = ast::StmtGoto { time: None, destination: skip_label.clone() };

                self.lower_cond_jump_predecrement(stmt_span, stmt_time, &if_keyword, var, &if_goto)?;
                self.lower_uncond_jump(stmt_span, stmt_time, goto)?;
                self.out.push(LowerStmt::Label { time: stmt_time, label: skip_label });
                Ok(())
            },
        }
    }

    fn lower_cond_jump_expr(
        &mut self,
        stmt_span: Span,
        stmt_time: i32,
        keyword: &Sp<ast::CondKeyword>,
        expr: &Sp<ast::Expr>,
        goto: &ast::StmtGoto,
    ) -> Result<(), CompileError>{
        match &expr.value {
            // 'if (<A> <= <B>) goto label'
            // 'unless (<A> <= <B>) goto label'
            Expr::Binop(a, binop, b) if binop.is_comparison() => {
                self.lower_cond_jump_comparison(stmt_span, stmt_time, keyword, a, binop, b, goto)
            },

            // 'if (<A> || <B>) goto label'
            // 'unless (<A> || <B>) goto label'
            Expr::Binop(a, binop, b) if matches!(binop.value, token![&&] | token![||]) => {
                self.lower_cond_jump_logic_binop(stmt_span, stmt_time, keyword, a, binop, b, goto)
            },

            // 'if (!<B>) goto label'
            // 'unless (!<B>) goto label'
            Expr::Unop(sp_pat!(op_span => token![!]), b) => {
                let negated_kw = sp!(*op_span => keyword.negate());
                self.lower_cond_jump_expr(stmt_span, stmt_time, &negated_kw, b, goto)
            },

            // other arbitrary expressions: use `<if|unless> (<expr> != 0)`
            _ => {
                let ty = expr.compute_ty(self.ty_ctx).expect("type-checked so not void");
                let zero = sp!(expr.span => ast::Expr::zero(ty));
                let ne_sign = sp!(expr.span => token![!=]);
                self.lower_cond_jump_comparison(stmt_span, stmt_time, keyword, expr, &ne_sign, &zero, goto)
            },
        }
    }

    /// Lowers `if (<A> != <B>) goto label @ time;` and similar
    fn lower_cond_jump_comparison(
        &mut self,
        stmt_span: Span,
        stmt_time: i32,
        keyword: &Sp<ast::CondKeyword>,
        a: &Sp<Expr>,
        binop: &Sp<ast::BinopKind>,
        b: &Sp<Expr>,
        goto: &ast::StmtGoto,
    ) -> Result<(), CompileError>{
        match (classify_expr(a, self.ty_ctx)?, classify_expr(b, self.ty_ctx)?) {
            // `if (<A> != <B>) ...` (or `unless (<A> != <B>) ...`)
            // split out to: `tmp = <A>;  if (tmp != <B>) ...`;
            (ExprClass::NeedsTemp(data_a), _) => {
                let (id, var_expr) = self.define_temporary(stmt_time, &data_a)?;
                self.lower_cond_jump_comparison(stmt_span, stmt_time, keyword, &var_expr, binop, b, goto)?;
                self.undefine_temporary(id)?;
            },

            // `if (a != <B>) ...` (or `unless (a != <B>) ...`)
            // split out to: `tmp = <B>;  if (a != tmp) ...`;
            (ExprClass::Simple(_), ExprClass::NeedsTemp(data_b)) => {
                let (id, var_expr) = self.define_temporary(stmt_time, &data_b)?;
                self.lower_cond_jump_comparison(stmt_span, stmt_time, keyword, a, binop, &var_expr, goto)?;
                self.undefine_temporary(id)?;
            },

            // `if (a != b) ...` (or `unless (a != b) ...`)
            (ExprClass::Simple(data_a), ExprClass::Simple(data_b)) => {
                let binop = sp!(binop.span => match keyword.value {
                    token![if] => binop.value,
                    token![unless] => binop.negate_comparison().expect("lower_cond_jump_comparison called with non-comparison operator"),
                });

                let ty_arg = ast::Expr::binop_ty(binop.value, &a.value, self.ty_ctx);
                let (lowered_label, lowered_time) = lower_goto_args(goto);
                self.out.push(LowerStmt::Instr(LowerInstr {
                    time: stmt_time,
                    opcode: self.get_opcode(IKind::CondJmp(binop.value, ty_arg), binop.span, "conditional jump with this operator")?,
                    args: vec![data_a.lowered, data_b.lowered, lowered_label, lowered_time],
                }));
            },
        }
        Ok(())
    }

    /// Lowers `if (<A> || <B>) goto label @ time;` and similar
    fn lower_cond_jump_logic_binop(
        &mut self,
        stmt_span: Span,
        stmt_time: i32,
        keyword: &Sp<ast::CondKeyword>,
        a: &Sp<Expr>,
        binop: &Sp<ast::BinopKind>,
        b: &Sp<Expr>,
        goto: &ast::StmtGoto,
    ) -> Result<(), CompileError> {
        let is_easy_case = match (keyword.value, binop.value) {
            (token![if], token![||]) => true,
            (token![if], token![&&]) => false,
            (token![unless], token![&&]) => true,
            (token![unless], token![||]) => false,
            _ => unreachable!("non-logic binop in lower_cond_jump_logic_binop: {}", binop)
        };

        if is_easy_case {
            // 'if (a || b) ...' can just split up into 'if (a) ...' and 'if (b) ...'.
            // Likewise for 'unless (a && b) ...'
            self.lower_cond_jump_expr(stmt_span, stmt_time, keyword, a, goto)?;
            self.lower_cond_jump_expr(stmt_span, stmt_time, keyword, b, goto)?;
            Ok(())

        } else {
            // The other case is only slightly more unsightly.
            // 'if (a && b) goto label' compiles to:
            //
            //         unless (a) goto skip;
            //         unless (b) goto skip;
            //         goto label;
            //      skip:

            let negated_kw = sp!(keyword.span => keyword.negate());
            let skip_label = sp!(binop.span => self.ty_ctx.gensym("@unless_predec_skip#"));
            let skip_goto = ast::StmtGoto { time: None, destination: skip_label.clone() };

            self.lower_cond_jump_expr(stmt_span, stmt_time, &negated_kw, a, &skip_goto)?;
            self.lower_cond_jump_expr(stmt_span, stmt_time, &negated_kw, b, &skip_goto)?;
            self.lower_uncond_jump(stmt_span, stmt_time, goto)?;
            self.out.push(LowerStmt::Label { time: stmt_time, label: skip_label });
            Ok(())
        }
    }

    // ------------------
    // Helpers for dealing with temporaries.

    /// Declares a new register-allocated temporary and initializes it with an expression.
    ///
    /// When done emitting instructions that use the temporary, one should call [`Self::undefine_temporary`].
    fn define_temporary(
        &mut self,
        time: i32,
        data: &TemporaryExpr<'_>,
    ) -> Result<(ResolveId, Sp<Expr>), CompileError> {
        let (res, var) = self.allocate_temporary(data.tmp_expr.span, data.tmp_ty)?;
        let var_as_expr = self.compute_temporary_expr(time, &var, data)?;

        Ok((res, var_as_expr))
    }

    /// Evaluate a temporary expression into an existing variable by emitting the instructions that compute it.
    ///
    /// For convenience, also returns an expression for reading the variable as a specific type, as you presumably
    /// have a reason for storing this value there. (the read type is allowed to differ from the expression's type)
    fn compute_temporary_expr(
        &mut self,
        time: i32,
        var: &Sp<ast::Var>,
        data: &TemporaryExpr<'_>,
    ) -> Result<Sp<Expr>, CompileError> {
        let eq_sign = sp!(data.tmp_expr.span => token![=]);
        self.lower_assign_op(data.tmp_expr.span, time, var, &eq_sign, data.tmp_expr)?;

        let mut read_var = var.clone();
        let read_ty_sigil = get_temporary_read_ty(data.read_ty, var.span)?;
        read_var.set_ty_sigil(Some(read_ty_sigil));
        Ok(sp!(var.span => ast::Expr::Var(read_var)))
    }

    /// Emits an intrinsic that cleans up a register-allocated temporary.
    fn undefine_temporary(&mut self, res: ResolveId) -> Result<(), CompileError> {
        self.out.push(LowerStmt::RegFree { res });
        Ok(())
    }

    /// Grabs a new unique [`VarId`] and constructs an [`ast::Var`] for assigning a value to it.
    /// Emits an intrinsic to allocate a register to it.
    ///
    /// Call [`Self::undefine_temporary`] afterwards to clean up.
    fn allocate_temporary(
        &mut self,
        span: Span,
        tmp_ty: ScalarType,
    ) -> Result<(ResolveId, Sp<ast::Var>), CompileError> {
        // FIXME: It bothers me that we have to actually allocate an identifier here.
        let ident = sp!(span => self.ty_ctx.gensym("temp").into());
        let ident = self.ty_ctx.add_local(ident, Some(tmp_ty));
        let sigil = get_temporary_read_ty(tmp_ty, span)?;
        let res = ident.expect_res();

        let var = sp!(span => ast::Var::Named { ty_sigil: Some(sigil), ident: ident.value });
        self.out.push(LowerStmt::RegAlloc { res, cause: span });

        Ok((res, var))
    }

    fn get_opcode(&self, kind: IntrinsicInstrKind, span: Span, descr: &str) -> Result<u16, CompileError> {
        self.intrinsic_instrs.get_opcode(kind, span, descr)
    }
}

// This function makes sure string-typed temporaries produce errors.
//
// String-typed temporaries can legally occur as the result of expressions like `I0 ? "a" : "b"` which can't be
// const-folded.  However, there are no string registers, so we must emit an error instead.
//
// Basically, this function performs this check at the time that we are trying to generate the Var expression
// that would be used to read the temporary.  This does feel like an unusual time to perform this check,
// but it works out this way because we need to go from a type with a string variant to a type that has none.
fn get_temporary_read_ty(ty: ScalarType, span: Span) -> Result<ast::VarReadType, CompileError> {
    ty.sigil().ok_or_else(|| error!(
        message("runtime temporary of non-numeric type"),
        primary(span, "temporary {} cannot be created", ty.descr_plural())
    ))
}

enum ExprClass<'a> {
    Simple(SimpleExpr),
    NeedsTemp(TemporaryExpr<'a>),
}

struct SimpleExpr {
    lowered: Sp<LowerArg>,
    ty: ScalarType,
}

struct TemporaryExpr<'a> {
    /// The part that must be stored to a temporary. Usually the whole expression, but for a cast we
    /// only store the inner part as a temporary.
    tmp_expr: &'a Sp<Expr>,
    tmp_ty: ScalarType,
    read_ty: ScalarType,
}

fn classify_expr<'a>(arg: &'a Sp<ast::Expr>, ty_ctx: &TypeSystem) -> Result<ExprClass<'a>, CompileError> {
    match arg.value {
        ast::Expr::LitInt { value, .. } => Ok(ExprClass::Simple(SimpleExpr {
            lowered: sp!(arg.span => LowerArg::Raw(value.into())),
            ty: ScalarType::Int,
        })),
        ast::Expr::LitFloat { value, .. } => Ok(ExprClass::Simple(SimpleExpr {
            lowered: sp!(arg.span => LowerArg::Raw(value.into())),
            ty: ScalarType::Float,
        })),
        ast::Expr::LitString(ast::LitString { ref string, .. }) => Ok(ExprClass::Simple(SimpleExpr {
            lowered: sp!(arg.span => LowerArg::Raw(string.clone().into())),
            ty: ScalarType::String,
        })),
        ast::Expr::Var(ref var) => {
            let (lowered, ty) = lower_var_to_arg(var, ty_ctx)?;
            Ok(ExprClass::Simple(SimpleExpr { lowered, ty }))
        },

        // Here we treat casts.  A cast of any expression is understood to require a temporary of
        // the *input* type of the cast, but not the output type.  For example:
        //
        //             foo(_f($I + 3));
        //
        // Ideally, this should compile into using only a single integer scratch register:
        //
        //             int tmp = $I + 3;
        //             foo(%tmp);
        //
        ast::Expr::Unop(unop, ref b) if unop.is_cast() => {
            let (tmp_ty, read_ty) = match unop.value {
                token![_S] => (ScalarType::Float, ScalarType::Int),
                token![_f] => (ScalarType::Int, ScalarType::Float),
                _ => unreachable!("filtered out by is_cast()"),
            };
            Ok(ExprClass::NeedsTemp(TemporaryExpr { tmp_ty, read_ty, tmp_expr: b }))
        },

        // Anything else needs a temporary of the same type, consisting of the whole expression.
        _ => Ok(ExprClass::NeedsTemp({
            let ty = arg.compute_ty(ty_ctx).expect("shouldn't be void");
            TemporaryExpr { tmp_expr: arg, tmp_ty: ty, read_ty: ty }
        })),
    }
}

fn lower_var_to_arg(var: &Sp<ast::Var>, ty_ctx: &TypeSystem) -> Result<(Sp<LowerArg>, ScalarType), CompileError> {
    let read_ty = ty_ctx.var_read_ty_from_ast(var).expect("shoulda been type-checked");

    // Up to this point in compilation, register aliases use Var::Named.
    // But now, we want both registers and their aliases to be resolved to a register
    let arg = match ty_ctx.var_reg_from_ast(var) {
        Ok(reg) => LowerArg::Raw(SimpleArg::from_reg(reg, read_ty)),
        Err(res) => LowerArg::Local { res, read_ty },
    };
    Ok((sp!(var.span => arg), read_ty))
}

fn lower_goto_args(goto: &ast::StmtGoto) -> (Sp<LowerArg>, Sp<LowerArg>) {
    let label_arg = goto.destination.clone().sp_map(LowerArg::Label);
    let time_arg = match goto.time {
        Some(time) => time.sp_map(|t| LowerArg::Raw(t.into())),
        None => goto.destination.clone().sp_map(LowerArg::TimeOf),
    };
    (label_arg, time_arg)
}

fn expr_uses_var(ast: &Sp<ast::Expr>, var: &ast::Var) -> bool {
    use ast::Visit;

    struct Visitor<'a> {
        var: &'a ast::Var,
        found: bool,
    };

    impl Visit for Visitor<'_> {
        fn visit_var(&mut self, var: &Sp<ast::Var>) {
            if self.var.eq_upto_ty(var) {
                self.found = true;
            }
        }
    }

    let mut v = Visitor { var, found: false };
    v.visit_expr(ast);
    v.found
}

// =============================================================================

/// Eliminates all `LowerArg::Local`s by allocating registers for them.
pub (in crate::llir::lower) fn assign_registers(
    code: &mut [LowerStmt],
    format: &dyn InstrFormat,
    ty_ctx: &TypeSystem,
) -> Result<(), CompileError> {
    let used_regs = get_used_regs(code);

    let mut unused_regs = format.general_use_regs();
    for vec in unused_regs.values_mut() {
        vec.retain(|reg| !used_regs.contains(reg));
        vec.reverse();  // since we'll be popping from these lists
    }

    let mut local_regs = HashMap::<ResolveId, (RegId, ScalarType, Span)>::new();
    let mut has_used_scratch: Option<Span> = None;
    let mut has_anti_scratch_ins = false;

    for stmt in code {
        match stmt {
            LowerStmt::RegAlloc { res, ref cause } => {
                has_used_scratch.get_or_insert(*cause);

                let required_ty = ty_ctx.var_inherent_ty(*res).expect("(bug!) this should have been type-checked!");

                let reg = unused_regs[required_ty].pop().ok_or_else(|| {
                    let ty_as_sigil = ast::VarReadType::from_ty(required_ty).expect("reg ty is always numeric");
                    let stringify_reg = |reg| crate::fmt::stringify(&ty_ctx.reg_to_ast(reg, ty_as_sigil));

                    let mut error = crate::error::Diagnostic::error();
                    error.message(format!("script too complex to compile"));
                    error.primary(cause, format!("no more registers of this type!"));
                    for &(scratch_reg, scratch_ty, scratch_span) in local_regs.values() {
                        if scratch_ty == required_ty {
                            error.secondary(scratch_span, format!("{} holds this", stringify_reg(scratch_reg)));
                        }
                    }
                    let regs_of_ty = format.general_use_regs()[required_ty].clone();
                    let unavailable_strs = regs_of_ty.iter().copied()
                        .filter(|reg| used_regs.contains(reg))
                        .map(stringify_reg)
                        .collect::<Vec<_>>();
                    if !unavailable_strs.is_empty() {
                        error.note(format!(
                            "the following registers are unavailable due to explicit use: {}",
                            unavailable_strs.join(", "),
                        ));
                    }

                    error
                })?;

                assert!(local_regs.insert(*res, (reg, required_ty, *cause)).is_none());
            },
            LowerStmt::RegFree { res } => {
                let inherent_ty = ty_ctx.var_inherent_ty(*res).expect("(bug!) we allocated a reg so it must have a type");
                let (reg, _, _) = local_regs.remove(&res).expect("(bug!) RegFree without RegAlloc!");
                unused_regs[inherent_ty].push(reg);
            },
            LowerStmt::Instr(instr) => {
                if format.instr_disables_scratch_regs(instr.opcode) {
                    has_anti_scratch_ins = true;
                }

                for arg in &mut instr.args {
                    if let LowerArg::Local { res, read_ty } = arg.value {
                        arg.value = LowerArg::Raw(SimpleArg::from_reg(local_regs[&res].0, read_ty));
                    }
                }
            },
            LowerStmt::Label { .. } => {},
        }
    }

    if has_anti_scratch_ins {
        if let Some(span) = has_used_scratch {
            return Err(error!(
                message("scratch registers are disabled in this script"),
                primary(span, "this requires a scratch register"),
                // FIXME: If we ever add spans around Instr, we should give its span instead of this unhelpful note
                note("Automatic register allocation is disabled in this script because it contains an instruction that uses variables without mentioning them"),
            ))
        }
    }

    Ok(())
}

// Gather all explicitly-used registers in the source. (so that we can avoid using them for scratch)
fn get_used_regs(func_body: &[LowerStmt]) -> BTreeSet<RegId> {
    func_body.iter()
        .filter_map(|stmt| match stmt {
            LowerStmt::Instr(LowerInstr { args, .. }) => Some(args),
            _ => None
        }).flat_map(|args| args.iter().filter_map(|arg| match &arg.value {
            LowerArg::Raw(arg) => arg.get_reg_id(),
            _ => None,
        })).collect()
}
