//! Lowering for languages without a stack.
//!
//! Responsible for compilation of expressions into instructions that use temporary registers.

use std::collections::{HashMap, BTreeSet};

use super::{LowerStmt, LowerInstr, LowerArgs, LowerArg};
use crate::diagnostic::Diagnostic;
use crate::llir::{InstrFormat, IntrinsicInstrKind, IntrinsicInstrs, SimpleArg};
use crate::error::{GatherErrorIteratorExt, ErrorReported};
use crate::pos::{Sp, Span};
use crate::ast::{self, pseudo::PseudoArgData};
use crate::resolve::{DefId, RegId};
use crate::value::ScalarType;
use crate::context::CompilerContext;

use IntrinsicInstrKind as IKind;

/// Helper responsible for converting an AST into [`LowLevelStmt`]s.
pub (in crate::llir::lower) struct Lowerer<'a, 'ctx> {
    pub out: Vec<LowerStmt>,
    pub intrinsic_instrs: IntrinsicInstrs,
    pub instr_format: &'a dyn InstrFormat,
    pub ctx: &'a mut CompilerContext<'ctx>,
}

impl Lowerer<'_, '_> {
    pub fn lower_sub_ast(
        &mut self,
        code: &[Sp<ast::Stmt>],
    ) -> Result<(), ErrorReported> {
        let mut th06_anm_end_span = None;
        code.iter().map(|stmt| {
            if let Some(end) = th06_anm_end_span {
                if !matches!(&stmt.body, ast::StmtBody::NoInstruction) { return Err(self.ctx.emitter.emit(error!(
                    message("statement after end of script"),
                    primary(&stmt, "forbidden statement"),
                    secondary(&end, "marks the end of the script"),
                    note("In EoSD ANM, every script must have a single exit point (opcode 0 or 15), as the final instruction."),
                )))}
            }

            match &stmt.body {
                ast::StmtBody::Goto(goto) => {
                    self.lower_uncond_jump(stmt.span, stmt.time, goto)?;
                },


                ast::StmtBody::Assignment { var, op, value } => {
                    self.lower_assign_op(stmt.span, stmt.time, var, op, value)?;
                },


                ast::StmtBody::InterruptLabel(interrupt_id) => {
                    self.out.push(LowerStmt::Instr(LowerInstr {
                        time: stmt.time,
                        opcode: self.get_opcode(IKind::InterruptLabel, stmt.span, "interrupt label")?,
                        extra_arg: None,
                        user_param_mask: None,
                        args: LowerArgs::Known(vec![sp!(interrupt_id.span => LowerArg::Raw(interrupt_id.value.into()))]),
                    }));
                },


                ast::StmtBody::CondGoto { keyword, cond, goto } => {
                    self.lower_cond_jump(stmt.span, stmt.time, keyword, cond, goto)?;
                },


                ast::StmtBody::Declaration { ty_keyword, vars } => {
                    self.lower_var_declaration(stmt.span, stmt.time, ty_keyword, vars)?;
                },


                ast::StmtBody::Expr(expr) => match &expr.value {
                    ast::Expr::Call { name, pseudos, args } => {
                        let opcode = self.lower_func_stmt(stmt, name, pseudos, args)?;
                        if self.instr_format.is_th06_anm_terminating_instr(opcode) {
                            th06_anm_end_span = Some(name);
                        }
                    },
                    _ => return Err(self.unsupported(&stmt.span, &format!("{} in {}", expr.descr(), stmt.body.descr()))),
                }, // match expr

                ast::StmtBody::Label(ident) => self.out.push(LowerStmt::Label { time: stmt.time, label: ident.clone() }),

                &ast::StmtBody::ScopeEnd(def_id) => self.out.push(LowerStmt::RegFree { def_id }),

                ast::StmtBody::NoInstruction => {},

                // handled by helper
                ast::StmtBody::AbsTimeLabel { .. } => {},
                ast::StmtBody::RelTimeLabel { .. } => {},

                _ => return Err(self.unsupported(&stmt.span, stmt.body.descr())),
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
        pseudos: &[Sp<ast::PseudoArg>],
        args: &[Sp<ast::Expr>],
    ) -> Result<u16, ErrorReported> {
        // all function statements currently refer to single instructions
        let (lang, opcode) = self.ctx.func_opcode_from_ast(name).expect("non-instr func still present at lowering!");
        assert_eq!(lang, self.instr_format.language());

        self.lower_instruction(stmt, opcode as _, pseudos, args)
    }

    /// Lowers `func(<ARG1>, <ARG2>, <...>);` where `func` is an instruction alias.
    fn lower_instruction(
        &mut self,
        stmt: &Sp<ast::Stmt>,
        opcode: u16,
        pseudos: &[Sp<ast::PseudoArg>],
        args: &[Sp<ast::Expr>],
    ) -> Result<u16, ErrorReported> {
        let PseudoArgData {
            // fully unpack because we need to add errors for anything unsupported
            pop: pseudo_pop, blob: pseudo_blob, param_mask: pseudo_param_mask, extra_arg: pseudo_extra_arg,
        } = PseudoArgData::from_pseudos(pseudos).map_err(|e| self.ctx.emitter.emit(e))?;

        if let Some(pop) = pseudo_pop {
            if pop.value != 0 {
                return Err(self.unsupported(&pop.span, "stack-pop pseudo argument"));
            }
        }

        // records temporaries for function arguments
        let mut temp_def_ids = vec![];

        let low_level_args = match pseudo_blob {
            Some(blob) => {
                assert!(args.is_empty());
                LowerArgs::Unknown(sp!(blob.span => blob.to_vec()))
            },

            None => {
                // determine whether each argument can be directly used as is, or if it needs a temporary
                LowerArgs::Known(args.iter().map(|expr| {
                    let lowered = match classify_expr(expr, self.ctx)? {
                        ExprClass::Simple(data) => data.lowered,
                        ExprClass::NeedsTemp(data) => {
                            // Save this expression to a temporary
                            let (def_id, _) = self.define_temporary(stmt.time, &data)?;
                            let lowered = sp!(expr.span => LowerArg::Local { def_id, read_ty: data.read_ty });

                            temp_def_ids.push(def_id); // so we can free the register later
                            lowered
                        },
                    };
                    Ok::<_, ErrorReported>(lowered)
                }).collect_with_recovery()?)
            },
        };

        self.out.push(LowerStmt::Instr(LowerInstr {
            time: stmt.time,
            opcode: opcode as _,
            user_param_mask: pseudo_param_mask.map(|x| x.value),
            extra_arg: pseudo_extra_arg.map(|x| x.value),
            args: low_level_args,
        }));

        for id in temp_def_ids.into_iter().rev() {
            self.undefine_temporary(id)?;
        }

        Ok(opcode)
    }

    /// Lowers `int x, y = 3, z;`
    fn lower_var_declaration(
        &mut self,
        _stmt_span: Span,
        stmt_time: i32,
        keyword: &Sp<ast::TypeKeyword>,
        vars: &[Sp<(Sp<ast::Var>, Option<Sp<ast::Expr>>)>],
    ) -> Result<(), ErrorReported>{
        if keyword.value == token![var] {
            return Err(self.unsupported(&keyword.span, "untyped variables"));
        }

        for pair in vars {
            let (var, expr) = &pair.value;
            let ident = var.name.expect_ident();
            let def_id = self.ctx.resolutions.expect_def(ident);
            self.out.push(LowerStmt::RegAlloc { def_id, cause: var.span });

            if let Some(expr) = expr {
                let assign_op = sp!(pair.span => token![=]);
                self.lower_assign_op(pair.span, stmt_time, var, &assign_op, expr)?;
            }
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
    ) -> Result<(), ErrorReported> {
        let (lowered_var, ty_var) = lower_var_to_arg(var, self.ctx)?;

        let data_rhs = match classify_expr(rhs, self.ctx)? {
            // a = <atom>;
            // a += <atom>;
            ExprClass::Simple(SimpleExpr { lowered: lowered_rhs, ty: ty_rhs }) => {
                assert_eq!(ty_var, ty_rhs, "already type-checked");
                self.out.push(LowerStmt::Instr(LowerInstr {
                    time,
                    opcode: self.get_opcode(IKind::AssignOp(assign_op.value, ty_var), span, "update assignment with this operation")?,
                    extra_arg: None,
                    user_param_mask: None,
                    args: LowerArgs::Known(vec![lowered_var, lowered_rhs]),
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
            let (tmp_def_id, tmp_as_expr) = self.define_temporary(time, &data_rhs)?;
            self.lower_assign_op(span, time, var, assign_op, &tmp_as_expr)?;
            self.undefine_temporary(tmp_def_id)?;
            return Ok(());
        }

        // complex expressions without a cast
        match (assign_op.value, &data_rhs.tmp_expr.value) {
            // a = <expr> + <expr>;
            (ast::AssignOpKind::Assign, ast::Expr::Binop(a, binop, b)) => {
                self.lower_assign_direct_binop(span, time, var, assign_op, rhs.span, a, binop, b)
            },

            // a = -<expr>;
            // a = sin(<expr>);
            (ast::AssignOpKind::Assign, ast::Expr::Unop(unop, b)) => {
                self.lower_assign_direct_unop(span, time, var, assign_op, rhs.span, unop, b)
            },

            // a = <any other expr>;
            // a += <expr>;
            (_, _) => {
                match assign_op.value {
                    // a = <big expr>
                    // if none of the other branches handled it yet, we can't do it
                    ast::AssignOpKind::Assign => Err(self.unsupported(&rhs.span, "this expression")),

                    // a += <expr>;
                    // split out to: `tmp = <expr>;  a += tmp;`
                    _ => {
                        let (tmp_def_id, tmp_var_expr) = self.define_temporary(time, &data_rhs)?;
                        self.lower_assign_op(span, time, var, assign_op, &tmp_var_expr)?;
                        self.undefine_temporary(tmp_def_id)?;
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
        a: &Sp<ast::Expr>,
        binop: &Sp<ast::BinopKind>,
        b: &Sp<ast::Expr>,
    ) -> Result<(), ErrorReported> {
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
        let simple_a = match classify_expr(a, self.ctx)? {
            ExprClass::NeedsTemp(data_a) => {
                if data_a.tmp_ty == data_a.read_ty && !expr_uses_var(b, var) {
                    // we can reuse the output variable!
                    let var_as_expr = self.compute_temporary_expr(time, var, &data_a)?;
                    self.lower_assign_direct_binop(span, time, var, eq_sign, rhs_span, &var_as_expr, binop, b)?;
                } else {
                    // we need a temporary, either due to the type cast or to avoid invalidating the other subexpression
                    let (tmp_def_id, tmp_as_expr) = self.define_temporary(time, &data_a)?;
                    self.lower_assign_direct_binop(span, time, var, eq_sign, rhs_span, &tmp_as_expr, binop, b)?;
                    self.undefine_temporary(tmp_def_id)?;
                }
                return Ok(());
            },
            ExprClass::Simple(simple) => simple,
        };

        // FIXME: This is somewhat copy-pasta-y.  It's possible to write this and the above into a loop with two
        //        iterations, but the end result looked pretty awkward last time I tried.
        // First guy is simple.  Evaluate the second subexpression if necessary.
        let simple_b = match classify_expr(b, self.ctx)? {
            ExprClass::NeedsTemp(data_b) => {
                // similar conditions apply...
                if data_b.tmp_ty == data_b.read_ty && !expr_uses_var(a, var) {
                    // we can reuse the output variable!
                    let var_as_expr = self.compute_temporary_expr(time, var, &data_b)?;
                    self.lower_assign_direct_binop(span, time, var, eq_sign, rhs_span, a, binop, &var_as_expr)?;
                } else {
                    // we need a temporary, either due to the type cast or to avoid invalidating the other subexpression
                    let (tmp_def_id, tmp_as_expr) = self.define_temporary(time, &data_b)?;
                    self.lower_assign_direct_binop(span, time, var, eq_sign, rhs_span, a, binop, &tmp_as_expr)?;
                    self.undefine_temporary(tmp_def_id)?;
                }
                return Ok(());
            },
            ExprClass::Simple(simple) => simple,
        };

        // They're both simple.  Emit a primitive instruction.
        let (lowered_var, ty_var) = lower_var_to_arg(var, self.ctx)?;
        let ty_rhs = ast::Expr::binop_ty(binop.value, &a.value, self.ctx);
        assert_eq!(ty_var, ty_rhs, "already type-checked");

        self.out.push(LowerStmt::Instr(LowerInstr {
            time,
            opcode: self.get_opcode(IKind::Binop(binop.value, ty_var), span, "this binary operation")?,
            extra_arg: None,
            user_param_mask: None,
            args: LowerArgs::Known(vec![lowered_var, simple_a.lowered, simple_b.lowered]),
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
        b: &Sp<ast::Expr>,
    ) -> Result<(), ErrorReported> {
        // `a = -b;` is not a native instruction.  Just treat it as `a = 0 - b;`
        if unop.value == token![-] {
            let ty = b.compute_ty(self.ctx).as_value_ty().expect("type-checked so not void");
            let zero = sp!(unop.span => ast::Expr::zero(ty));
            let minus = sp!(unop.span => token![-]);
            self.lower_assign_direct_binop(span, time, var, eq_sign, rhs_span, &zero, &minus, b)?;
            return Ok(());
        }

        match classify_expr(b, self.ctx)? {
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
                    let (tmp_def_id, tmp_as_expr) = self.define_temporary(time, &data_b)?;
                    self.lower_assign_direct_unop(span, time, var, eq_sign, rhs_span, unop, &tmp_as_expr)?;
                    self.undefine_temporary(tmp_def_id)?;
                }
                Ok(())
            },

            ExprClass::Simple(data_b) => {
                let (lowered_var, ty_var) = lower_var_to_arg(var, self.ctx)?;
                let ty_rhs = ast::Expr::unop_ty(unop.value, b, self.ctx);
                assert_eq!(ty_var, ty_rhs, "already type-checked");
                let ty = ty_var;

                match unop.value {
                    // These are all handled other ways
                    token![_S] |
                    token![_f] |
                    token![unop -] => unreachable!(),

                    // TODO: we *could* polyfill this with some conditional jumps but bleccccch
                    token![!] => return Err(self.unsupported(&span, "logical not operator")),

                    token![sin] |
                    token![cos] |
                    token![sqrt] => self.out.push(LowerStmt::Instr(LowerInstr {
                        time,
                        opcode: self.get_opcode(IKind::Unop(unop.value, ty), span, "this unary operation")?,
                        extra_arg: None,
                        user_param_mask: None,
                        args: LowerArgs::Known(vec![lowered_var, data_b.lowered]),
                    })),
                }
                Ok(())
            },
        }
    }

    fn lower_uncond_jump(&mut self, stmt_span: Span, stmt_time: i32, goto: &ast::StmtGoto) -> Result<(), ErrorReported> {
        if goto.time.is_some() && !self.instr_format.jump_has_time_arg() {
            return Err(self.unsupported(&stmt_span, "goto @ time"));
        }

        let (label_arg, time_arg) = lower_goto_args(goto);

        self.out.push(LowerStmt::Instr(LowerInstr {
            time: stmt_time,
            opcode: self.get_opcode(IKind::Jmp, stmt_span, "'goto'")?,
            extra_arg: None,
            user_param_mask: None,
            args: LowerArgs::Known(vec![label_arg, time_arg]),
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
    ) -> Result<(), ErrorReported>{
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
    ) -> Result<(), ErrorReported>{
        match keyword.value {
            // 'if (--var) goto label'
            token![if] => {
                let (arg_var, ty_var) = lower_var_to_arg(var, self.ctx)?;
                let (arg_label, arg_time) = lower_goto_args(goto);
                assert_eq!(ty_var, ScalarType::Int, "shoulda been type-checked!");

                self.out.push(LowerStmt::Instr(LowerInstr {
                    time: stmt_time,
                    opcode: self.get_opcode(IKind::CountJmp, stmt_span, "decrement jump")?,
                    extra_arg: None,
                    user_param_mask: None,
                    args: LowerArgs::Known(vec![arg_var, arg_label, arg_time]),
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

                let skip_label = sp!(keyword.span => self.ctx.gensym.gensym("@unless_predec_skip#"));
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
    ) -> Result<(), ErrorReported>{
        match &expr.value {
            // 'if (<A> <= <B>) goto label'
            // 'unless (<A> <= <B>) goto label'
            ast::Expr::Binop(a, binop, b) if binop.is_comparison() => {
                self.lower_cond_jump_comparison(stmt_span, stmt_time, keyword, a, binop, b, goto)
            },

            // 'if (<A> || <B>) goto label'
            // 'unless (<A> || <B>) goto label'
            ast::Expr::Binop(a, binop, b) if matches!(binop.value, token![&&] | token![||]) => {
                self.lower_cond_jump_logic_binop(stmt_span, stmt_time, keyword, a, binop, b, goto)
            },

            // 'if (!<B>) goto label'
            // 'unless (!<B>) goto label'
            ast::Expr::Unop(sp_pat!(op_span => token![!]), b) => {
                let negated_kw = sp!(*op_span => keyword.negate());
                self.lower_cond_jump_expr(stmt_span, stmt_time, &negated_kw, b, goto)
            },

            // other arbitrary expressions: use `<if|unless> (<expr> != 0)`
            _ => {
                let ty = expr.compute_ty(self.ctx).as_value_ty().expect("type-checked so not void");
                assert_eq!(ty, ScalarType::Int);
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
        a: &Sp<ast::Expr>,
        binop: &Sp<ast::BinopKind>,
        b: &Sp<ast::Expr>,
        goto: &ast::StmtGoto,
    ) -> Result<(), ErrorReported>{
        match (classify_expr(a, self.ctx)?, classify_expr(b, self.ctx)?) {
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
                assert_eq!(data_a.ty, data_b.ty, "should've been type-checked");
                let ty_arg = data_a.ty;

                let (lowered_label, lowered_time) = lower_goto_args(goto);
                self.out.push(LowerStmt::Instr(LowerInstr {
                    time: stmt_time,
                    opcode: self.get_opcode(IKind::CondJmp(binop.value, ty_arg), binop.span, "conditional jump with this operator")?,
                    extra_arg: None,
                    user_param_mask: None,
                    args: LowerArgs::Known(vec![data_a.lowered, data_b.lowered, lowered_label, lowered_time]),
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
      a: &Sp<ast::Expr>,
      binop: &Sp<ast::BinopKind>,
      b: &Sp<ast::Expr>,
      goto: &ast::StmtGoto,
  ) -> Result<(), ErrorReported> {
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
            let skip_label = sp!(binop.span => self.ctx.gensym.gensym("@unless_predec_skip#"));
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
    ) -> Result<(DefId, Sp<ast::Expr>), ErrorReported> {
        let (def_id, var) = self.allocate_temporary(data.tmp_expr.span, data.tmp_ty)?;
        let var_as_expr = self.compute_temporary_expr(time, &var, data)?;

        Ok((def_id, var_as_expr))
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
    ) -> Result<Sp<ast::Expr>, ErrorReported> {
        let eq_sign = sp!(data.tmp_expr.span => token![=]);
        self.lower_assign_op(data.tmp_expr.span, time, var, &eq_sign, data.tmp_expr)?;

        let mut read_var = var.clone();
        let read_ty_sigil = get_temporary_read_ty(data.read_ty, var.span).map_err(|e| self.ctx.emitter.emit(e))?;
        read_var.ty_sigil = Some(read_ty_sigil);
        Ok(sp!(var.span => ast::Expr::Var(read_var)))
    }

    /// Emits an intrinsic that cleans up a register-allocated temporary.
    fn undefine_temporary(&mut self, def_id: DefId) -> Result<(), ErrorReported> {
        self.out.push(LowerStmt::RegFree { def_id });
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
    ) -> Result<(DefId, Sp<ast::Var>), ErrorReported> {
        // FIXME: It bothers me that we have to actually allocate an identifier here.
        let ident = self.ctx.gensym.gensym("temp");
        let ident = sp!(span => self.ctx.resolutions.attach_fresh_res(ident));
        let def_id = self.ctx.define_local(ident.clone(), tmp_ty.into());
        let sigil = get_temporary_read_ty(tmp_ty, span).map_err(|e| self.ctx.emitter.emit(e))?;

        let var = sp!(span => ast::Var { ty_sigil: Some(sigil), name: ast::VarName::new_non_reg(ident.value) });
        self.out.push(LowerStmt::RegAlloc { def_id, cause: span });

        Ok((def_id, var))
    }

    fn get_opcode(&self, kind: IntrinsicInstrKind, span: Span, descr: &str) -> Result<u16, ErrorReported> {
        self.intrinsic_instrs.get_opcode(kind, span, descr).map_err(|e| self.ctx.emitter.emit(e))
    }

    fn unsupported(&self, span: &crate::pos::Span, what: &str) -> ErrorReported {
        self.ctx.emitter.emit(super::unsupported(span, what))
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
fn get_temporary_read_ty(ty: ScalarType, span: Span) -> Result<ast::VarSigil, Diagnostic> {
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
    tmp_expr: &'a Sp<ast::Expr>,
    tmp_ty: ScalarType,
    read_ty: ScalarType,
}

fn classify_expr<'a>(arg: &'a Sp<ast::Expr>, ctx: &CompilerContext) -> Result<ExprClass<'a>, ErrorReported> {
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
            let (lowered, ty) = lower_var_to_arg(var, ctx)?;
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
            let ty = arg.compute_ty(ctx).as_value_ty().expect("shouldn't be void");
            TemporaryExpr { tmp_expr: arg, tmp_ty: ty, read_ty: ty }
        })),
    }
}

fn lower_var_to_arg(var: &Sp<ast::Var>, ctx: &CompilerContext) -> Result<(Sp<LowerArg>, ScalarType), ErrorReported> {
    let read_ty = ctx.var_read_ty_from_ast(var).as_known_ty().expect("(bug!) untyped in stackless lowerer");

    // Up to this point in compilation, register aliases use Var::Named.
    // But now, we want both registers and their aliases to be resolved to a register
    let arg = match ctx.var_reg_from_ast(&var.name) {
        Ok((_lang, reg)) => LowerArg::Raw(SimpleArg::from_reg(reg, read_ty)),
        Err(def_id) => LowerArg::Local { def_id, read_ty },
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
    }

    impl Visit for Visitor<'_> {
        fn visit_var(&mut self, var: &Sp<ast::Var>) {
            if self.var.name == var.name {
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
    ctx: &CompilerContext,
) -> Result<(), ErrorReported> {
    let used_regs = get_used_regs(code);

    let mut unused_regs = format.general_use_regs();
    for vec in unused_regs.values_mut() {
        vec.retain(|reg| !used_regs.contains(reg));
        vec.reverse();  // since we'll be popping from these lists
    }

    let mut local_regs = HashMap::<DefId, (RegId, ScalarType, Span)>::new();
    let mut has_used_scratch: Option<Span> = None;
    let mut has_anti_scratch_ins = false;

    for stmt in code {
        match stmt {
            LowerStmt::RegAlloc { def_id, ref cause } => {
                has_used_scratch.get_or_insert(*cause);

                let required_ty = ctx.defs.var_inherent_ty(*def_id).as_known_ty().expect("(bug!) untyped in stackless lowerer");

                let reg = unused_regs[required_ty].pop().ok_or_else(|| {
                    let stringify_reg = |reg| crate::fmt::stringify(&ctx.reg_to_ast(format.language(), reg));

                    let mut error = error!(
                        message("script too complex to compile"),
                        primary(cause, "no more registers of this type!"),
                    );
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

                    ctx.emitter.emit(error)
                })?;

                assert!(local_regs.insert(*def_id, (reg, required_ty, *cause)).is_none());
            },
            LowerStmt::RegFree { def_id } => {
                let inherent_ty = ctx.defs.var_inherent_ty(*def_id).as_known_ty().expect("(bug!) we allocated a reg so it must have a type");
                let (reg, _, _) = local_regs.remove(&def_id).expect("(bug!) RegFree without RegAlloc!");
                unused_regs[inherent_ty].push(reg);
            },
            LowerStmt::Instr(instr) => {
                if format.instr_disables_scratch_regs(instr.opcode) {
                    has_anti_scratch_ins = true;
                }

                if let LowerArgs::Known(args) = &mut instr.args {
                    for arg in args {
                        if let LowerArg::Local { def_id, read_ty } = arg.value {
                            arg.value = LowerArg::Raw(SimpleArg::from_reg(local_regs[&def_id].0, read_ty));
                        }
                    }
                }
            },
            LowerStmt::Label { .. } => {},
        }
    }

    if has_anti_scratch_ins {
        if let Some(span) = has_used_scratch {
            return Err(ctx.emitter.emit(error!(
                message("scratch registers are disabled in this script"),
                primary(span, "this requires a scratch register"),
            )))
        }
    }

    Ok(())
}

// Gather all explicitly-used registers in the source. (so that we can avoid using them for scratch)
fn get_used_regs(func_body: &[LowerStmt]) -> BTreeSet<RegId> {
    func_body.iter()
        .filter_map(|stmt| match stmt {
            LowerStmt::Instr(LowerInstr { args: LowerArgs::Known(args), .. }) => Some(args),
            _ => None
        }).flat_map(|args| args.iter().filter_map(|arg| match &arg.value {
            LowerArg::Raw(arg) => arg.get_reg_id(),
            _ => None,
        })).collect()
}
