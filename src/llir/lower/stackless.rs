//! Lowering for languages without a stack.
//!
//! Responsible for compilation of expressions into instructions that use temporary registers.

use std::collections::{HashMap, BTreeMap};

use crate::raw;
use super::{LowerStmt, LowerInstr, LowerArgs, LowerArg, SimpleArg};
use crate::diagnostic::Diagnostic;
use crate::llir::{LanguageHooks, IntrinsicInstrKind, IntrinsicInstrs, HowBadIsIt, intrinsic::alternatives};
use crate::error::{GatherErrorIteratorExt, ErrorReported};
use crate::pos::{Sp, Span};
use crate::ast::{self, pseudo::PseudoArgData};
use crate::resolve::{DefId, RegId, NodeId, AliasableId, IdMap};
use crate::value::{ScalarType, ReadType};
use crate::context::CompilerContext;
use crate::passes::semantics::time_and_difficulty::TimeAndDifficulty;
use crate::debug_info;
use crate::ecl::ecl_06;

use IntrinsicInstrKind as IKind;

/// Helper responsible for converting an AST into [`LowLevelStmt`]s.
pub (in crate::llir::lower) struct SingleSubLowerer<'a, 'ctx> {
    pub out: Vec<Sp<LowerStmt>>,
    pub intrinsic_instrs: IntrinsicInstrs,
    pub hooks: &'a dyn LanguageHooks,
    pub ctx: &'a mut CompilerContext<'ctx>,
    pub stmt_data: IdMap<NodeId, TimeAndDifficulty>,
    pub sub_info: Option<&'a super::SubInfo<'a>>,
}

impl SingleSubLowerer<'_, '_> {
    pub fn lower_sub_ast(
        &mut self,
        code: &[Sp<ast::Stmt>],
    ) -> Result<(), ErrorReported> {
        let mut th06_anm_end_span = None;
        code.iter().map(|stmt| {
            if let Some(end) = th06_anm_end_span {
                if !matches!(&stmt.kind, ast::StmtKind::NoInstruction) { return Err(self.ctx.emitter.emit(error!(
                    message("statement after end of script"),
                    primary(&stmt, "forbidden statement"),
                    secondary(&end, "marks the end of the script"),
                    note("In EoSD ANM, every script must have a single exit point (opcode 0 or 15), as the final instruction."),
                )))}
            }

            let stmt_data = self.stmt_data[&stmt.node_id.expect("stmt_data would've failed if missing")];

            match &stmt.kind {
                ast::StmtKind::Jump(jump) => {
                    let goto = self.expect_simple_goto(jump)?;
                    self.lower_uncond_jump(stmt.span, stmt_data, goto)?;
                },


                ast::StmtKind::Assignment { var, op, value } => {
                    self.lower_assign_op(stmt.span, stmt_data, var, op, value)?;
                },


                ast::StmtKind::InterruptLabel(interrupt_id_expr) => {
                    let interrupt_id = interrupt_id_expr.as_const_int().ok_or_else(|| {
                        // FIXME: can't we unify this with other non-const errors and make this a panic?
                        self.ctx.emitter.emit(error!(
                            message("const evaluation error in interrupt label"),
                            primary(interrupt_id_expr, "non-const expression"),
                        ))
                    })?;
                    self.lower_intrinsic(stmt.span, stmt_data, IKind::InterruptLabel, "interrupt label", |bld| {
                        let lowered_id = sp!(interrupt_id_expr.span => LowerArg::Raw(interrupt_id.into()));
                        bld.plain_args.push(lowered_id);
                    })?;
                },


                ast::StmtKind::CondJump { keyword, cond, jump } => {
                    let goto = self.expect_simple_goto(jump)?;
                    self.lower_cond_jump(stmt.span, stmt_data, keyword, cond, goto)?;
                },


                ast::StmtKind::Declaration { ty_keyword, vars } => {
                    self.lower_var_declaration(stmt.span, stmt_data, ty_keyword, vars)?;
                },


                ast::StmtKind::Expr(expr) => match &expr.value {
                    ast::Expr::Call(call) => self.lower_call_stmt(&mut th06_anm_end_span, expr.span, stmt_data, call)?,
                    _ => return Err(self.unsupported(expr.span, &format!("{} in {}", expr.descr(), stmt.kind.descr()))),
                }, // match expr

                ast::StmtKind::Label(ident) => {
                    self.out.push(sp!(stmt.span => LowerStmt::Label { time: stmt_data.time, label: ident.clone() }));
                },

                &ast::StmtKind::ScopeEnd(def_id) => {
                    self.out.push(sp!(stmt.span => LowerStmt::RegFree { def_id }));
                },

                ast::StmtKind::NoInstruction => {},

                // handled by semantics pass
                ast::StmtKind::AbsTimeLabel { .. } => {},
                ast::StmtKind::RelTimeLabel { .. } => {},
                ast::StmtKind::Item { .. } => {},

                _ => return Err(self.unsupported(stmt.span, stmt.kind.descr())),
            }
            Ok(())
        }).collect_with_recovery()
    }

    // ------------------
    // Methods for lowering specific types of statement bodies.

    /// Lowers `func(<ARG1>, <ARG2>, <...>);`
    fn lower_call_stmt<'a>(
        &mut self,
        th06_anm_end_span: &mut Option<Span>,
        stmt_span: Span,
        stmt_data: TimeAndDifficulty,
        call: &ast::ExprCall,
    ) -> Result<(), ErrorReported> {
        match self.ctx.func_opcode_from_ast(&call.name) {
            Ok((lang, opcode)) => {
                // single instruction
                assert_eq!(lang, self.hooks.language());
                self.lower_instruction(stmt_span, stmt_data, opcode as _, call)?;

                if self.hooks.is_th06_anm_terminating_instr(opcode) {
                    *th06_anm_end_span = Some(call.name.span);
                }
                Ok(())
            },

            Err(def_id) => {
                // exported sub
                let sub_info = self.sub_info.unwrap();
                match self.ctx.defs.user_func_qualifier(def_id).expect("isn't user func?") {
                    Some(sp_pat!(token![inline])) => Err(self.unsupported(stmt_span, "call to inline func")),
                    Some(sp_pat!(token![const])) => panic!("leftover const func call during lowering"),
                    None => match sub_info.call_reg_info.as_ref() {
                        None => {
                            self.lower_eosd_call(stmt_span, stmt_data, call, &sub_info.exported_subs.subs[&def_id])
                        },
                        Some(call_reg_info) => {
                            self.lower_reg_call(stmt_span, stmt_data, call, &sub_info.exported_subs.subs[&def_id], call_reg_info)
                        },
                    },
                }
            },
        }
    }

    fn lower_eosd_call(
        &mut self,
        stmt_span: Span,
        stmt_data: TimeAndDifficulty,
        call: &ast::ExprCall,
        sub: &ecl_06::OldeExportedSub,
    ) -> Result<(), ErrorReported> {
        let int = {
            sub.params_by_ty[ReadType::Int].get(0)
                .map(|&(index, _)| call.args[index].clone())
                .unwrap_or(sp!((0).into()))
        };
        let float = {
            sub.params_by_ty[ReadType::Float].get(0)
                .map(|&(index, _)| call.args[index].clone())
                .unwrap_or(sp!((0.0).into()))
        };

        // EoSD args must be const
        let lowered_int = self.classify_expr(&int)?.expect_simple().lowered.clone();
        let lowered_float = self.classify_expr(&float)?.expect_simple().lowered.clone();
        let lowered_sub_id = sp!(call.name.span => LowerArg::Raw(sub.index.into()));

        self.lower_intrinsic(
            stmt_span, stmt_data, IKind::CallEosd, "sub call",
            |bld| {
                bld.sub_id = Some(lowered_sub_id);
                bld.plain_args.push(lowered_int);
                bld.plain_args.push(lowered_float);
            },
        )
    }

    fn lower_reg_call(
        &mut self,
        stmt_span: Span,
        stmt_data: TimeAndDifficulty,
        call: &ast::ExprCall,
        sub: &ecl_06::OldeExportedSub,
        call_reg_info: &ecl_06::CallRegInfo,
    ) -> Result<(), ErrorReported> {
        // Each argument gets assigned to a special "arg register."
        let mut arg_regs_iter_by_ty = enum_map::enum_map!{
            ty => call_reg_info.arg_regs_by_type[ty].iter().copied()
        };
        for (param_index, &(_, ty, _)) in sub.params_in_sig.iter().enumerate() {
            let arg_reg = arg_regs_iter_by_ty[ty].next().unwrap();
            let arg_expr = &call.args[param_index];
            let arg_var = self.reg_to_var(sp!(arg_expr.span => arg_reg), ty);
            let eq_sign = sp!(arg_expr.span => token![=]);
            self.lower_assign_op(arg_expr.span, stmt_data, &arg_var, &eq_sign, arg_expr)?;
        }

        let lowered_sub_id = sp!(call.name.span => LowerArg::Raw(sub.index.into()));
        self.lower_intrinsic(
            stmt_span, stmt_data, IKind::CallReg, "sub call",
            |bld| {
                bld.sub_id = Some(lowered_sub_id);
            },
        )
    }

    /// Lowers `func(<ARG1>, <ARG2>, <...>);` where `func` is an instruction alias.
    fn lower_instruction(
        &mut self,
        stmt_span: Span,
        stmt_data: TimeAndDifficulty,
        opcode: raw::Opcode,
        call: &ast::ExprCall,
    ) -> Result<raw::Opcode, ErrorReported> {
        let ast::ExprCall { pseudos, args, .. } = call;
        let PseudoArgData {
            // fully unpack because we need to add errors for anything unsupported
            pop: pseudo_pop, blob: pseudo_blob, param_mask: pseudo_param_mask,
            extra_arg: pseudo_extra_arg, arg_count: pseudo_arg_count,
        } = PseudoArgData::from_pseudos(pseudos).map_err(|e| self.ctx.emitter.emit(e))?;

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
                    let lowered = match self.classify_expr(expr)? {
                        ExprClass::Simple(data) => data.lowered,
                        ExprClass::NeedsElaboration(data) => {
                            // Save this expression to a temporary
                            let (def_id, _) = self.define_temporary(stmt_data, &data)?;
                            let lowered = sp!(expr.span => LowerArg::Local { def_id, storage_ty: data.read_ty });

                            temp_def_ids.push((expr.span.end_span(), def_id)); // so we can free the register later
                            lowered
                        },
                    };
                    Ok::<_, ErrorReported>(lowered)
                }).collect_with_recovery()?)
            },
        };

        self.out.push(sp!(stmt_span => LowerStmt::Instr(LowerInstr {
            stmt_data,
            opcode: opcode as _,
            user_param_mask: pseudo_param_mask.map(|x| x.value),
            explicit_extra_arg: pseudo_extra_arg.map(|x| x.value),
            user_pop: pseudo_pop.map(|x| x.value),
            user_arg_count: pseudo_arg_count.map(|x| x.value),
            args: low_level_args,
        })));

        for (span, id) in temp_def_ids.into_iter().rev() {
            self.undefine_temporary(span, id)?;
        }

        Ok(opcode)
    }

    /// Lowers `int x, y = 3, z;`
    fn lower_var_declaration(
        &mut self,
        _stmt_span: Span,
        stmt_data: TimeAndDifficulty,
        keyword: &Sp<ast::TypeKeyword>,
        vars: &[Sp<(Sp<ast::Var>, Option<Sp<ast::Expr>>)>],
    ) -> Result<(), ErrorReported>{
        if keyword.value == token![var] {
            return Err(self.unsupported(keyword.span, "untyped variables"));
        }

        for pair in vars {
            let (var, expr) = &pair.value;
            let ident = var.name.expect_ident();
            let def_id = self.ctx.resolutions.expect_def(ident);
            self.out.push(sp!(var.span => LowerStmt::RegAlloc { def_id }));

            if let Some(expr) = expr {
                let assign_op = sp!(pair.span => token![=]);
                self.lower_assign_op(pair.span, stmt_data, var, &assign_op, expr)?;
            }
        }
        Ok(())
    }

    /// Lowers `a = <B>;`  or  `a *= <B>;`
    fn lower_assign_op(
        &mut self,
        span: Span,
        stmt_data: TimeAndDifficulty,
        var: &Sp<ast::Var>,
        assign_op: &Sp<ast::AssignOpKind>,
        rhs: &Sp<ast::Expr>,
    ) -> Result<(), ErrorReported> {
        let data_rhs = match self.classify_expr(rhs)? {
            // a = <atom>;
            // a += <atom>;
            ExprClass::Simple(simple_rhs) => {
                return self.lower_assign_op_intrinsic(span, stmt_data, var, assign_op, simple_rhs);
            },
            ExprClass::NeedsElaboration(data) => data,
        };

        // a = %(<expr>);
        // a *= %(<expr>);
        // TODO: should this be data_rhs.tmp_ty != var_ty or similar to catch EoSD ECL casts?
        //       (I tried to trigger a bug with this but was unable)
        if data_rhs.read_ty != data_rhs.tmp_ty {
            // Regardless of what the expression contains, assign it to a temporary.
            // (i.e.:    `float tmp = <expr>;  a = $tmp;`
            let (tmp_def_id, tmp_as_expr) = self.define_temporary(stmt_data, &data_rhs)?;
            self.lower_assign_op(span, stmt_data, var, assign_op, &tmp_as_expr)?;
            self.undefine_temporary(span.end_span(), tmp_def_id)?;
            return Ok(());
        }

        // complex expressions without a cast
        match (assign_op.value, &data_rhs.tmp_expr.value) {
            // a = <expr> + <expr>;
            (ast::AssignOpKind::Assign, ast::Expr::BinOp(a, binop, b)) => {
                self.lower_assign_direct_binop(span, stmt_data, var, assign_op, rhs.span, a, binop, b)
            },

            // a = -<expr>;
            // a = sin(<expr>);
            (ast::AssignOpKind::Assign, ast::Expr::UnOp(unop, b)) => {
                self.lower_assign_direct_unop(span, stmt_data, var, assign_op, rhs.span, unop, b)
            },

            // a = <expr>:<expr>:<expr>:<expr>;
            (ast::AssignOpKind::Assign, ast::Expr::DiffSwitch(cases)) => {
                self.lower_assign_diff_switch(span, stmt_data, &data_rhs.tmp_expr, var, assign_op, cases)
            },

            // a = <expr> + <expr>;
            (ast::AssignOpKind::Assign, ast::Expr::Ternary { cond, left, right, question, colon, .. }) => {
                self.lower_assign_direct_ternary(span, stmt_data, var, assign_op, cond, question, left, colon, right)
            },

            // a = <any other expr>;
            // a += <expr>;
            (_, _) => {
                match assign_op.value {
                    // a = <big expr>;
                    // if none of the other branches handled it yet, we can't do it
                    ast::AssignOpKind::Assign => Err(self.unsupported(rhs.span, "this expression")),

                    // a += <expr>;
                    // split out to: `tmp = <expr>;  a += tmp;`
                    _ => {
                        let (tmp_def_id, tmp_var_expr) = self.define_temporary(stmt_data, &data_rhs)?;
                        self.lower_assign_op(span, stmt_data, var, assign_op, &tmp_var_expr)?;
                        self.undefine_temporary(span.end_span(), tmp_def_id)?;
                        Ok(())
                    },
                }
            },
        }
    }

    /// Lowers `a = <atom>;`  or  `a *= <atom>;`
    fn lower_assign_op_intrinsic(
        &mut self,
        span: Span,
        stmt_data: TimeAndDifficulty,
        var: &Sp<ast::Var>,
        assign_op: &Sp<ast::AssignOpKind>,
        rhs: SimpleExpr,
    ) -> Result<(), ErrorReported> {
        let SimpleExpr { lowered: lowered_rhs, ty: ty_rhs } = rhs;
        let (lowered_var, ty_var) = lower_var_to_arg(var, self.ctx)?;
        assert_eq!(ty_var, ty_rhs, "already type-checked");

        match self.intrinsic_instrs.alternatives().assign_ops.get(&(assign_op.value, ty_var)) {
            None => return Err(self.unsupported(span, "update assignment with this operation")),

            Some(&alternatives::AssignOp::Intrinsic { opcode }) => {
                self.lower_intrinsic_by_opcode(span, stmt_data, opcode, |bld| {
                    bld.outputs.push(lowered_var);
                    bld.plain_args.push(lowered_rhs);
                })?;
            },

            Some(&alternatives::AssignOp::ViaBinOp { opcode }) => {
                self.lower_intrinsic_by_opcode(span, stmt_data, opcode, |bld| {
                    bld.outputs.push(lowered_var.clone());
                    bld.plain_args.push(lowered_var);
                    bld.plain_args.push(lowered_rhs);
                })?;
            },
        }

        Ok(())
    }

    // NOTE:  It feels silly that this needs to exist in lowering code, but there's no avoiding it.
    //        We can't just change all the ast::Var usage to SimpleExpr because it can't accomodate
    //        temporaries, and `ast::Var` is useful anyways by allowing things like `expr_uses_var`.
    fn reg_to_var(&self, reg: Sp<RegId>, ty: ReadType) -> Sp<ast::Var> {
        sp!(reg.span => ast::Var {
            ty_sigil: Some(ty),
            name: ast::VarName::Reg {
                reg: reg.value,
                language: Some(self.hooks.language()),
            },
        })
    }

    /// Lowers `x = 2:a+4:6:7;`
    fn lower_assign_diff_switch(
        &mut self,
        stmt_span: Span,
        stmt_data: TimeAndDifficulty,
        whole_expr: &Sp<ast::Expr>,
        var: &Sp<ast::Var>,
        eq_sign: &Sp<ast::AssignOpKind>,
        cases: &[Option<Sp<ast::Expr>>],
    ) -> Result<(), ErrorReported>{
        // It should be impossible to get here for a simple expression, I think?
        // Those would've hit an ExprClass::Simple case in another method first...
        match self.classify_expr(whole_expr)? {
            ExprClass::Simple(SimpleExpr { .. }) => {
                self.ctx.emitter.emit(bug!(
                    message("unhandled simple diff switch"),
                    note("I didn't think this was possible. You get a cookie!"),
                )).ignore();
            },
            ExprClass::NeedsElaboration(TemporaryExpr { .. }) => {},
        }

        // This doesn't actually need a temporary.
        // We can just elaborate it into separate assignment statements on each difficulty.
        let instr_full_mask = stmt_data.difficulty_mask;
        let instr_diff_mask = instr_full_mask & self.ctx.diff_flag_defs.difficulty_bits();
        let instr_aux_mask = instr_full_mask & self.ctx.diff_flag_defs.aux_bits();
        for (case_mask, case) in crate::diff_switch_utils::explicit_difficulty_cases(cases) {
            let new_mask = instr_diff_mask & case_mask | instr_aux_mask;
            if !new_mask.is_empty() {
                let modified_stmt_data = TimeAndDifficulty { difficulty_mask: new_mask, ..stmt_data };
                self.lower_assign_op(stmt_span, modified_stmt_data, var, &eq_sign, case)?;
            }
        }
        Ok(())
    }

    /// Lowers `a = <B> * <C>;`
    fn lower_assign_direct_binop(
        &mut self,
        span: Span,
        stmt_data: TimeAndDifficulty,
        var: &Sp<ast::Var>,
        eq_sign: &Sp<ast::AssignOpKind>,
        rhs_span: Span,
        a: &Sp<ast::Expr>,
        binop: &Sp<ast::BinOpKind>,
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

        let ty_rhs = ast::Expr::binop_ty(binop.value, &a.value, self.ctx);

        // Evaluate the first subexpression if necessary.
        let simple_a = match self.classify_expr(a)? {
            ExprClass::NeedsElaboration(data_a) => {
                // FIXME: I'm not sure that the tmp_ty == read_ty condition (which forbids casts) is necessary and it
                //        even prevents some legitimate cases of reuse like reusing `A` in `A = %(I0 + 1) < 1.5`;
                //        But I'm not 100% sure and I'd rather just wait until we can replace of all of this
                //        "variable reuse" logic with SSA-based analysis.
                if data_a.tmp_ty == ty_rhs && data_a.tmp_ty == data_a.read_ty && !expr_uses_var(b, var, self.ctx) {
                    // we can reuse the output variable!
                    let var_as_expr = self.compute_temporary_expr(stmt_data, var, &data_a)?;
                    self.lower_assign_direct_binop(span, stmt_data, var, eq_sign, rhs_span, &var_as_expr, binop, b)?;
                } else {
                    // we need a temporary, either due to the type cast or to avoid invalidating the other subexpression
                    let (tmp_def_id, tmp_as_expr) = self.define_temporary(stmt_data, &data_a)?;
                    self.lower_assign_direct_binop(span, stmt_data, var, eq_sign, rhs_span, &tmp_as_expr, binop, b)?;
                    self.undefine_temporary(span.end_span(), tmp_def_id)?;
                }
                return Ok(());
            },
            ExprClass::Simple(simple) => simple,
        };

        // FIXME: This is somewhat copy-pasta-y.  It's possible to write this and the above into a loop with two
        //        iterations, but the end result looked pretty awkward last time I tried.
        // First was simple.  Evaluate the second subexpression if necessary.
        let simple_b = match self.classify_expr(b)? {
            ExprClass::NeedsElaboration(data_b) => {
                // similar conditions apply...
                if data_b.tmp_ty == ty_rhs && data_b.tmp_ty == data_b.read_ty && !expr_uses_var(a, var, self.ctx) {
                    // we can reuse the output variable!
                    let var_as_expr = self.compute_temporary_expr(stmt_data, var, &data_b)?;
                    self.lower_assign_direct_binop(span, stmt_data, var, eq_sign, rhs_span, a, binop, &var_as_expr)?;
                } else {
                    // we need a temporary, either due to the type cast or to avoid invalidating the other subexpression
                    let (tmp_def_id, tmp_as_expr) = self.define_temporary(stmt_data, &data_b)?;
                    self.lower_assign_direct_binop(span, stmt_data, var, eq_sign, rhs_span, a, binop, &tmp_as_expr)?;
                    self.undefine_temporary(span.end_span(), tmp_def_id)?;
                }
                return Ok(());
            },
            ExprClass::Simple(simple) => simple,
        };

        // They're both simple.  Emit a primitive instruction.
        let (lowered_var, ty_var) = lower_var_to_arg(var, self.ctx)?;
        assert_eq!(ty_var, ty_rhs, "already type-checked");

        self.lower_intrinsic(rhs_span, stmt_data, IKind::BinOp(binop.value, simple_a.ty), "this binary operation", |bld| {
            bld.outputs.push(lowered_var);
            bld.plain_args.push(simple_a.lowered);
            bld.plain_args.push(simple_b.lowered);
        })
    }

    /// Lowers `a = -<B>;`
    fn lower_assign_direct_unop(
        &mut self,
        span: Span,
        stmt_data: TimeAndDifficulty,
        var: &Sp<ast::Var>,
        eq_sign: &Sp<ast::AssignOpKind>,
        rhs_span: Span,
        unop: &Sp<ast::UnOpKind>,
        b: &Sp<ast::Expr>,
    ) -> Result<(), ErrorReported> {
        let ty_rhs = ast::Expr::unop_ty(unop.value, b, self.ctx);

        match self.classify_expr(b)? {
            ExprClass::NeedsElaboration(data_b) => {
                // Unary operations can reuse their destination register as long as it's the same type.

                // FIXME: I'm not sure that the tmp_ty == read_ty condition is necessary.
                //        But I'd rather just wait until we can replace of all of this
                //        "variable reuse" logic with SSA-based analysis.
                if data_b.tmp_ty == ty_rhs && data_b.tmp_ty == data_b.read_ty {
                    // compile to:   a = <B>;
                    //               a = sin(a);
                    let var_as_expr = self.compute_temporary_expr(stmt_data, var, &data_b)?;
                    self.lower_assign_direct_unop(span, stmt_data, var, eq_sign, rhs_span, unop, &var_as_expr)?;
                } else {
                    // compile to:   temp = <B>;
                    //               a = sin(temp);
                    let (tmp_def_id, tmp_as_expr) = self.define_temporary(stmt_data, &data_b)?;
                    self.lower_assign_direct_unop(span, stmt_data, var, eq_sign, rhs_span, unop, &tmp_as_expr)?;
                    self.undefine_temporary(span.end_span(), tmp_def_id)?;
                }
                Ok(())
            },

            ExprClass::Simple(data_b) => {
                let (lowered_var, ty_var) = lower_var_to_arg(var, self.ctx)?;
                assert_eq!(ty_var, ty_rhs, "already type-checked");

                self.lower_assign_direct_unop_intrinsic(span, stmt_data, lowered_var, rhs_span, unop, data_b)
            },
        }
    }

    /// Lowers `a = -<atom>;`
    fn lower_assign_direct_unop_intrinsic(
        &mut self,
        span: Span,
        stmt_data: TimeAndDifficulty,
        lowered_var: Sp<LowerArg>,
        rhs_span: Span,
        unop: &Sp<ast::UnOpKind>,
        b: SimpleExpr,
    ) -> Result<(), ErrorReported> {
        match self.intrinsic_instrs.alternatives().unops.get(&(unop.value, b.ty)) {
            None => return Err(self.unsupported(rhs_span, "this unary operation")),

            Some(&alternatives::UnOp::Intrinsic { opcode }) => {
                self.lower_intrinsic_by_opcode(span, stmt_data, opcode, |bld| {
                    bld.outputs.push(lowered_var);
                    bld.plain_args.push(b.lowered);
                })?;
            },

            Some(&alternatives::UnOp::ViaConstBinOp { ref a, opcode }) => {
                let lowered_a = sp!(span => a.clone().into());
                self.lower_intrinsic_by_opcode(span, stmt_data, opcode, |bld| {
                    bld.outputs.push(lowered_var);
                    bld.plain_args.push(lowered_a);
                    bld.plain_args.push(b.lowered);
                })?;
            },
        }

        Ok(())
    }

    /// Lowers `a = <C> ? <A> : <B>;`
    fn lower_assign_direct_ternary(
        &mut self,
        span: Span,
        stmt_data: TimeAndDifficulty,
        var: &Sp<ast::Var>,
        eq_sign: &Sp<ast::AssignOpKind>,
        cond: &Sp<ast::Expr>,
        question: &Sp<()>,
        left: &Sp<ast::Expr>,
        colon: &Sp<()>,
        right: &Sp<ast::Expr>,
    ) -> Result<(), ErrorReported> {
        // TODO: Add cond_clobber to 'lower_cond_jump_*' functions so that we can do the register optimization.
        // // Evaluate the first subexpression if necessary.
        // let mut cond_tmp_def_id = None;
        // let cond_lowered;
        // match self.classify_expr(cond)? {
        //     ExprClass::NeedsElaboration(data_cond) => {
        //         let cond_var = if data_cond.tmp_ty == data_cond.read_ty && !expr_uses_var(left, var, self.ctx) && !expr_uses_var(right, var, self.ctx) {
        //             // we can reuse the output variable for the condition!
        //             var.clone()
        //         } else {
        //             // we need a temporary, either due to the type cast or to avoid invalidating the subexpressions
        //             let (tmp_def_id, tmp_as_var) = self.allocate_temporary(data_cond.tmp_expr.span, data_cond.tmp_ty)?;
        //             cond_tmp_def_id = Some(tmp_def_id);  // save to be undefined later
        //             tmp_as_var
        //         };
        //         self.compute_temporary_expr(stmt_data, &cond_var, &data_cond)?;
        //         let (var_lowered, var_read_ty) = lower_var_to_arg(var, self.ctx)?;
        //         assert_eq!(var_read_ty, data_cond.read_ty);
        //         cond_lowered = var_lowered;
        //     },
        //     ExprClass::Simple(simple) => {
        //         cond_lowered = simple.lowered;
        //     },
        // };

        // compile to:
        //
        //        unless (<cond>) goto false_case:
        //        var = <true_case>;
        //        goto end;
        //     false_case:
        //        var = <false_case>;
        //     end:

        let false_label = sp!(colon.span.end_span() => self.ctx.gensym.gensym("@ternary_false#"));
        let end_label = sp!(span.end_span() => self.ctx.gensym.gensym("@ternary_end#"));
        let unless_keyword = sp!(question.span => token![unless]);
        let false_goto = ast::StmtGoto { time: None, destination: false_label.clone() };
        let end_goto = ast::StmtGoto { time: None, destination: end_label.clone() };

        self.lower_cond_jump(question.span, stmt_data, &unless_keyword, cond, &false_goto)?;
        self.lower_assign_op(span, stmt_data, var, eq_sign, left)?;
        self.lower_uncond_jump(colon.span, stmt_data, &end_goto)?;
        self.out.push(sp!(false_label.span => LowerStmt::Label { time: stmt_data.time, label: false_label }));
        self.lower_assign_op(span, stmt_data, var, eq_sign, right)?;
        self.out.push(sp!(end_label.span => LowerStmt::Label { time: stmt_data.time, label: end_label }));
        Ok(())
    }

    fn lower_uncond_jump(&mut self, stmt_span: Span, stmt_data: TimeAndDifficulty, goto: &ast::StmtGoto) -> Result<(), ErrorReported> {
        self.lower_intrinsic(stmt_span, stmt_data, IKind::Jmp, "'goto'", |bld| {
            bld.jump = Some(goto);
        })
    }

    /// Lowers `if (<cond>) goto label @ time;`
    fn lower_cond_jump(
        &mut self,
        stmt_span: Span,
        stmt_data: TimeAndDifficulty,
        keyword: &Sp<ast::CondKeyword>,
        cond: &Sp<ast::Expr>,
        goto: &ast::StmtGoto,
    ) -> Result<(), ErrorReported>{
        if let Some((var, kind)) = alternatives::CountJmpKind::of_cond(cond) {
            self.lower_count_jump_or_bust(stmt_span, stmt_data, keyword, var, kind, goto)
        } else {
            self.lower_cond_jump_non_count(stmt_span, stmt_data, keyword, cond, goto)
        }
    }

    fn lower_count_jump_or_bust(
        &mut self,
        stmt_span: Span,
        stmt_data: TimeAndDifficulty,
        keyword: &Sp<ast::CondKeyword>,
        var: &Sp<ast::Var>,
        count_jmp_kind: alternatives::CountJmpKind,
        goto: &ast::StmtGoto,
    ) -> Result<(), ErrorReported>{
        let alternatives = self.intrinsic_instrs.alternatives();
        match alternatives.count_jmps.get(&count_jmp_kind) {
            None => {
                let mut diag = self.intrinsic_instrs.missing_intrinsic_error(stmt_span, "decrement jump of this form");
                if let Some(existing_kind) = alternatives.preferred_count_jmp {
                    let suggestion = existing_kind.render_suggestion(var);
                    diag.note(format!("this language supports a different form of decrement jump; try '{keyword} ({suggestion})'"));
                }
                return Err(self.ctx.emitter.emit(diag));
            },
            Some(&alternatives::CountJmp::Intrinsic { opcode }) => {
                self.lower_count_jump_intrinsic(stmt_span, stmt_data, keyword, var, opcode, goto)
            }
        }
    }

    fn lower_count_jump_intrinsic(
        &mut self,
        stmt_span: Span,
        stmt_data: TimeAndDifficulty,
        keyword: &Sp<ast::CondKeyword>,
        var: &Sp<ast::Var>,
        opcode: raw::Opcode,
        goto: &ast::StmtGoto,
    ) -> Result<(), ErrorReported>{
        match keyword.value {
            // 'if (--var) goto label'
            token![if] => {
                let (lowered_var, ty_var) = lower_var_to_arg(var, self.ctx)?;
                assert_eq!(ty_var, ScalarType::Int, "shoulda been type-checked!");

                self.lower_intrinsic_by_opcode(stmt_span, stmt_data, opcode, |bld| {
                    bld.jump = Some(goto);
                    bld.outputs.push(lowered_var);
                })
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

                self.lower_count_jump_intrinsic(stmt_span, stmt_data, &if_keyword, var, opcode, &if_goto)?;
                self.lower_uncond_jump(stmt_span, stmt_data, goto)?;
                self.out.push(sp!(stmt_span => LowerStmt::Label { time: stmt_data.time, label: skip_label }));
                Ok(())
            },
        }
    }

    /// Lower any conditional jump that doesn't get lowered to a CountJmp.
    fn lower_cond_jump_non_count(
        &mut self,
        stmt_span: Span,
        stmt_data: TimeAndDifficulty,
        keyword: &Sp<ast::CondKeyword>,
        expr: &Sp<ast::Expr>,
        goto: &ast::StmtGoto,
    ) -> Result<(), ErrorReported>{
        match &expr.value {
            // 'if (<A> <= <B>) goto label'
            // 'unless (<A> <= <B>) goto label'
            ast::Expr::BinOp(a, binop, b) if binop.is_comparison() => {
                self.lower_cond_jump_comparison(stmt_span, stmt_data, keyword, a, binop, b, goto)
            },

            // 'if (<A> || <B>) goto label'
            // 'unless (<A> || <B>) goto label'
            ast::Expr::BinOp(a, binop, b) if matches!(binop.value, token![&&] | token![||]) => {
                self.lower_cond_jump_logic_binop(stmt_span, stmt_data, keyword, a, binop, b, goto)
            },

            // 'if (!<B>) goto label'
            // 'unless (!<B>) goto label'
            ast::Expr::UnOp(sp_pat!(op_span => token![!]), b) => {
                let negated_kw = sp!(*op_span => keyword.negate());
                self.lower_cond_jump_non_count(stmt_span, stmt_data, &negated_kw, b, goto)
            },

            // other arbitrary expressions: use `<if|unless> (<expr> != 0)`
            _ => {
                let ty = expr.compute_ty(self.ctx).as_value_ty().expect("type-checked so not void");
                assert_eq!(ty, ScalarType::Int);
                let zero = sp!(expr.span => ast::Expr::int_of_ty(0, ty));
                let ne_sign = sp!(expr.span => token![!=]);
                self.lower_cond_jump_comparison(stmt_span, stmt_data, keyword, expr, &ne_sign, &zero, goto)
            },
        }
    }

    /// Lowers `if (<A> != <B>) goto label @ time;` and similar
    fn lower_cond_jump_comparison(
        &mut self,
        stmt_span: Span,
        stmt_data: TimeAndDifficulty,
        keyword: &Sp<ast::CondKeyword>,
        a: &Sp<ast::Expr>,
        binop: &Sp<ast::BinOpKind>,
        b: &Sp<ast::Expr>,
        goto: &ast::StmtGoto,
    ) -> Result<(), ErrorReported>{
        match (self.classify_expr(a)?, self.classify_expr(b)?) {
            // `if (<A> != <B>) ...` (or `unless (<A> != <B>) ...`)
            // split out to: `tmp = <A>;  if (tmp != <B>) ...`;
            (ExprClass::NeedsElaboration(data_a), _) => {
                let (id, var_expr) = self.define_temporary(stmt_data, &data_a)?;
                self.lower_cond_jump_comparison(stmt_span, stmt_data, keyword, &var_expr, binop, b, goto)?;
                self.undefine_temporary(stmt_span.end_span(), id)?;
            },

            // `if (a != <B>) ...` (or `unless (a != <B>) ...`)
            // split out to: `tmp = <B>;  if (a != tmp) ...`;
            (ExprClass::Simple(_), ExprClass::NeedsElaboration(data_b)) => {
                let (id, var_expr) = self.define_temporary(stmt_data, &data_b)?;
                self.lower_cond_jump_comparison(stmt_span, stmt_data, keyword, a, binop, &var_expr, goto)?;
                self.undefine_temporary(stmt_span.end_span(), id)?;
            },

            // `if (a != b) ...` (or `unless (a != b) ...`)
            (ExprClass::Simple(data_a), ExprClass::Simple(data_b)) => {
                let binop = sp!(binop.span => match keyword.value {
                    token![if] => binop.value,
                    token![unless] => binop.negate_comparison().expect("lower_cond_jump_comparison called with non-comparison operator"),
                });
                self.lower_cond_jump_intrinsic(stmt_span, stmt_data, data_a, &binop, data_b, goto)?;
            },
        }
        Ok(())
    }

    /// Lowers `if (<atom> != <atom>) goto label @ time;` and similar
    fn lower_cond_jump_intrinsic(
        &mut self,
        stmt_span: Span,
        stmt_data: TimeAndDifficulty,
        data_a: SimpleExpr,
        binop: &Sp<ast::BinOpKind>,
        data_b: SimpleExpr,
        goto: &ast::StmtGoto,
    ) -> Result<(), ErrorReported> {
        assert_eq!(data_a.ty, data_b.ty, "should've been type-checked");
        let ty_arg = data_a.ty;

        match self.intrinsic_instrs.alternatives().cond_jmps.get(&(binop.value, ty_arg)) {
            None => return Err(self.unsupported(stmt_span, "this conditional jump")),

            Some(&alternatives::CondJmp::Intrinsic { opcode }) => {
                self.lower_intrinsic_by_opcode(stmt_span, stmt_data, opcode, |bld| {
                    bld.plain_args.push(data_a.lowered);
                    bld.plain_args.push(data_b.lowered);
                    bld.jump = Some(goto);
                })?;
            },

            Some(&alternatives::CondJmp::TwoPart { cmp_opcode, jmp_opcode }) => {
                self.lower_intrinsic_by_opcode(stmt_span, stmt_data, cmp_opcode, |bld| {
                    bld.plain_args.push(data_a.lowered);
                    bld.plain_args.push(data_b.lowered);
                })?;
                self.lower_intrinsic_by_opcode(stmt_span, stmt_data, jmp_opcode, |bld| {
                    bld.jump = Some(goto);
                })?;
            },
        }

        Ok(())
    }

    /// Lowers `if (<A> || <B>) goto label @ time;` and similar
    fn lower_cond_jump_logic_binop(
        &mut self,
        stmt_span: Span,
        stmt_data: TimeAndDifficulty,
        keyword: &Sp<ast::CondKeyword>,
        a: &Sp<ast::Expr>,
        binop: &Sp<ast::BinOpKind>,
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
            self.lower_cond_jump_non_count(stmt_span, stmt_data, keyword, a, goto)?;
            self.lower_cond_jump_non_count(stmt_span, stmt_data, keyword, b, goto)?;
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

            self.lower_cond_jump_non_count(stmt_span, stmt_data, &negated_kw, a, &skip_goto)?;
            self.lower_cond_jump_non_count(stmt_span, stmt_data, &negated_kw, b, &skip_goto)?;
            self.lower_uncond_jump(stmt_span, stmt_data, goto)?;
            self.out.push(sp!(binop.span => LowerStmt::Label { time: stmt_data.time, label: skip_label }));
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
        stmt_data: TimeAndDifficulty,
        data: &TemporaryExpr<'_>,
    ) -> Result<(DefId, Sp<ast::Expr>), ErrorReported> {
        let (def_id, var) = self.allocate_temporary(data.tmp_expr.span, data.tmp_ty)?;
        let var_as_expr = self.compute_temporary_expr(stmt_data, &var, data)?;

        Ok((def_id, var_as_expr))
    }

    /// Evaluate a temporary expression into an existing variable by emitting the instructions that compute it.
    ///
    /// For convenience, also returns an expression for reading the variable as a specific type, as you presumably
    /// have a reason for storing this value there. (the read type is allowed to differ from the expression's type)
    fn compute_temporary_expr(
        &mut self,
        stmt_data: TimeAndDifficulty,
        var: &Sp<ast::Var>,
        data: &TemporaryExpr<'_>,
    ) -> Result<Sp<ast::Expr>, ErrorReported> {
        let eq_sign = sp!(data.tmp_expr.span => token![=]);
        self.lower_assign_op(data.tmp_expr.span, stmt_data, var, &eq_sign, data.tmp_expr)?;

        let mut read_var = var.clone();
        let read_ty_sigil = get_temporary_read_ty(data.read_ty, var.span).map_err(|e| self.ctx.emitter.emit(e))?;
        read_var.ty_sigil = Some(read_ty_sigil);
        Ok(sp!(var.span => ast::Expr::Var(read_var)))
    }

    /// Emits an intrinsic that cleans up a register-allocated temporary.
    fn undefine_temporary(&mut self, span: Span, def_id: DefId) -> Result<(), ErrorReported> {
        self.out.push(sp!(span => LowerStmt::RegFree { def_id }));
        Ok(())
    }

    /// Grabs a new unique [`DefId`] and constructs an [`ast::Var`] for assigning a value to it.
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
        self.out.push(sp!(span => LowerStmt::RegAlloc { def_id }));

        Ok((def_id, var))
    }

    fn expect_simple_goto<'a>(&self, jump: &'a ast::StmtJumpKind) -> Result<&'a ast::StmtGoto, ErrorReported> {
        match jump {
            ast::StmtJumpKind::Goto(goto) => Ok(goto),
            ast::StmtJumpKind::BreakContinue { .. } => panic!("a break/continue made it to the lowering stage"),
        }
    }

    fn unsupported(&self, span: crate::pos::Span, what: &str) -> ErrorReported {
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
fn get_temporary_read_ty(ty: ScalarType, span: Span) -> Result<ReadType, Diagnostic> {
    ty.sigil().ok_or_else(|| error!(
        message("runtime temporary of non-numeric type"),
        primary(span, "temporary {} cannot be created", ty.descr_plural())
    ))
}

#[derive(Debug)]
enum ExprClass<'a> {
    /// The expression can become a single [`LowerArg`].
    Simple(SimpleExpr),
    /// The expression must be compiled separately and stored into some variable first.
    /// (possibly a new temporary)
    NeedsElaboration(TemporaryExpr<'a>),
}

#[derive(Debug)]
struct SimpleExpr {
    lowered: Sp<LowerArg>,
    /// Type in the AST. This *can* contradict the type of `lowered`. (e.g. float registers in EoSD ECL are ints)
    ty: ScalarType,
}

impl ExprClass<'_> {
    #[track_caller]
    fn expect_simple(&self) -> &SimpleExpr {
        match self {
            ExprClass::Simple(e) => e,
            _ => panic!("not simple: {:?}", self),
        }
    }
}

#[derive(Debug)]
struct TemporaryExpr<'a> {
    /// The part that must be stored to a temporary. Usually the whole expression, but for a cast we
    /// only store the inner part as a temporary.
    tmp_expr: &'a Sp<ast::Expr>,
    tmp_ty: ScalarType,
    read_ty: ScalarType,
}

impl SingleSubLowerer<'_, '_> {
    fn classify_expr<'a>(&self, arg: &'a Sp<ast::Expr>) -> Result<ExprClass<'a>, ErrorReported> {
        let needs_elaboration = || ExprClass::NeedsElaboration({
            let ty = arg.compute_ty(self.ctx).as_value_ty().expect("shouldn't be void");
            TemporaryExpr { tmp_expr: arg, tmp_ty: ty, read_ty: ty }
        });

        match &arg.value {
            &ast::Expr::LitInt { value, .. } => Ok(ExprClass::Simple(SimpleExpr {
                lowered: sp!(arg.span => LowerArg::Raw(value.into())),
                ty: ScalarType::Int,
            })),
            &ast::Expr::LitFloat { value, .. } => Ok(ExprClass::Simple(SimpleExpr {
                lowered: sp!(arg.span => LowerArg::Raw(value.into())),
                ty: ScalarType::Float,
            })),
            ast::Expr::LitString(ast::LitString { string, .. }) => Ok(ExprClass::Simple(SimpleExpr {
                lowered: sp!(arg.span => LowerArg::Raw(string.clone().into())),
                ty: ScalarType::String,
            })),
            ast::Expr::Var(var) => {
                let (lowered, ty) = lower_var_to_arg(var, self.ctx)?;
                Ok(ExprClass::Simple(SimpleExpr { lowered, ty }))
            },
            ast::Expr::LabelProperty { keyword, label } => Ok(ExprClass::Simple(SimpleExpr {
                lowered: sp!(arg.span => match keyword.value {
                    token![timeof] => LowerArg::TimeOf(label.value.clone()),
                    token![offsetof] => LowerArg::Label(label.value.clone()),
                }),
                ty: ScalarType::Int,
            })),

            // Here we treat casts.  A cast of any expression is understood to require a temporary of
            // the *input* type of the cast, but not the output type.  For example:
            //
            //             foo(%($I + 3));
            //
            // Ideally, this should compile into using only a single integer scratch register:
            //
            //             int tmp = $I + 3;
            //             foo(%tmp);
            //
            ast::Expr::UnOp(unop, b) => {

                // Check if this operation can lower to just a variable read
                if let Some(ty_sigil) = unop.as_ty_sigil_with_auto_cast() {
                    // This is a sigil or cast.
                    let tmp_ty = b.compute_ty(self.ctx).as_value_ty().expect("shouldn't be void");

                    // Most likely it needs no explicit instruction and can simply lower to a read.
                    let mut easy = false;
                    easy = easy || self.hooks.has_auto_casts();  // casts may lower to sigils...
                    easy = easy || unop.as_ty_sigil().is_some();  // ...and sigils are always reads.
                    easy = easy || unop.is_cast_of_type(tmp_ty);  // trivial casts (int -> int)
                    if easy {
                        let read_ty = ty_sigil.into();
                        Ok(ExprClass::NeedsElaboration(TemporaryExpr { tmp_ty, read_ty, tmp_expr: b }))
                    } else {
                        // This path will get taken by `int(...)/float(...)` in EoSD, requiring
                        // a `UnOp(op="int";type="float")` or `UnOp(op="float";type="int")`
                        // user-defined intrinsic.
                        Ok(needs_elaboration())
                    }
                } else {
                    // Not sigil or cast.  Needs to call a dedicated instruction
                    Ok(needs_elaboration())
                }
            },

            // Difficulty switches.
            //
            // These are "simple" if all of their cases are simple.  In this case, we propagate them
            // all the way down to the final stages of lowering so they can be used to replicate an
            // arbitrary instruction.  This significantly reduces scratch variable usage and allows
            // difficulty switches to roundtrip a lot more things.
            ast::Expr::DiffSwitch(cases) => {
                let mut lowered_cases = vec![];
                let mut ty = None;
                for case in cases {
                    match case {
                        None => lowered_cases.push(None),
                        Some(case) => match self.classify_expr(case)? {
                            ExprClass::Simple(out_case) => {
                                lowered_cases.push(Some(out_case.lowered));
                                ty = Some(out_case.ty);
                            },
                            // if even one case is not simple, the diff switch will need to be
                            // compiled into a dedicated assignment first
                            ExprClass::NeedsElaboration { .. } => return Ok(needs_elaboration()),
                        },
                    }
                }

                assert_eq!(cases.len(), lowered_cases.len());
                Ok(ExprClass::Simple(SimpleExpr {
                    lowered: sp!(arg.span => LowerArg::DiffSwitch(lowered_cases)),
                    ty: ty.expect("always at least one case"),
                }))
            },

            // Anything else needs a temporary of the same type, consisting of the whole expression.
            _ => Ok(needs_elaboration()),
        }
    }
}

fn lower_var_to_arg(var: &Sp<ast::Var>, ctx: &CompilerContext) -> Result<(Sp<LowerArg>, ScalarType), ErrorReported> {
    let read_ty = ctx.var_read_ty_from_ast(var).as_known_ty().expect("(bug!) untyped in stackless lowerer");

    // Up to this point in compilation, register aliases use Var::Named.
    // But now, we want both registers and their aliases to be resolved to a register
    let arg = match ctx.var_reg_from_ast(&var.name) {
        Ok((_lang, reg)) => LowerArg::Raw(SimpleArg::from_reg(reg, read_ty)),
        Err(def_id) => LowerArg::Local { def_id, storage_ty: read_ty },
    };
    Ok((sp!(var.span => arg), read_ty))
}

fn expr_uses_var(ast: &Sp<ast::Expr>, var: &ast::Var, ctx: &CompilerContext) -> bool {
    use ast::Visit;

    struct Visitor<'a, 'ctx> {
        ctx: &'a CompilerContext<'ctx>,
        aliasable_id: AliasableId,
        found: bool,
    }

    impl Visit for Visitor<'_, '_> {
        fn visit_var(&mut self, var: &Sp<ast::Var>) {
            let aliasable_id = self.ctx.var_aliasable_id(&var.name);
            if self.aliasable_id == aliasable_id {
                self.found = true;
            }
        }
    }

    let aliasable_id = ctx.var_aliasable_id(&var.name);
    let mut v = Visitor { aliasable_id, ctx, found: false };
    v.visit_expr(ast);
    v.found
}

// =============================================================================

#[derive(Default)]
pub (in crate::llir::lower) struct PersistentState {
    has_used_scratch: Option<Span>,
    has_anti_scratch_ins: Option<Span>,
}

impl PersistentState {
    pub (in crate::llir::lower) fn finish(self, ctx: &CompilerContext<'_>) -> Result<(), ErrorReported> {
        if let Some(anti_span) = self.has_anti_scratch_ins {
            if let Some(used_span) = self.has_used_scratch {
                return Err(ctx.emitter.emit(error!(
                    message("scratch registers are disabled in this entire file"),
                    primary(used_span, "this fancy expression requires a scratch register"),
                    secondary(anti_span, "Patchouli has tainted this entire file"),
                )))
            }
        }
        Ok(())
    }
}

/// Eliminates all `LowerArg::Local`s in a function body by allocating registers for them.
pub (in crate::llir::lower) fn assign_registers(
    code: &mut [Sp<LowerStmt>],
    global_scratch_results: &mut PersistentState,
    hooks: &dyn LanguageHooks,
    sub_info: Option<&super::SubInfo>,
    def_id: Option<DefId>,
    ctx: &CompilerContext,
    do_debug_info: bool,
) -> Result<Option<debug_info::ScriptRegisterInfo>, ErrorReported> {
    let stringify_reg = |reg| crate::fmt::stringify(&ctx.reg_to_ast(hooks.language(), reg));

    let mut local_regs = IdMap::<DefId, RegId>::new();
    let mut implicitly_used_regs = HashMap::<RegId, (ScalarType, Span)>::new();
    let mut has_used_scratch: Option<Span> = None;
    let mut has_anti_scratch_ins: Option<Span> = None;
    let mut debug_info = do_debug_info.then(|| debug_info::ScriptRegisterInfo {
        locals: vec![],
    });

    // FIXME:  Should this be here?  Stack-based ECL might want this check as well...
    // For detecting multiple names that represent the same register for non-scratch registers;
    // Presenting warnings on this is particularly important for old ECL subs with parameters,
    // as those parameters may alias registers.
    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    enum UsedName { RegId(RegId), DefId(DefId) }
    struct UsedNameData<'a> { span: Span, note: Option<&'a str> }
    let mut clashing_names_for_regs = IdMap::<RegId, IdMap<UsedName, UsedNameData>>::new();

    let explicitly_used_regs = get_explicitly_used_regs(code);

    // Start with all scratch regs.
    let mut remaining_scratch_regs_by_ty = hooks.general_use_regs();
    // Filter out ones explicitly mentioned by name.
    for vec in remaining_scratch_regs_by_ty.values_mut() {
        vec.retain(|reg| !explicitly_used_regs.contains_key(reg));
        vec.reverse();  // since we'll be popping from these lists
    }

    for (&reg, &span) in &explicitly_used_regs {
        clashing_names_for_regs.entry(reg).or_insert_with(Default::default)
            .insert(UsedName::RegId(reg), UsedNameData { span, note: None });
    }

    // assign registers to the params in accordance with however calls in this game work
    let param_note; // defined out here for lifetime purposes
    assert_eq!(sub_info.is_some(), def_id.is_some());
    if let (Some(sub_info), Some(def_id)) = (sub_info, def_id) {
        param_note = sub_info.sub_format.reg_usage_explanation(ctx);
        let this_sub_info = &sub_info.exported_subs.subs[&def_id];

        for (param_def_id, param_reg, ty, param_span) in this_sub_info.param_registers(sub_info.sub_format) {
            // make the register ineligible for scratch.  This only really affects EoSD.
            implicitly_used_regs.insert(param_reg, (ty.into(), param_span));
            for vec in remaining_scratch_regs_by_ty.values_mut() {
                vec.retain(|&scratch_reg| scratch_reg != param_reg);
            }

            // if the parameter has a name, record it
            if let Some(param_def_id) = param_def_id {
                local_regs.insert(param_def_id, param_reg);
                if let Some(debug_info) = &mut debug_info {
                    debug_info.locals.push(debug_info::Local {
                        name: ctx.defs.var_name(param_def_id).to_string(),
                        name_span: param_span.into(),
                        r#type: ty.into(),
                        bound_to: param_reg.into(),
                    });
                }

                clashing_names_for_regs.entry(param_reg).or_insert_with(Default::default)
                    .insert(UsedName::DefId(param_def_id), UsedNameData { note: param_note.as_deref(), span: param_span });
            }
        }
    }

    // assign scratch registers to all variables defined with RegAlloc
    for stmt in code {
        match &mut stmt.value {
            &mut LowerStmt::RegAlloc { def_id } => {
                has_used_scratch.get_or_insert(stmt.span);

                let required_ty = ctx.defs.var_inherent_ty(def_id).as_known_ty().expect("(bug!) untyped in stackless lowerer");

                let reg = remaining_scratch_regs_by_ty[required_ty].pop().ok_or_else(|| {
                    script_too_complex(stmt, hooks, required_ty, &explicitly_used_regs, &implicitly_used_regs, &ctx)
                })?;

                implicitly_used_regs.insert(reg, (required_ty, stmt.span));
                assert!(local_regs.insert(def_id, reg).is_none());
                assert!(!clashing_names_for_regs.contains_key(&reg));
                if let Some(debug_info) = &mut debug_info {
                    debug_info.locals.push(debug_info::Local {
                        name: ctx.defs.var_name(def_id).to_string(),
                        name_span: stmt.span.into(),
                        r#type: ReadType::from_ty(required_ty).expect("string-typed register?!").into(),
                        bound_to: reg.into(),
                    });
                }
            },
            LowerStmt::RegFree { def_id } => {
                let inherent_ty = ctx.defs.var_inherent_ty(*def_id).as_known_ty().expect("(bug!) we allocated a reg so it must have a type");
                let reg = local_regs.remove(&def_id).expect("(bug!) RegFree without RegAlloc!");
                assert!(implicitly_used_regs.remove(&reg).is_some());

                remaining_scratch_regs_by_ty[inherent_ty].push(reg);
            },
            LowerStmt::Instr(instr) => {
                if let Some(how_bad) = hooks.instr_disables_scratch_regs(instr.opcode) {
                    match how_bad {
                        HowBadIsIt::OhItsJustThisOneFunction => {
                            has_anti_scratch_ins.get_or_insert(stmt.span);
                        },
                        HowBadIsIt::ItsWaterElf => {
                            global_scratch_results.has_anti_scratch_ins.get_or_insert(stmt.span);
                        },
                    }
                }

                if let LowerArgs::Known(args) = &mut instr.args {
                    for arg in args {
                        // may need to recurse into difficulty switches
                        each_lower_arg(arg, &mut |arg| {
                            if let LowerArg::Local { def_id, storage_ty } = arg.value {
                                arg.value = LowerArg::Raw(SimpleArg::from_reg(local_regs[&def_id], storage_ty));
                            }
                        })
                    }
                }
            },
            LowerStmt::Label { .. } => {},
        }
    }

    if let Some(anti_span) = has_anti_scratch_ins {
        if let Some(used_span) = has_used_scratch {
            return Err(ctx.emitter.emit(error!(
                message("scratch registers are disabled in this script"),
                primary(used_span, "this fancy expression requires a scratch register"),
                primary(anti_span, "this disables scratch registers"),
            )))
        }
    }

    // FIXME: This might be too trigger happy and will fire on some innocent code.
    // However, we need SOMETHING to protect the user from overwriting `ARG_A` without realizing that
    // it is already in use.
    for (reg, used_names) in clashing_names_for_regs {
        if used_names.len() > 1 {
            let mut diag = warning!("register {} used under multiple names", stringify_reg(reg));
            for (_, UsedNameData { span, note }) in used_names {
                diag.primary(span, format!(""));
                if let Some(note) = note {
                    diag.note(format!("{}", note));
                }
            }
            ctx.emitter.emit(diag).ignore();
        }
    }

    if let Some(span) = has_used_scratch {
        global_scratch_results.has_used_scratch.get_or_insert(span);
    }

    Ok(debug_info)
}

fn each_lower_arg(arg: &mut Sp<LowerArg>, func: &mut dyn FnMut(&mut Sp<LowerArg>)) {
    func(arg);
    if let LowerArg::DiffSwitch(cases) = &mut arg.value {
        for case in cases {
            if let Some(case) = case {
                each_lower_arg(case, func);
            }
        }
    }
}

/// Generate a "script too complex" error.
fn script_too_complex(
    stmt: &Sp<LowerStmt>,
    hooks: &dyn LanguageHooks,
    required_ty: ScalarType,
    explicitly_used_regs: &BTreeMap<RegId, Span>,
    implicitly_used_regs: &HashMap<RegId, (ScalarType, Span)>,
    ctx: &CompilerContext,
) -> ErrorReported {
    let stringify_reg = |reg| crate::fmt::stringify(&ctx.reg_to_ast(hooks.language(), reg));

    let mut error = error!(
        message("script too complex to compile"),
        primary(stmt.span, "no more registers of this type!"),
    );
    for (&scratch_reg, &(scratch_ty, scratch_span)) in implicitly_used_regs {
        if scratch_ty == required_ty {
            error.secondary(scratch_span, format!("{} holds this", stringify_reg(scratch_reg)));
        }
    }
    let regs_of_ty = hooks.general_use_regs()[required_ty].clone();
    let unavailable_strs = regs_of_ty.iter().copied()
        .filter(|reg| explicitly_used_regs.contains_key(reg))
        .map(stringify_reg)
        .collect::<Vec<_>>();
    if !unavailable_strs.is_empty() {
        error.note(format!(
            "the following registers are unavailable due to explicit use: {}",
            unavailable_strs.join(", "),
        ));
    }

    ctx.emitter.emit(error)
}

// Gather all explicitly-used registers in the source. (so that we can avoid using them for scratch)
fn get_explicitly_used_regs(func_body: &[Sp<LowerStmt>]) -> BTreeMap<RegId, Span> {
    func_body.iter()
        .filter_map(|stmt| match &stmt.value {
            LowerStmt::Instr(LowerInstr { args: LowerArgs::Known(args), .. }) => Some(args),
            _ => None
        }).flat_map(|args| args.iter().filter_map(|arg| match &arg.value {
            LowerArg::Raw(raw) => raw.get_reg_id().map(|reg| (reg, arg.span)),
            _ => None,
        })).collect()
}
