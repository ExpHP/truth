use std::collections::{HashMap};

use super::unsupported;
use crate::llir::{Instr, InstrFormat, IntrinsicInstrKind, IntrinsicInstrs, InstrArg, RawArg};
use crate::error::{GatherErrorIteratorExt, CompileError};
use crate::pos::{Sp, Span};
use crate::ast::{self, Expr};
use crate::ident::Ident;
use crate::var::{LocalId, VarId, RegId};
use crate::type_system::{TypeSystem, ArgEncoding, ScalarType};

use IntrinsicInstrKind as IKind;

/// An intermediate representation that is only used during lowering.
///
/// In addition to instructions, it has a couple of extra things that are handled via
/// some post-processing steps
#[derive(Debug, Clone, PartialEq)]
enum LowLevelStmt {
    /// Represents a single instruction in the compiled file.
    Instr(Instr),
    /// An intrinsic that represents a label that can be jumped to.
    Label { time: i32, label: Sp<Ident> },
    /// An intrinsic that begins the scope of a register-allocated local.
    RegAlloc { local_id: LocalId, cause: Span },
    /// An intrinsic that ends the scope of a register-allocated local.
    RegFree { local_id: LocalId },
}

pub fn lower_sub_ast_to_instrs(
    instr_format: &dyn InstrFormat,
    code: &[Sp<ast::Stmt>],
    ty_ctx: &mut TypeSystem,
) -> Result<Vec<Instr>, CompileError> {
    let used_regs = get_used_regs(code);

    let mut lowerer = Lowerer {
        out: vec![],
        intrinsic_instrs: instr_format.intrinsic_instrs(),
        ty_ctx,
        instr_format,
    };
    lowerer.lower_sub_ast(code)?;
    let mut out = lowerer.out;

    // And now postprocess
    encode_labels(&mut out, instr_format, 0)?;
    assign_registers(&mut out, &used_regs, instr_format, ty_ctx)?;

    Ok(out.into_iter().filter_map(|x| match x {
        LowLevelStmt::Instr(instr) => Some(instr),
        LowLevelStmt::Label { .. } => None,
        LowLevelStmt::RegAlloc { .. } => None,
        LowLevelStmt::RegFree { .. } => None,
    }).collect())
}

/// Helper responsible for converting an AST into [`LowLevelStmt`]s.
struct Lowerer<'ts> {
    out: Vec<LowLevelStmt>,
    intrinsic_instrs: IntrinsicInstrs,
    instr_format: &'ts dyn InstrFormat,
    ty_ctx: &'ts mut TypeSystem,
}

impl Lowerer<'_> {
    pub fn lower_sub_ast(
        &mut self,
        code: &[Sp<ast::Stmt>],
    ) -> Result<(), CompileError> {
        let mut th06_anm_end_span = None;
        code.iter().map(|stmt| {
            if let Some(end) = th06_anm_end_span {
                if !matches!(&stmt.body.value, ast::StmtBody::NoInstruction) { return Err(error!(
                    message("statement after end of script"),
                    primary(&stmt.body, "forbidden statement"),
                    secondary(&end, "marks the end of the script"),
                    note("In EoSD ANM, every script must have a single exit point (opcode 0 or 15), as the final instruction."),
                ))}
            }

            match &stmt.body.value {
                ast::StmtBody::Jump(goto) => {
                    if goto.time.is_some() && !self.instr_format.jump_has_time_arg() {
                        return Err(unsupported(&stmt.body.span, "goto @ time"));
                    }

                    let (label_arg, time_arg) = lower_goto_args(goto);

                    self.out.push(LowLevelStmt::Instr(Instr {
                        time: stmt.time,
                        opcode: self.get_opcode(IKind::Jmp, stmt.body.span, "'goto'")?,
                        args: vec![label_arg, time_arg],
                    }));
                },


                ast::StmtBody::Assignment { var, op, value } => {
                    self.lower_assign_op(stmt.body.span, stmt.time, var, op, value)?;
                },


                ast::StmtBody::InterruptLabel(interrupt_id) => {
                    self.out.push(LowLevelStmt::Instr(Instr {
                        time: stmt.time,
                        opcode: self.get_opcode(IKind::InterruptLabel, stmt.body.span, "interrupt label")?,
                        args: vec![InstrArg::Raw(interrupt_id.value.into())],
                    }));
                },


                ast::StmtBody::CondJump { keyword, cond, jump } => {
                    self.lower_cond_jump(stmt.body.span, stmt.time, keyword, cond, jump)?;
                },


                ast::StmtBody::Declaration { keyword, vars } => {
                    self.lower_var_declaration(stmt.body.span, stmt.time, keyword, vars)?;
                },


                ast::StmtBody::Expr(expr) => match &expr.value {
                    ast::Expr::Call { func, args } => {
                        let opcode = self.lower_func_stmt(stmt, func, args)?;
                        if self.instr_format.is_th06_anm_terminating_instr(opcode) {
                            th06_anm_end_span = Some(func);
                        }
                    },
                    _ => return Err(unsupported(&stmt.body.span, &format!("{} in {}", expr.descr(), stmt.body.descr()))),
                }, // match expr

                ast::StmtBody::Label(ident) => self.out.push(LowLevelStmt::Label { time: stmt.time, label: ident.clone() }),

                &ast::StmtBody::ScopeEnd(local_id) => self.out.push(LowLevelStmt::RegFree { local_id }),

                ast::StmtBody::NoInstruction => {}

                _ => return Err(unsupported(&stmt.body.span, stmt.body.descr())),
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
        func: &Sp<Ident>,
        args: &[Sp<Expr>],
    ) -> Result<u16, CompileError> {
        // all function statements currently refer to single instructions
        let opcode = match self.ty_ctx.regs_and_instrs.resolve_func_aliases(func).as_ins() {
            Some(opcode) => opcode,
            None => return Err(error!(
                message("unknown instruction '{}'", func),
                primary(func, "not an instruction"),
            )),
        };

        self.lower_instruction(stmt, opcode as _, func, args)
    }

    /// Lowers `func(<ARG1>, <ARG2>, <...>);` where `func` is an instruction alias.
    fn lower_instruction(
        &mut self,
        stmt: &Sp<ast::Stmt>,
        opcode: u16,
        name: &Sp<Ident>,
        args: &[Sp<Expr>],
    ) -> Result<u16, CompileError> {
        // If a signature is in the mapfile, validate the args.
        let encodings = match self.ty_ctx.regs_and_instrs.ins_signature(opcode) {
            Some(siggy) => {
                if !(siggy.min_args() <= args.len() && args.len() <= siggy.max_args()) {
                    return Err(error!(
                        message("wrong number of arguments to '{}'", name),
                        primary(name, "expects {} to {} arguments, got {}", siggy.min_args(), siggy.max_args(), args.len()),
                    ));
                }
                Some(siggy.arg_encodings())
            },
            None => None,
        };

        let mut temp_local_ids = vec![];
        let low_level_args = args.iter().enumerate().map(|(arg_index, expr)| {
            let (lowered, actual_ty) = match classify_expr(expr, self.ty_ctx)? {
                ExprClass::Simple(data) => (data.lowered, data.ty),
                ExprClass::NeedsTemp(data) => {
                    // Save this expression to a temporary
                    let (local_id, _) = self.define_temporary(stmt.time, &data)?;
                    let lowered = InstrArg::Local { local_id, read_ty: data.read_ty };

                    temp_local_ids.push(local_id); // so we can free the register later

                    (lowered, data.read_ty)
                },
            };

            let expected_ty = match encodings.as_ref() {
                Some(encodings) => match encodings[arg_index] {
                    ArgEncoding::Padding |
                    ArgEncoding::Color |
                    ArgEncoding::Dword => ScalarType::Int,
                    ArgEncoding::Float => ScalarType::Float,
                },
                // signature not in mapfile.  Just let it be whatever.
                None => actual_ty,
            };
            if actual_ty != expected_ty {
                return Err(error!(
                    message("type error"),
                    primary(expr, "wrong type for argument {}", arg_index+1),
                    secondary(name, "expects {}", expected_ty.descr()),
                    // TODO: note ECL file or pragma that gives signature?
                ));
            }
            Ok(lowered)
        }).collect_with_recovery()?;

        self.out.push(LowLevelStmt::Instr(Instr {
            time: stmt.time,
            opcode: opcode as _,
            args: low_level_args,
        }));

        for id in temp_local_ids.into_iter().rev() {
            self.undefine_temporary(id)?;
        }

        Ok(opcode)
    }

    /// Lowers `if (<cond>) goto label @ time;`
    fn lower_var_declaration(
        &mut self,
        _stmt_span: Span,
        stmt_time: i32,
        _keyword: &Sp<ast::VarDeclKeyword>,
        vars: &[Sp<(Sp<ast::Var>, Option<Sp<ast::Expr>>)>],
    ) -> Result<(), CompileError>{
        for pair in vars {
            let (var, expr) = &pair.value;
            let var_id = match var.value {
                ast::Var::Named { ref ident, .. } => panic!("(bug!) unresolved var during lowering: {}", ident),
                ast::Var::Resolved { var_id, .. } => var_id,
            };
            let local_id = match var_id {
                VarId::Local(local_id) => local_id,
                VarId::Reg { .. } => panic!("(bug?) declared var somehow resolved as register!"),
            };

            self.out.push(LowLevelStmt::RegAlloc { local_id, cause: var.span });

            if let Some(expr) = expr {
                let assign_op = sp!(pair.span => ast::AssignOpKind::Assign);
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
    ) -> Result<(), CompileError> {
        let (lowered_var, ty_var) = lower_var_to_arg(var, self.ty_ctx)?;

        let data_rhs = match classify_expr(rhs, self.ty_ctx)? {
            // a = <atom>;
            // a += <atom>;
            ExprClass::Simple(SimpleExpr { lowered: lowered_rhs, ty: ty_rhs }) => {
                let ty = ty_var.check_same(ty_rhs, assign_op.span, (var.span, rhs.span))?;
                self.out.push(LowLevelStmt::Instr(Instr {
                    time,
                    opcode: self.get_opcode(IKind::AssignOp(assign_op.value, ty), span, "update assignment with this operation")?,
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
            let (tmp_local_id, tmp_as_expr) = self.define_temporary(time, &data_rhs)?;
            self.lower_assign_op(span, time, var, assign_op, &tmp_as_expr)?;
            self.undefine_temporary(tmp_local_id)?;
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
                        let (tmp_local_id, tmp_var_expr) = self.define_temporary(time, &data_rhs)?;
                        self.lower_assign_op(span, time, var, assign_op, &tmp_var_expr)?;
                        self.undefine_temporary(tmp_local_id)?;
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
                    let (tmp_local_id, tmp_as_expr) = self.define_temporary(time, &data_a)?;
                    self.lower_assign_direct_binop(span, time, var, eq_sign, rhs_span, &tmp_as_expr, binop, b)?;
                    self.undefine_temporary(tmp_local_id)?;
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
                    let (tmp_local_id, tmp_as_expr) = self.define_temporary(time, &data_b)?;
                    self.lower_assign_direct_binop(span, time, var, eq_sign, rhs_span, a, binop, &tmp_as_expr)?;
                    self.undefine_temporary(tmp_local_id)?;
                }
                return Ok(());
            },
            ExprClass::Simple(simple) => simple,
        };

        // They're both simple.  Emit a primitive instruction.
        let (lowered_var, ty_var) = lower_var_to_arg(var, self.ty_ctx)?;
        let ty_rhs = binop.result_type(simple_a.ty, simple_b.ty, (a.span, b.span))?;
        let ty = ty_var.check_same(ty_rhs, eq_sign.span, (var.span, rhs_span))?;

        self.out.push(LowLevelStmt::Instr(Instr {
            time,
            opcode: self.get_opcode(IKind::Binop(binop.value, ty), span, "this binary operation")?,
            args: vec![lowered_var, simple_a.lowered, simple_b.lowered],
        }));
        Ok(())
    }

    /// Lowers `a = <B> * <C>;`
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
        if unop.value == ast::UnopKind::Neg {
            let ty = self.ty_ctx.compute_type_shallow(b)?;
            let zero = sp!(unop.span => ast::Expr::zero(ty));
            let minus = sp!(unop.span => ast::BinopKind::Sub);
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
                    let (tmp_local_id, tmp_as_expr) = self.define_temporary(time, &data_b)?;
                    self.lower_assign_direct_unop(span, time, var, eq_sign, rhs_span, unop, &tmp_as_expr)?;
                    self.undefine_temporary(tmp_local_id)?;
                }
                Ok(())
            },

            ExprClass::Simple(data_b) => {
                let (lowered_var, ty_var) = lower_var_to_arg(var, self.ty_ctx)?;
                let ty_rhs = unop.result_type(data_b.ty, b.span)?;
                ty_var.check_same(ty_rhs, eq_sign.span, (var.span, rhs_span))?;
                let ty = ty_var;

                match unop.value {
                    // These are all handled other ways
                    ast::UnopKind::CastI |
                    ast::UnopKind::CastF |
                    ast::UnopKind::Neg => unreachable!(),

                    // TODO: we *could* polyfill this with some conditional jumps but bleccccch
                    ast::UnopKind::Not => return Err(unsupported(&span, "logical not operator")),

                    ast::UnopKind::Sin |
                    ast::UnopKind::Cos |
                    ast::UnopKind::Sqrt => self.out.push(LowLevelStmt::Instr(Instr {
                        time,
                        opcode: self.get_opcode(IKind::Unop(unop.value, ty), span, "this unary operation")?,
                        args: vec![lowered_var, data_b.lowered],
                    })),
                }
                Ok(())
            },
        }
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
        let (arg_label, arg_time) = lower_goto_args(goto);

        match (keyword.value, &cond.value) {
            (ast::CondKeyword::If, ast::Cond::Decrement(var)) => {
                let (arg_var, ty_var) = lower_var_to_arg(var, self.ty_ctx)?;
                if ty_var != ScalarType::Int {
                    return Err(error!(
                        message("type error"),
                        primary(cond, "expected an int, got {}", ty_var.descr()),
                        secondary(keyword, "required by this"),
                    ));
                }

                self.out.push(LowLevelStmt::Instr(Instr {
                    time: stmt_time,
                    opcode: self.get_opcode(IKind::CountJmp, stmt_span, "decrement jump")?,
                    args: vec![arg_var, arg_label, arg_time],
                }));
                Ok(())
            },

            (ast::CondKeyword::If, ast::Cond::Expr(expr)) => match &expr.value {
                Expr::Binop(a, binop, b) => self.lower_cond_jump_binop(stmt_span, stmt_time, keyword, a, binop, b, goto),

                // other arbitrary expressions: use `if (<expr> != 0)`
                _ => {
                    let ty = self.ty_ctx.compute_type_shallow(expr)?;
                    let zero = sp!(expr.span => ast::Expr::zero(ty));
                    let ne_sign = sp!(expr.span => ast::BinopKind::Ne);
                    self.lower_cond_jump_binop(stmt_span, stmt_time, keyword, expr, &ne_sign, &zero, goto)
                },
            },
        }
    }

    /// Lowers `if (<A> != <B>) goto label @ time;` and similar
    fn lower_cond_jump_binop(
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
            // `if (<A> != <B>) ...`
            // split out to: `tmp = <A>;  if (tmp != <B>) ...`;
            (ExprClass::NeedsTemp(data_a), _) => {
                let (id, var_expr) = self.define_temporary(stmt_time, &data_a)?;
                self.lower_cond_jump_binop(stmt_span, stmt_time, keyword, &var_expr, binop, b, goto)?;
                self.undefine_temporary(id)?;
            },

            // `if (a != <B>) ...`
            // split out to: `tmp = <B>;  if (a != tmp) ...`;
            (ExprClass::Simple(_), ExprClass::NeedsTemp(data_b)) => {
                let (id, var_expr) = self.define_temporary(stmt_time, &data_b)?;
                self.lower_cond_jump_binop(stmt_span, stmt_time, keyword, a, binop, &var_expr, goto)?;
                self.undefine_temporary(id)?;
            },

            // `if (a != b) ...`
            (ExprClass::Simple(data_a), ExprClass::Simple(data_b)) => {
                let ty_arg = binop.result_type(data_a.ty, data_b.ty, (a.span, b.span))?;
                let (lowered_label, lowered_time) = lower_goto_args(goto);
                self.out.push(LowLevelStmt::Instr(Instr {
                    time: stmt_time,
                    opcode: self.get_opcode(IKind::CondJmp(binop.value, ty_arg), binop.span, "conditional jump with this operator")?,
                    args: vec![data_a.lowered, data_b.lowered, lowered_label, lowered_time],
                }));
            },
        }
        Ok(())
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
    ) -> Result<(LocalId, Sp<Expr>), CompileError> {
        let (local_id, var) = self.allocate_temporary(data.tmp_expr.span, data.tmp_ty);
        let var_as_expr = self.compute_temporary_expr(time, &var, data)?;

        Ok((local_id, var_as_expr))
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
        let eq_sign = sp!(data.tmp_expr.span => ast::AssignOpKind::Assign);
        self.lower_assign_op(data.tmp_expr.span, time, var, &eq_sign, data.tmp_expr)?;

        let mut read_var = var.clone();
        read_var.set_ty_sigil(Some(data.read_ty.into()));
        Ok(sp!(var.span => ast::Expr::Var(read_var)))
    }

    /// Emits an intrinsic that cleans up a register-allocated temporary.
    fn undefine_temporary(&mut self, local_id: LocalId) -> Result<(), CompileError> {
        self.out.push(LowLevelStmt::RegFree { local_id });
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
    ) -> (LocalId, Sp<ast::Var>) {
        let local_id = self.ty_ctx.variables.declare_temporary(Some(tmp_ty));

        let var = sp!(span => ast::Var::Resolved { ty_sigil: Some(tmp_ty.into()), var_id: local_id.into() });
        self.out.push(LowLevelStmt::RegAlloc { local_id, cause: span });

        (local_id, var)
    }

    fn get_opcode(&self, kind: IntrinsicInstrKind, span: Span, descr: &str) -> Result<u16, CompileError> {
        self.intrinsic_instrs.get_opcode(kind, span, descr)
    }
}

enum ExprClass<'a> {
    Simple(SimpleExpr),
    NeedsTemp(TemporaryExpr<'a>),
}

struct SimpleExpr {
    lowered: InstrArg,
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
            lowered: InstrArg::Raw(value.into()),
            ty: ScalarType::Int,
        })),
        ast::Expr::LitFloat { value, .. } => Ok(ExprClass::Simple(SimpleExpr {
            lowered: InstrArg::Raw(value.into()),
            ty: ScalarType::Float,
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
                ast::UnopKind::CastI => (ScalarType::Float, ScalarType::Int),
                ast::UnopKind::CastF => (ScalarType::Int, ScalarType::Float),
                _ => unreachable!("filtered out by is_cast()"),
            };
            Ok(ExprClass::NeedsTemp(TemporaryExpr { tmp_ty, read_ty, tmp_expr: b }))
        },

        // Anything else needs a temporary of the same type, consisting of the whole expression.
        _ => Ok(ExprClass::NeedsTemp({
            let ty = ty_ctx.compute_type_shallow(arg)?;
            TemporaryExpr { tmp_expr: arg, tmp_ty: ty, read_ty: ty }
        })),
    }
}

fn lower_var_to_arg(var: &Sp<ast::Var>, ty_ctx: &TypeSystem) -> Result<(InstrArg, ScalarType), CompileError> {
    let read_ty = ty_ctx.var_read_type_from_ast(var)?;
    let arg = match var.value {
        ast::Var::Named { ref ident, .. } => panic!("(bug!) unresolved var during lowering: {}", ident),
        ast::Var::Resolved { var_id: VarId::Reg(reg), .. } => InstrArg::Raw(RawArg::from_reg(reg, read_ty)),
        ast::Var::Resolved { var_id: VarId::Local(local_id), .. } => InstrArg::Local { local_id, read_ty },
    };
    Ok((arg, read_ty))
}

fn lower_goto_args(goto: &ast::StmtGoto) -> (InstrArg, InstrArg) {
    let label_arg = InstrArg::Label(goto.destination.clone());
    let time_arg = match goto.time {
        Some(time) => InstrArg::Raw(time.into()),
        None => InstrArg::TimeOf(goto.destination.clone()),
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


struct RawLabelInfo {
    time: i32,
    offset: usize,
}
fn gather_label_info(
    format: &dyn InstrFormat,
    initial_offset: usize,
    code: &[LowLevelStmt]
) -> Result<HashMap<Sp<Ident>, RawLabelInfo>, CompileError> {
    use std::collections::hash_map::Entry;

    let mut offset = initial_offset;
    let mut out = HashMap::new();
    code.iter().map(|thing| {
        match *thing {
            LowLevelStmt::Instr(ref instr) => {
                offset += format.instr_size(instr);
            },
            LowLevelStmt::Label { time, ref label } => {
                match out.entry(label.clone()) {
                    Entry::Vacant(e) => {
                        e.insert(RawLabelInfo { time, offset });
                    },
                    Entry::Occupied(e) => {
                        return Err(error!{
                            message("duplicate label '{}'", label),
                            primary(label, "redefined here"),
                            secondary(e.key(), "originally defined here"),
                        });
                    },
                }
            },
            _ => {},
        }
        Ok::<_, CompileError>(())
    }).collect_with_recovery()?;

    Ok(out)
}

// =============================================================================

/// Eliminates all `InstrArg::Label`s by replacing them with their dword values.
fn encode_labels(
    code: &mut [LowLevelStmt],
    format: &dyn InstrFormat,
    initial_offset: usize,
) -> Result<(), CompileError> {
    let label_info = gather_label_info(format, initial_offset, code)?;

    code.iter_mut().map(|thing| {
        match thing {
            LowLevelStmt::Instr(instr) => for arg in &mut instr.args {
                match *arg {
                    | InstrArg::Label(ref label)
                    | InstrArg::TimeOf(ref label)
                    => match label_info.get(label) {
                        Some(info) => match arg {
                            InstrArg::Label(_) => *arg = InstrArg::Raw(format.encode_label(info.offset).into()),
                            InstrArg::TimeOf(_) => *arg = InstrArg::Raw(info.time.into()),
                            _ => unreachable!(),
                        },
                        None => return Err(error!{
                            message("undefined label '{}'", label),
                            primary(label, "there is no label by this name"),
                        }),
                    },
                    _ => {},
                }
            },
            _ => {},
        }
        Ok(())
    }).collect_with_recovery()
}

/// Eliminates all `InstrArg::Label`s by replacing them with their dword values.
fn assign_registers(
    code: &mut [LowLevelStmt],
    used_regs: &[RegId],
    format: &dyn InstrFormat,
    ty_ctx: &TypeSystem,
) -> Result<(), CompileError> {
    let mut unused_regs = format.general_use_regs();
    for vec in unused_regs.values_mut() {
        vec.retain(|id| !used_regs.contains(id));
        vec.reverse();  // since we'll be popping from these lists
    }

    let mut local_regs = HashMap::<LocalId, (RegId, ScalarType, Span)>::new();

    for stmt in code {
        match stmt {
            LowLevelStmt::RegAlloc { local_id, ref cause } => {
                let ty = ty_ctx.variables.get_type(*local_id).expect("(bug!) this should have been type-checked!");

                let reg = unused_regs[ty].pop().ok_or_else(|| {
                    let stringify_reg = |reg| crate::fmt::stringify(&ty_ctx.var_to_ast(VarId::Reg(reg), ty, false));

                    let mut error = crate::error::Diagnostic::error();
                    error.message(format!("script too complex to compile"));
                    error.primary(cause, format!("no more registers of this type!"));
                    for &(scratch_reg, scratch_ty, scratch_span) in local_regs.values() {
                        if scratch_ty == ty {
                            error.secondary(scratch_span, format!("{} holds this", stringify_reg(scratch_reg)));
                        }
                    }
                    let regs_of_ty = format.general_use_regs()[ty].clone();
                    let unavailable_strs = regs_of_ty.iter().copied()
                        .filter(|id| used_regs.contains(id))
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

                assert!(local_regs.insert(*local_id, (reg, ty, *cause)).is_none());
            },
            LowLevelStmt::RegFree { local_id } => {
                let inherent_ty = ty_ctx.variables.get_type(*local_id).expect("(bug!) this should have been type-checked!");
                let (reg, _, _) = local_regs.remove(&local_id).expect("(bug!) RegFree without RegAlloc!");
                unused_regs[inherent_ty].push(reg);
            },
            LowLevelStmt::Instr(instr) => {
                for arg in &mut instr.args {
                    if let InstrArg::Local { local_id, read_ty } = *arg {
                        *arg = InstrArg::Raw(RawArg::from_reg(local_regs[&local_id].0, read_ty));
                    }
                }
            },
            LowLevelStmt::Label { .. } => {},
        }
    }
    Ok(())
}

// NOTE: at the time of writing, this has to be done to the ast (it can't be done to LowLevelStmts because
//       there's no way to recover a register number from a RawArg in consideration of floats).
fn get_used_regs(func_body: &[Sp<ast::Stmt>]) -> Vec<RegId> {
    use ast::Visit;

    struct UsedVisitor { used: Vec<RegId> }

    impl Visit for UsedVisitor {
        fn visit_var(&mut self, x: &Sp<ast::Var>) { match &x.value {
            ast::Var::Named { ident, .. } => panic!("(bug!) unresolved var during lowering: {}", ident),
            ast::Var::Resolved { var_id: VarId::Reg(reg), .. } => self.used.push(*reg),
            ast::Var::Resolved { var_id: VarId::Local(_), .. } => {},
        }}
    }

    let mut v = UsedVisitor { used: vec![] };
    for stmt in func_body {
        v.visit_stmt(stmt);
    }
    v.used
}
