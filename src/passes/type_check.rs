//! See [`run`].

use crate::ast;
use crate::error::{GatherErrorIteratorExt, ErrorReported, ErrorFlag};
use crate::pos::{Sp, Span};
use crate::value::{ScalarType, VarType, ExprType};
use crate::context::CompilerContext;
use crate::resolve::DefId;
use crate::ast::TypeKeyword;

/// Performs type-checking on the whole AST.
///
/// Requires [name resolution](`crate::passes::resolution`).
///
/// The purpose of this pass is to serve as the answer to the question, "when do we generate an
/// error about this?"  Ideally, all errors that can be classified as type errors are reported
/// to the user during this pass.  Having run this pass, one can feel comfortable simply panicking
/// when bad types are encountered in other passes like lowering.
pub fn run<A: ast::Visitable>(ast: &A, ctx: &mut CompilerContext) -> Result<(), ErrorReported> {
    let checker = ExprTypeChecker { ctx };
    let mut v = Visitor { checker, errors: ErrorFlag::new(), cur_func_stack: vec![] };
    ast.visit_with(&mut v);
    v.errors.into_result(())
}

/// Performs additional, shallow type checks that couldn't be done by [`run`] or the checks in
/// [`FromMeta`] for whatever reason.
pub fn extra_checks(checks: &[ShallowTypeCheck], ctx: &CompilerContext) -> Result<(), ErrorReported> {
    let checker = ExprTypeChecker { ctx };
    checks.iter().map(|check| checker.perform_shallow_type_check(check, ctx))
        .collect_with_recovery()
}

/// Represents an auxilliary type-check that isn't normally performed by the `type_check` pass.
pub struct ShallowTypeCheck {
    pub expr: Sp<ast::Expr>,
    pub ty: ExprType,
    pub cause: Option<Span>,
}

type ImplResult<T = ()> = Result<T, ErrorReported>;

// =============================================================================

struct ExprTypeChecker<'a, 'ctx> {
    ctx: &'a CompilerContext<'ctx>,
}

struct Visitor<'a, 'ctx> {
    checker: ExprTypeChecker<'a, 'ctx>,
    errors: ErrorFlag,
    /// Stack of nested functions whose bodies we are currently inside.
    cur_func_stack: Vec<FuncState>,
}

struct FuncState {
    func_def_id: DefId,
    missing_return: bool,
}

impl<'a, 'ctx> std::ops::Deref for Visitor<'a, 'ctx> {
    type Target = ExprTypeChecker<'a, 'ctx>;

    fn deref(&self) -> &Self::Target { &self.checker }
}

impl<'a, 'ctx> std::ops::DerefMut for Visitor<'a, 'ctx> {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.checker }
}

impl ast::Visit for Visitor<'_, '_> {
    // NOTE: This visitor is a bit unusual.
    //
    //       Whenever we encounter an expression, we will stop using Visit to walk subexpressions, and we
    //       will instead call `self.check_expr`.
    //
    //       self.check_expr is a function that, much like a Visitor, walks the AST... but the difference is
    //       that it returns the type of the expr.  So basically by using it we get to type check the whole
    //       interior of the expression, and then we get back its type that can be used to perform any
    //       additional validation.  (e.g. the count of `times` must be an integer)
    //
    //       Because that additional validation cannot be performed within just visit_expr, this method is
    //       actually fairly unlikely to be called.  Most of the legwork is in done in the visit methods
    //       for things that CONTAIN expressions.
    fn visit_expr(&mut self, expr: &Sp<ast::Expr>) {
        if let Err(e) = self.check_expr(expr) {
            self.errors.set(e);
        }
    }

    fn visit_item(&mut self, item: &Sp<ast::Item>) {
        match &item.value {
            ast::Item::Func(ast::ItemFunc { ident, ty_keyword, .. }) => {
                let func_def_id = self.ctx.resolutions.expect_def(ident);
                self.cur_func_stack.push(FuncState {
                    func_def_id,
                    missing_return: matches!(ty_keyword.expr_ty(), ExprType::Value(_)),
                });

                ast::walk_item(self, item);

                let finished_state = self.cur_func_stack.pop().expect("unbalanced stack usage");

                if finished_state.missing_return {
                    // FIXME: Needs test of warnings
                    self.emit(warning!(
                        message("value-returning function without a return"),
                        primary(item, "has no return statements"),
                    )).ignore();
                }
            },

            _ => ast::walk_item(self, item),
        }
    }

    fn visit_stmt(&mut self, stmt: &Sp<ast::Stmt>) {
        match &stmt.value.kind {
            // statement types where there's nothing additional to check beyond what
            // would already be done by recursively walking the node
            | ast::StmtKind::Item { .. }
            | ast::StmtKind::CondChain { .. }
            | ast::StmtKind::CondJump { .. }
            | ast::StmtKind::While { .. }
            | ast::StmtKind::Jump { .. }
            | ast::StmtKind::Loop { .. } => {
                ast::walk_stmt(self, stmt)
            },

            &ast::StmtKind::Return { ref value, keyword } => {
                if let Err(e) = self.check_stmt_return(keyword, value) {
                    self.errors.set(e);
                }
            },

            ast::StmtKind::Assignment { var, op, value } => {
                if let Err(e) = self.check_stmt_assignment(var, *op, value) {
                    self.errors.set(e);
                }
            },

            ast::StmtKind::Expr(expr) => {
                if let Err(e) = self.check_stmt_expr(expr) {
                    self.errors.set(e);
                }
            },

            ast::StmtKind::Times { clobber, count, block, keyword: _, loop_id: _ } => {
                if let Err(e) = self.check_stmt_times(clobber, count) {
                    self.errors.set(e);
                }
                ast::walk_block(self, block);
            },

            ast::StmtKind::Declaration { ty_keyword, vars } => {
                if let Err(e) = self.check_stmt_declaration(*ty_keyword, vars) {
                    self.errors.set(e);
                }
            },

            ast::StmtKind::CallSub { .. } => unimplemented!("need to check arg types against signature"),

            ast::StmtKind::Block { .. } => {},
            ast::StmtKind::InterruptLabel { .. } => {},
            ast::StmtKind::AbsTimeLabel { .. } => {},
            ast::StmtKind::RelTimeLabel { .. } => {},
            ast::StmtKind::Label { .. } => {},
            ast::StmtKind::ScopeEnd { .. } => {},
            ast::StmtKind::NoInstruction { .. } => {},
        }
    }

    fn visit_jump(&mut self, jump: &ast::StmtJumpKind) {
        ast::walk_jump(self, jump);

        match jump {
            ast::StmtJumpKind::Goto(ast::StmtGoto { destination, time }) => {
                // There is the remote possibility that at some point in the future, I may want to change
                // either or both of these into full-fledged expressions (and subject them to const folding).
                //
                // In case that change is ever made, these statements will stop compiling and you will see
                // this comment reminding you to fix this.  ;)
                //
                // (in particular, you need to check that the new expression(s) are of integer type).
                let _: &Option<Sp<i32>> = time;
                let _: &Sp<crate::ident::Ident> = destination;
            },
            ast::StmtJumpKind::BreakContinue { .. } => {},
        }
    }

    fn visit_cond(&mut self, cond: &Sp<ast::Cond>) {
        if let Err(e) = self.check_cond(cond) {
            self.errors.set(e);
        }
    }
}

impl Visitor<'_, '_> {
    fn check_stmt_assignment(
        &self,
        var: &Sp<ast::Var>,
        op: Sp<ast::AssignOpKind>,
        value: &Sp<ast::Expr>,
    ) -> ImplResult {
        let var_ty = self.check_var(var);
        let value_ty = self.check_expr_as_value(value, op.span);
        let (var_ty, value_ty) = (var_ty?, value_ty?);

        match op.value {
            ast::AssignOpKind::Assign => {
                self.require_same((var_ty, value_ty), op.span, (var.span, value.span))?;
                Ok(())
            },
            _ => {
                let binop = op.corresponding_binop().expect("only Assign has no binop");
                self.binop_check(sp!(op.span => binop), (var_ty, value_ty), (var.span, value.span))
            },
        }
    }

    fn check_stmt_expr(
        &self,
        expr: &Sp<ast::Expr>,
    ) -> ImplResult {
        let ty = self.check_expr(expr)?;
        self.require_void(ty, expr.span, "expression statements must be of void type")
    }

    fn check_stmt_times(
        &self,
        clobber: &Option<Sp<ast::Var>>,
        count: &Sp<ast::Expr>,
    ) -> ImplResult {
        let count_ty = self.check_expr_as_value(count, count.span)?;
        self.require_int(count_ty, count.span, count.span)?;

        if let Some(clobber) = clobber {
            let clobber_ty = self.check_var(clobber)?;
            self.require_same((clobber_ty, count_ty), count.span, (clobber.span, count.span))?;
        }
        Ok(())
    }

    fn check_stmt_return(
        &mut self,
        return_keyword: ast::TokenSpan,
        expr: &Option<Sp<ast::Expr>>,
    ) -> ImplResult {
        let mut func_state = self.cur_func_stack.last_mut().expect("return outside of function?!");
        func_state.missing_return = false;

        let func_def_id = func_state.func_def_id;
        let siggy = self.ctx.defs.func_signature(func_def_id).expect("must succeed since not an ins alias");
        let (expr_ty, expr_span) = match expr {
            None => (ExprType::Void, return_keyword.span),
            Some(value) => {
                let expr_ty = self.check_expr(value)?;
                // this restriction could be lifted to allow `return void_fn();` in a `void` function
                // but we'll need to carefully test all lowerers to make sure they don't panic
                let value_ty = self.require_value(expr_ty, return_keyword.span, value.span)?;
                (ExprType::Value(value_ty), value.span)
            },
        };

        self._require_exact_expr(expr_ty, siggy.return_ty.value, siggy.return_ty.span, expr_span)
    }

    fn check_stmt_declaration(
        &self,
        keyword: Sp<TypeKeyword>,
        vars: &[Sp<(Sp<ast::Var>, Option<Sp<ast::Expr>>)>],
    ) -> ImplResult {
        vars.iter().map(|sp_pat!((var, value))| {
            self.check_single_var_decl(keyword, var, value.as_ref())
        }).collect_with_recovery()
    }

    fn check_cond(&self, cond: &Sp<ast::Cond>) -> ImplResult {
        let ty = match &cond.value {
            ast::Cond::PreDecrement(var) => self.check_var(var)?,
            ast::Cond::Expr(expr) => self.check_expr_as_value(expr, expr.span)?,
        };
        self.require_int(ty, cond.span, cond.span)
    }

    /// Fully checks a variable declaration or a function parameter declaration.
    fn check_single_var_decl(
        &self,
        keyword: Sp<TypeKeyword>,
        var: &Sp<ast::Var>,
        value: Option<&Sp<ast::Expr>>,
    ) -> ImplResult {
        self.check_var_weak(var)?;

        // forbid 'int %x;'
        if let VarType::Typed(decl_ty) = keyword.var_ty() {
            let var_ty = self.ctx.var_read_ty_from_ast(var).as_known_ty().expect("var is typed");
            self._require_exact(decl_ty, var_ty, keyword.span, var.span)?;
        }

        // is a value being assigned?
        if let Some(value) = value {
            let var_ty = self.check_var(var)?;
            let value_ty = self.check_expr(value)?;
            let value_ty = self.require_value(value_ty, value.span, value.span)?;
            self._require_exact(value_ty, var_ty, keyword.span, value.span)?;
        }
        Ok(())
    }
}

impl ExprTypeChecker<'_, '_> {
    fn emit(&self, err: impl crate::diagnostic::IntoDiagnostics) -> ErrorReported {
        self.ctx.emitter.emit(err)
    }

    /// Fully check an expression and all subexpressions, and return the type.
    ///
    /// (`None` for a `void` (unit) type).
    fn check_expr(&self, expr: &Sp<ast::Expr>) -> ImplResult<ExprType> {
        let out = match expr.value {
            ast::Expr::LitFloat { .. } => ExprType::Value(ScalarType::Float),
            ast::Expr::LitInt { .. } => ExprType::Value(ScalarType::Int),
            ast::Expr::LitString { .. } => ExprType::Value(ScalarType::String),

            ast::Expr::Var(ref var)
            => ExprType::Value(self.check_var(var)?),

            ast::Expr::EnumConst { .. }
            => ExprType::Value(ScalarType::Int),

            ast::Expr::BinOp(ref a, op, ref b)
            => {
                let a_ty = self.check_expr_as_value(a, op.span);
                let b_ty = self.check_expr_as_value(b, op.span);

                self.binop_check(op, (a_ty?, b_ty?), (a.span, b.span))?;
                ExprType::Value(ast::Expr::binop_ty(op.value, &a.value, self.ctx))
            },

            ast::Expr::UnOp(op, ref x)
            => {
                let x_ty = self.check_expr_as_value(x, op.span)?;

                self.unop_check(op, x_ty, x.span)?;
                ExprType::Value(ast::Expr::unop_ty(op.value, &x.value, self.ctx))
            },

            ast::Expr::Ternary { ref cond, question, ref left, colon, ref right }
            => {
                let left_ty = self.check_expr_as_value(left, question.span);
                let right_ty = self.check_expr_as_value(right, colon.span);
                let cond_ty = self.check_expr_as_value(cond, colon.span);

                self.require_int(cond_ty?, question.span, cond.span)?;
                self.require_same((left_ty?, right_ty?), colon.span, (left.span, right.span))?;
                ExprType::Value(left_ty?)
            },

            ast::Expr::DiffSwitch(ref cases)
            => {
                let first = cases[0].as_ref().expect("empty first woulda been parse error");
                let first_ty = self.check_expr_as_value(first, expr.span);

                for other in &cases[1..] {
                    if let Some(other) = other {
                        let other_ty = self.check_expr_as_value(other, expr.span);
                        self.require_same((first_ty?, other_ty?), expr.span, (first.span, other.span))?;
                    }
                }
                ExprType::Value(first_ty?)
            },

            ast::Expr::LabelProperty { keyword: _, label: _ }
            => ExprType::Value(ScalarType::Int),

            ast::Expr::Call(ref call)
            => self.check_expr_call(call)?,
        };

        // Most code after this will be using compute_ty, which has a separate implementation.
        // Let's check that it produces consistent results.
        debug_assert_eq!(out, expr.compute_ty(self.ctx));
        Ok(out)
    }

    fn check_expr_as_value(&self, expr: &Sp<ast::Expr>, value_reason: Span) -> ImplResult<ScalarType> {
        let expr_ty = self.check_expr(expr)?;
        self.require_value(expr_ty, value_reason, expr.span)
    }

    /// Weaker version of [`Self::check_var`] that applies even in places where the variable is neither read
    /// nor written, such as in `int x;`.
    ///
    /// NOTE: while sigils aren't currently allowed in declarations, they could be in the future.
    fn check_var_weak(&self, var: &Sp<ast::Var>) -> ImplResult {
        let inherent_ty = self.ctx.var_inherent_ty_from_ast(var);
        let read_ty = var.ty_sigil;
        match inherent_ty {
            // no restrictions on these
            | VarType::Untyped
            | VarType::Typed(ScalarType::Int)
            | VarType::Typed(ScalarType::Float)
            => {},

            // these can't have sigils
            | VarType::Typed(own_ty@ScalarType::String)
            => match read_ty {
                None => {},  // good; no sigil
                Some(read_ty) => return Err(self.emit(error!(
                    message("type error"),
                    primary(var, "cannot cast {} to {}", own_ty.descr(), ScalarType::from(read_ty).descr()),
                ))),
            }
        };
        Ok(())
    }

    /// Check a variable that's actually being used in some way (read or written to).
    fn check_var(&self, var: &Sp<ast::Var>) -> ImplResult<ScalarType> {
        self.check_var_weak(var)?;

        self.ctx.var_read_ty_from_ast(var).as_known_ty().ok_or_else(|| {
            let mut err = error!(
                message("variable requires a type prefix"),
                primary(var, "needs a '$' or '%' prefix"),
            );
            match self.ctx.var_reg_from_ast(&var.name) {
                Err(_) => err.note(format!("consider adding an explicit type to its declaration")),
                Ok((lang, reg)) => err.note(
                    if self.ctx.defs.reg_inherent_ty(lang, reg).is_some() {
                        format!("{reg} is explicitly untyped in your mapfile")
                    } else {
                        format!("consider adding {reg} to !gvar_types in your mapfile")
                    }
                ),
            };
            self.emit(err)
        })
    }

    /// Check a function call, and get its return type.
    fn check_expr_call(
        &self,
        call: &ast::ExprCall,
    ) -> ImplResult<ExprType> {
        let ast::ExprCall { name, pseudos, args } = call;

        // type check pseudos
        pseudos.iter().map(|pseudo| {
            let ast::PseudoArg { kind, ref value, at_sign: _, eq_sign: _ } = pseudo.value;
            let value_ty = self.check_expr_as_value(value, pseudo.tag_span())?;
            self.pseudo_check(kind, value_ty, value.span)
        }).collect_with_recovery()?;

        // Only instruction-like calls are allowed to have pseudo-args
        if self.ctx.func_opcode_from_ast(&call.name).is_err() {
            if let Some(pseudo) = call.pseudos.get(0) {
                return Err(self.emit(error!(
                    message("forbidden pseudo-arg in function call"),
                    primary(pseudo, ""),
                    secondary(&call.name, "not an instruction"),
                )));
            }
        }

        // '@blob=' is incompatible with normal args
        if let Some(pseudo) = call.blob() {
            if let Some(normal_arg) = args.get(0) {
                return Err(self.emit(error!(
                    message("cannot supply both normal arguments and an args blob"),
                    primary(normal_arg, "redundant normal argument"),
                    secondary(&pseudo.value.value, "represents all args"),
                )));
            }

            // Since there are no normal args to type check, we are done.
            return Ok(ExprType::Void);  // always void when providing a blob
        }

        // Type-check normal args.
        let siggy = match self.ctx.func_signature_from_ast(name) {
            Ok(siggy) => siggy,
            Err(crate::context::defs::InsMissingSigError { opcode, language }) => return Err(self.emit(error!(
                message("signature not known for {} opcode {}", language.descr(), opcode),
                primary(name, "signature not known"),
                note("try adding this instruction's signature to your mapfiles"),
            ))),
        };

        let (min_args, max_args) = (siggy.min_args(), siggy.max_args());
        if !(min_args <= args.len() && args.len() <= max_args) {
            let range_str = match min_args == max_args {
                true => format!("{}", min_args),
                false => format!("{} to {}", min_args, max_args),
            };
            return Err(self.emit(error!(
                message("wrong number of arguments to '{}'", name),
                primary(name, "expects {} arguments, got {}", range_str, args.len()),
            )));
        }

        zip!(1.., args, &siggy.params).map(|(param_num, arg, param)| {
            let arg_ty = self.check_expr_as_value(arg, name.span)?;
            if let VarType::Typed(param_ty) = param.ty.value {
                if arg_ty != param_ty {
                    return Err(self.emit(error!(
                        message("type error"),
                        primary(arg.span, "{}", arg_ty.descr()),
                        secondary(name, "expects {} for parameter {}", param_ty.descr(), param_num),
                    )));
                }
            }
            Ok(())
        }).collect_with_recovery()?;

        args.iter().map(|arg| self.check_expr(arg).map(|_| ())).collect_with_recovery()?;

        Ok(siggy.return_ty.value)
    }
}

impl ast::Expr {
    // NOTE: The difference between this and `check_expr` is that `check_expr` actually performs
    // checks.  Think of it as: `check_expr` is the costly, thorough check (performed once) which
    // ensures that the output of `compute_ty` (which can be called many times) is valid.
    //
    /// Determine the type of this expression.  Returns `None` for `void`-typed expressions.
    ///
    /// Requires name resolution.
    ///
    /// This may need to recurse into subexpressions, though it tries to generally do minimal work.
    /// It assumes that the expression has already been type-checked.  When provided an invalid
    /// expression, it may return anything.
    pub fn compute_ty(&self, ctx: &CompilerContext) -> ExprType {
        match self {
            ast::Expr::LitFloat { .. } => ExprType::Value(ScalarType::Float),
            ast::Expr::LitInt { .. } => ExprType::Value(ScalarType::Int),
            ast::Expr::LitString { .. } => ExprType::Value(ScalarType::String),

            ast::Expr::EnumConst { .. }
            => ExprType::Value(ScalarType::Int),

            ast::Expr::Var(ref var)
            => ExprType::Value(ctx.var_read_ty_from_ast(var).as_known_ty().expect("already type-checked")),

            ast::Expr::BinOp(ref a, op, _)
            => ExprType::Value(ast::Expr::binop_ty(op.value, &a.value, ctx)),

            ast::Expr::UnOp(op, ref x)
            => ExprType::Value(ast::Expr::unop_ty(op.value, &x.value, ctx)),

            ast::Expr::Ternary { ref left, .. }
            => left.compute_ty(ctx),

            ast::Expr::DiffSwitch(ref cases)
            => cases[0].as_ref().expect("empty first woulda been parse error").compute_ty(ctx),

            ast::Expr::LabelProperty { .. }
            => ExprType::Value(ScalarType::Int),

            ast::Expr::Call(call) => {
                if call.blob().is_some() {
                    ExprType::Void  // args blob always produces void
                } else {
                    ctx.func_signature_from_ast(&call.name).expect("already type-checked")
                        .return_ty.value
                }
            },
        }
    }
}

impl ExprTypeChecker<'_, '_> {
    fn binop_check(&self, op: Sp<ast::BinOpKind>, arg_tys: (ScalarType, ScalarType), arg_spans: (Span, Span)) -> ImplResult {
        match op.class() {
            | ast::OpClass::Arithmetic
            => self.require_numeric(arg_tys.0, op.span, arg_spans.0)?,

            | ast::OpClass::Comparison
            => self.require_numeric(arg_tys.0, op.span, arg_spans.0)?,

            | ast::OpClass::Bitwise
            | ast::OpClass::Logical
            | ast::OpClass::Shift
            => self.require_int(arg_tys.0, op.span, arg_spans.0)?,

            _ => unreachable!(),
        };

        // (we do this AFTER the other check because that yields more sensible errors; e.g.
        //  `"lol" - 3` should complain about the string, not about the type mismatch)
        self.require_same(arg_tys, op.span, arg_spans)?;
        Ok(())
    }
}

impl ast::Expr {
    /// Static function for computing the output type of a binary operator expression,
    /// given at least one of its arguments.
    ///
    /// Requires name resolution.
    ///
    /// This assumes that the expression has already been type-checked.  When provided an
    /// invalid combination of operator and arguments, it may return anything.
    pub fn binop_ty(op: ast::BinOpKind, arg: &ast::Expr, ctx: &CompilerContext) -> ScalarType {
        Self::_binop_ty(op, || arg.compute_ty(ctx).as_value_ty().expect("shouldn't be void"))
    }

    pub fn binop_ty_from_arg_ty(op: ast::BinOpKind, arg_ty: ScalarType) -> ScalarType {
        Self::_binop_ty(op, || arg_ty)
    }

    fn _binop_ty(op: ast::BinOpKind, compute_arg_ty: impl Fn() -> ScalarType) -> ScalarType {
        match op.class() {
            | ast::OpClass::Arithmetic
            => compute_arg_ty(),

            | ast::OpClass::Comparison
            => ScalarType::Int,

            | ast::OpClass::Bitwise
            | ast::OpClass::Logical
            | ast::OpClass::Shift
            => ScalarType::Int,

            _ => unreachable!(),
        }
    }
}

impl ExprTypeChecker<'_, '_> {
    fn unop_check(&self, op: Sp<ast::UnOpKind>, arg_ty: ScalarType, arg_span: Span) -> ImplResult {
        match op.value {
            | token![unop -]
            | token![unop $]
            | token![unop %]
            | token![unop int]
            | token![unop float]
            => self.require_numeric(arg_ty, op.span, arg_span),

            | token![unop !]
            | token![unop ~]
            => self.require_int(arg_ty, op.span, arg_span),

            | token![unop sin]
            | token![unop cos]
            | token![unop sqrt]
            => self.require_float(arg_ty, op.span, arg_span),
        }
    }
}

impl ast::Expr {
    /// Static function for computing the output type of a unary operator expression.
    ///
    /// Requires name resolution.
    ///
    /// This assumes that the expression has already been type-checked.  When provided an
    /// invalid combination of operator and arguments, it may return anything.
    pub fn unop_ty(op: ast::UnOpKind, arg: &ast::Expr, ctx: &CompilerContext) -> ScalarType {
        Self::_unop_ty(op, || arg.compute_ty(ctx).as_value_ty().expect("shouldn't be void"))
    }

    pub fn unop_ty_from_arg_ty(op: ast::UnOpKind, arg_ty: ScalarType) -> ScalarType {
        Self::_unop_ty(op, || arg_ty)
    }

    fn _unop_ty(op: ast::UnOpKind, compute_arg_ty: impl Fn() -> ScalarType) -> ScalarType {
        match op {
            token![unop -] => compute_arg_ty(),
            token![unop !] => ScalarType::Int,
            token![unop ~] => ScalarType::Int,

            token![unop sin] |
            token![unop cos] |
            token![unop sqrt] => ScalarType::Float,

            token![unop $] => ScalarType::Int,
            token![unop %] => ScalarType::Float,

            token![unop int] => ScalarType::Int,
            token![unop float] => ScalarType::Float,
        }
    }
}

impl ExprTypeChecker<'_, '_> {
    fn pseudo_check(&self, kind: Sp<ast::PseudoArgKind>, value_ty: ScalarType, value_span: Span) -> ImplResult {
        match kind.value {
            token![pop] |
            token![arg0] |
            token![mask] => self.require_int(value_ty, kind.span, value_span),
            token![blob] => self.require_string(value_ty, kind.span, value_span),
        }
    }
}

// =============================================================================

impl ExprTypeChecker<'_, '_> {
    fn perform_shallow_type_check(&self, check: &ShallowTypeCheck, ctx: &CompilerContext) -> ImplResult {
        let &ShallowTypeCheck { ref expr, ty: expected_ty, cause } = check;
        let actual_ty = expr.compute_ty(ctx);
        let cause = cause.unwrap_or(expr.span);
        match expected_ty {
            ExprType::Void => self.require_void(actual_ty, expr.span, "expected void type"),
            ExprType::Value(expected_ty) => {
                let actual_ty = self.require_value(actual_ty, cause, expr.span)?;
                self._require_exact(actual_ty, expected_ty, cause, expr.span)
            },
        }
    }
}

// =============================================================================

impl ExprTypeChecker<'_, '_> {
    fn require_same(&self, types: (ScalarType, ScalarType), cause: Span, spans: (Span, Span)) -> ImplResult<ScalarType> {
        if types.0 == types.1 {
            Ok(types.0)
        } else {
            let mut error = error!(
                message("type error"),
                secondary(spans.0, "{}", types.0.descr()),
                primary(spans.1, "{}", types.1.descr()),
            );

            // NOTE: In various places in this module you'll see checks on span equality.
            //
            // This is because it is commonplace during code transformations (e.g. macro expansions)
            // to reuse a single span for many things.
            if cause != spans.0 && cause != spans.1 {
                error.secondary(cause, format!("same types required by this"));
            }
            Err(self.emit(error))
        }
    }

    fn require_int(&self, ty: ScalarType, cause: Span, value_span: Span) -> ImplResult {
        self._require_exact(ty, ScalarType::Int, cause, value_span)
    }

    fn require_float(&self, ty: ScalarType, cause: Span, value_span: Span) -> ImplResult {
        self._require_exact(ty, ScalarType::Float, cause, value_span)
    }

    fn require_string(&self, ty: ScalarType, cause: Span, value_span: Span) -> ImplResult {
        self._require_exact(ty, ScalarType::String, cause, value_span)
    }

    fn _require_exact(&self, ty: ScalarType, expected: ScalarType, cause: Span, value_span: Span) -> ImplResult {
        self._require_exact_expr(ty.into(), expected.into(), cause, value_span)
    }

    fn _require_exact_expr(&self, ty: ExprType, expected: ExprType, cause: Span, value_span: Span) -> ImplResult {
        if ty == expected {
            Ok(())
        } else {
            let mut error = error!(
                message("type error"),
                primary(value_span, "{}", ty.descr()),
            );
            if cause == value_span {
                error.note(format!("{} is required", expected.descr()));
            } else {
                error.secondary(cause, format!("expects {}", expected.descr()));
            }
            Err(self.emit(error))
        }
    }

    /// Require int or float.
    fn require_numeric(&self, ty: ScalarType, cause: Span, value_span: Span) -> ImplResult {
        match ty {
            ScalarType::Int => Ok(()),
            ScalarType::Float => Ok(()),
            _ => {
                let mut error = error!(
                    message("type error"),
                    primary(value_span, "{}", ty.descr()),
                );
                if cause == value_span {
                    error.note(format!("a numeric type is required"));
                } else {
                    error.secondary(cause, format!("requires a numeric type"));
                }
                Err(self.emit(error))
            },
        }
    }

    /// Reject void types.
    fn require_value(&self, ty: ExprType, cause: Span, span: Span) -> ImplResult<ScalarType> {
        ty.as_value_ty().ok_or_else(|| {
            let mut error = error!(
                message("type error"),
                primary(span, "void type"),
            );
            if cause != span {
                error.secondary(cause, format!("expects a value"));
            }
            self.emit(error)
        })
    }

    fn require_void(&self, ty: ExprType, span: Span, note: &str) -> ImplResult {
        match ty {
            ExprType::Value(ty) => Err(self.emit(error!(
                message("type error"),
                primary(span, "{}", ty.descr()),
                note("{}", note),
            ))),
            ExprType::Void => Ok(()),
        }
    }
}
