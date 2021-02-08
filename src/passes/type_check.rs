//! Performs type-checking on the whole AST.
//!
//! Requires [name resolution](`crate::passes::resolve_names`).
//!
//! The purpose of this pass is to serve as the answer to the question, "when do we generate an
//! error about this?"  Ideally, all errors that can be classified as type errors are reported
//! to the user during this pass.  Having run this pass, one can feel comfortable simply panicking
//! when bad types are encountered in other passes like lowering.

use crate::ast;
use crate::error::{GatherErrorIteratorExt, CompileError, Diagnostic};
use crate::pos::{Sp, Span};
use crate::type_system::ScalarType;
use crate::type_system::TypeSystem;
use crate::ast::VarDeclKeyword;

/// Performs type-checking.
///
/// See the [the module-level documentation][self] for more details.
pub fn run<A: ast::Visitable>(ast: &A, ty_ctx: &mut TypeSystem) -> Result<(), CompileError> {
    let mut v = Visitor { ty_ctx, errors: CompileError::new_empty() };
    ast.visit_with(&mut v);
    v.errors.into_result(())
}

struct Visitor<'a> {
    ty_ctx: &'a TypeSystem,
    errors: CompileError,
}

impl ast::Visit for Visitor<'_> {
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
            self.errors.append(e);
        }
    }

    fn visit_stmt(&mut self, stmt: &Sp<ast::Stmt>) {
        match &stmt.value.body {
            // statement types where there's nothing additional to check beyond what
            // would already be done by recursively walking the node
            | ast::StmtBody::CondChain { .. }
            | ast::StmtBody::CondJump { .. }
            | ast::StmtBody::While { .. }
            | ast::StmtBody::Jump { .. }
            | ast::StmtBody::Loop { .. } => {
                ast::walk_stmt(self, stmt)
            },

            ast::StmtBody::Return { value, keyword: _ } => {
                if let Some(_) = value {
                    unimplemented!("need to check against current function's signature")
                }
            },

            ast::StmtBody::Assignment { var, op, value } => {
                if let Err(e) = self.check_stmt_assignment(var, *op, value) {
                    self.errors.append(e);
                }
            },

            ast::StmtBody::Expr(expr) => {
                if let Err(e) = self.check_stmt_expr(expr) {
                    self.errors.append(e);
                }
            },

            ast::StmtBody::Times { clobber, count, block, keyword: _ } => {
                if let Err(e) = self.check_stmt_times(clobber, count) {
                    self.errors.append(e);
                }
                ast::walk_block(self, block);
            },

            ast::StmtBody::Declaration { keyword, vars } => {
                if let Err(e) = self.check_stmt_declaration(*keyword, vars) {
                    self.errors.append(e);
                }
            },

            ast::StmtBody::CallSub { .. } => unimplemented!("need to check arg types against signature"),

            ast::StmtBody::InterruptLabel { .. } => {},
            ast::StmtBody::Label { .. } => {},
            ast::StmtBody::ScopeEnd { .. } => {},
            ast::StmtBody::NoInstruction { .. } => {},
        }
    }

    fn visit_goto(&mut self, goto: &ast::StmtGoto) {
        ast::walk_goto(self, goto);

        let ast::StmtGoto { destination, time } = goto;

        // There is the remote possibility that at some point in the future, I may want to change
        // either or both of these into full-fledged expressions (and subject them to const folding).
        //
        // In case that change is ever made, these statements will stop compiling and you will see
        // this comment reminding you to fix this.  ;)
        //
        // (in particular, you need to check that the new expression(s) are of integer type).
        let _: &Option<i32> = time;
        let _: &Sp<crate::ident::Ident> = destination;
    }

    fn visit_cond(&mut self, cond: &Sp<ast::Cond>) {
        if let Err(e) = self.check_cond(cond) {
            self.errors.append(e);
        }
    }
}

impl<'a> Visitor<'a> {
    fn check_stmt_assignment(
        &self,
        var: &Sp<ast::Var>,
        op: Sp<ast::AssignOpKind>,
        value: &Sp<ast::Expr>,
    ) -> Result<(), CompileError> {
        let var_result = self.check_var(var);
        let value_result = self.check_expr(value);
        let (var_ty, value_ty) = CompileError::join(var_result, value_result)?;
        let value_ty = require_value(value_ty, op.span, value.span)?;

        match op.value {
            ast::AssignOpKind::Assign => {
                require_same((var_ty, value_ty), op.span, (var.span, value.span))?;
                Ok(())
            },
            _ => {
                let binop = op.corresponding_binop().expect("only Assign has no binop");
                ast::Expr::binop_check(sp!(op.span => binop), (var_ty, value_ty), (var.span, value.span))
            },
        }
    }

    fn check_stmt_expr(
        &self,
        expr: &Sp<ast::Expr>,
    ) -> Result<(), CompileError> {
        let ty = self.check_expr(expr)?;
        require_void(ty, expr.span, "expression statements must be of void type")
    }

    fn check_stmt_times(
        &self,
        clobber: &Option<Sp<ast::Var>>,
        count: &Sp<ast::Expr>,
    ) -> Result<(), CompileError> {
        let count_ty = self.check_expr(count)?;
        let count_ty = require_value(count_ty, count.span, count.span)?;
        require_int(count_ty, count.span, count.span)?;

        if let Some(clobber) = clobber {
            let clobber_ty = self.check_var(clobber)?;
            require_same((clobber_ty, count_ty), count.span, (clobber.span, count.span))?;
        }
        Ok(())
    }

    fn check_stmt_declaration(
        &self,
        keyword: Sp<VarDeclKeyword>,
        vars: &[Sp<(Sp<ast::Var>, Option<Sp<ast::Expr>>)>],
    ) -> Result<(), CompileError> {
        let decl_ty = match keyword.value {
            ast::VarDeclKeyword::Int => Some(ScalarType::Int),
            ast::VarDeclKeyword::Float => Some(ScalarType::Float),
            ast::VarDeclKeyword::Var => None,
        };

        vars.iter().map(|sp_pat!((var, value))| {
            let var_ty = self.check_var(var)?;

            // forbid `int %x;` even if grammatically accepted
            if let Some(decl_ty) = decl_ty {
                _require_exact(decl_ty, var_ty, keyword.span, var.span)?;
            }
            if let Some(value) = value {
                let value_ty = self.check_expr(value)?;
                let value_ty = require_value(value_ty, value.span, value.span)?;
                _require_exact(value_ty, var_ty, keyword.span, value.span)?;
            }
            Ok::<_, CompileError>(())
        }).collect_with_recovery()
    }

    fn check_cond(&self, cond: &Sp<ast::Cond>) -> Result<(), CompileError> {
        let ty = match &cond.value {
            ast::Cond::PreDecrement(var) => self.check_var(var)?,
            ast::Cond::Expr(expr) => {
                let ty = self.check_expr(expr)?;
                let ty = require_value(ty, expr.span, expr.span)?;
                ty
            }
        };
        require_int(ty, cond.span, cond.span)
    }

    /// Fully check an expression and all subexpressions, and return the type.
    ///
    /// (`None` for a `void` (unit) type).
    fn check_expr(&self, expr: &Sp<ast::Expr>) -> Result<Option<ScalarType>, CompileError> {
        let out = match expr.value {
            ast::Expr::LitFloat { .. } => Some(ScalarType::Float),
            ast::Expr::LitInt { .. } => Some(ScalarType::Int),
            ast::Expr::LitString { .. } => Some(ScalarType::String),

            ast::Expr::Var(ref var)
            => Some(self.check_var(var)?),

            ast::Expr::Binop(ref a, op, ref b)
            => {
                let (a_ty, b_ty) = CompileError::join(self.check_expr(a), self.check_expr(b))?;
                let a_ty = require_value(a_ty, op.span, a.span)?;
                let b_ty = require_value(b_ty, op.span, b.span)?;

                ast::Expr::binop_check(op, (a_ty, b_ty), (a.span, b.span))?;
                Some(ast::Expr::binop_ty(op.value, &a.value, self.ty_ctx))
            },

            ast::Expr::Unop(op, ref x)
            => {
                let x_ty = self.check_expr(x)?;
                let x_ty = require_value(x_ty, op.span, x.span)?;

                ast::Expr::unop_check(op, x_ty, x.span)?;
                Some(ast::Expr::unop_ty(op.value, &x.value, self.ty_ctx))
            },

            ast::Expr::Ternary { ref cond, question, ref left, colon, ref right }
            => {
                let arg_tys = CompileError::join(self.check_expr(left), self.check_expr(right));
                let (cond_ty, (left_ty, right_ty)) = CompileError::join(self.check_expr(cond), arg_tys)?;

                let cond_ty = require_value(cond_ty, question.span, cond.span)?;
                let left_ty = require_value(left_ty, colon.span, left.span)?;
                let right_ty = require_value(right_ty, colon.span, right.span)?;

                require_int(cond_ty, question.span, cond.span)?;
                require_same((left_ty, right_ty), colon.span, (left.span, right.span))?;
                Some(left_ty)
            },

            ast::Expr::Call { ref args, ref ident } => {
                let func_res_id = self.ty_ctx.func_ident_id(ident);
                let siggy = match self.ty_ctx.func_signature(func_res_id) {
                    Ok(siggy) => siggy,
                    Err(crate::type_system::MissingSigError { opcode }) => return Err(error!(
                        message("signature not known for opcode {}", opcode),
                        primary(ident, "signature not known"),
                        note("try adding this instruction's signature to your mapfiles"),
                    )),
                };

                let (min_args, max_args) = (siggy.min_args(), siggy.max_args());
                if !(min_args <= args.len() && args.len() <= max_args) {
                    let range_str = match min_args == max_args {
                        true => format!("{}", min_args),
                        false => format!("{} to {}", min_args, max_args),
                    };
                    return Err(error!(
                        message("wrong number of arguments to '{}'", ident),
                        primary(ident, "expects {} arguments, got {}", range_str, args.len()),
                    ));
                }

                zip!(1.., args, &siggy.params).map(|(param_num, arg, param)| {
                    let arg_ty = self.check_expr(arg)?;
                    let arg_ty = require_value(arg_ty, ident.span, arg.span)?;
                    if arg_ty != param.ty.value {
                        return Err(error!(
                            message("type error"),
                            primary(arg.span, "{}", arg_ty.descr()),
                            secondary(ident, "expects {} for parameter {}", param.ty.descr(), param_num),
                        ));
                    }
                    Ok::<_, CompileError>(())
                }).collect_with_recovery()?;

                // HACK: for now just recurse on the args without validating against signature params
                args.iter().map(|arg| self.check_expr(arg).map(|_| ())).collect_with_recovery()?;

                // all calls are currently void-type
                None
            },
        };

        // Most code after this will be using compute_ty, which has a separate implementation.
        // Let's check that it produces consistent results.
        debug_assert_eq!(out, expr.compute_ty(self.ty_ctx));
        Ok(out)
    }

    /// Get the type that a variable is being used as.
    fn check_var(&self, var: &Sp<ast::Var>) -> Result<ScalarType, CompileError> {
        let inherent_ty = self.ty_ctx.var_inherent_ty_from_ast(var);
        let read_ty = var.read_ty();
        match inherent_ty {
            // no restrictions on these
            | None
            | Some(ScalarType::Int)
            | Some(ScalarType::Float)
            => {},

            // these can't have sigils
            | Some(ScalarType::String)
            => match read_ty {
                None => {},  // good; no sigil
                Some(read_ty) => return Err(error!(
                    message("type error"),
                    primary(var, "attempt to read {} as {}", inherent_ty.unwrap().descr(), ScalarType::from(read_ty).descr()),
                )),
            }
        };

        self.ty_ctx.var_read_ty_from_ast(var).ok_or_else(|| {
            let mut err = crate::error::Diagnostic::error();
            err.message(format!("variable requires a type prefix"));
            err.primary(var, format!("needs a '$' or '%' prefix"));
            match self.ty_ctx.var_reg_from_ast(var) {
                Err(_) => err.note(format!("consider adding an explicit type to its declaration")),
                Ok(reg) => err.note(format!("consider adding {} to !gvar_types in your mapfile", reg)),
            };
            err.into()
        })
    }
}

impl ast::Expr {
    /// Determine the type of this expression.  Returns `None` for `void`-typed expressions.
    ///
    /// Requires name resolution.
    ///
    /// This may need to recurse into subexpressions, though it tries to generally do minimal work.
    /// It assumes that the expression has already been type-checked.  When provided an invalid
    /// expression, it may return anything.
    pub fn compute_ty(&self, ty_ctx: &TypeSystem) -> Option<ScalarType> {
        match self {
            ast::Expr::LitFloat { .. } => Some(ScalarType::Float),
            ast::Expr::LitInt { .. } => Some(ScalarType::Int),
            ast::Expr::LitString { .. } => Some(ScalarType::String),

            ast::Expr::Var(ref var)
            => Some(ty_ctx.var_read_ty_from_ast(var).expect("already type-checked")),

            ast::Expr::Binop(ref a, op, _)
            => Some(ast::Expr::binop_ty(op.value, &a.value, ty_ctx)),

            ast::Expr::Unop(op, ref x)
            => Some(ast::Expr::unop_ty(op.value, &x.value, ty_ctx)),

            ast::Expr::Ternary { ref left, .. }
            => left.compute_ty(ty_ctx),

            ast::Expr::Call { .. } => {
                // FIXME: Type check args!

                // all calls are currently void-type
                None
            },
        }
    }

    fn binop_check(op: Sp<ast::BinopKind>, arg_tys: (ScalarType, ScalarType), arg_spans: (Span, Span)) -> Result<(), CompileError> {
        use ast::BinopKind as B;

        match op.value {
            | B::Add | B::Sub | B::Mul | B::Div | B::Rem
            => require_numeric(arg_tys.0, op.span, arg_spans.0)?,

            | B::Eq | B::Ne | B::Lt | B::Le | B::Gt | B::Ge
            => require_numeric(arg_tys.0, op.span, arg_spans.0)?,

            | B::BitXor | B::BitAnd | B::BitOr
            | B::LogicOr | B::LogicAnd
            => require_int(arg_tys.0, op.span, arg_spans.0)?,
        };

        // (we do this AFTER the other check because that yields more sensible errors; e.g.
        //  `"lol" - 3` should complain about the string, not about the type mismatch)
        require_same(arg_tys, op.span, arg_spans)?;
        Ok(())
    }

    /// Static function for computing the output type of a binary operator expression,
    /// given at least one of its arguments.
    ///
    /// Requires name resolution.
    ///
    /// This assumes that the expression has already been type-checked.  When provided an
    /// invalid combination of operator and arguments, it may return anything.
    pub fn binop_ty(op: ast::BinopKind, arg: &ast::Expr, ty_ctx: &TypeSystem) -> ScalarType {
        use ast::BinopKind as B;

        match op {
            | B::Add | B::Sub | B::Mul | B::Div | B::Rem
            => arg.compute_ty(ty_ctx).expect("shouldn't be void"),

            | B::Eq | B::Ne | B::Lt | B::Le | B::Gt | B::Ge
            => ScalarType::Int,

            | B::BitXor | B::BitAnd | B::BitOr
            | B::LogicOr | B::LogicAnd
            => ScalarType::Int,
        }
    }

    fn unop_check(op: Sp<ast::UnopKind>, arg_ty: ScalarType, arg_span: Span) -> Result<(), CompileError> {
        match op.value {
            token![unop -] => require_numeric(arg_ty, op.span, arg_span),

            token![unop _f] |
            token![unop !] => require_int(arg_ty, op.span, arg_span),

            token![unop _S] |
            token![unop sin] |
            token![unop cos] |
            token![unop sqrt] => require_float(arg_ty, op.span, arg_span),
        }
    }

    /// Static function for computing the output type of a unary operator expression.
    ///
    /// Requires name resolution.
    ///
    /// This assumes that the expression has already been type-checked.  When provided an
    /// invalid combination of operator and arguments, it may return anything.
    pub fn unop_ty(op: ast::UnopKind, arg: &ast::Expr, ty_ctx: &TypeSystem) -> ScalarType {
        match op {
            token![unop -] => arg.compute_ty(ty_ctx).expect("shouldn't be void"),
            token![unop !] => ScalarType::Int,

            token![unop sin] |
            token![unop cos] |
            token![unop sqrt] => ScalarType::Float,

            token![unop _S] => ScalarType::Int,
            token![unop _f] => ScalarType::Float,
        }
    }
}

// =============================================================================

fn require_same(types: (ScalarType, ScalarType), cause: Span, spans: (Span, Span)) -> Result<ScalarType, CompileError> {
    if types.0 == types.1 {
        Ok(types.0)
    } else {
        let mut error = Diagnostic::error();
        error.message(format!("type error"));
        error.primary(spans.1, format!("{}", types.1.descr()));
        error.secondary(spans.0, format!("{}", types.0.descr()));

        // NOTE: In varous places in this module you'll see checks on span equality.
        //
        // This is because it is commonplace during code transformations (e.g. macro expansions)
        // to reuse a single span for many things.
        if cause != spans.0 && cause != spans.1 {
            error.secondary(cause, format!("same types required by this"));
        }
        Err(error.into())
    }
}

fn require_int(ty: ScalarType, cause: Span, value_span: Span) -> Result<(), CompileError> {
    _require_exact(ty, ScalarType::Int, cause, value_span)
}

fn require_float(ty: ScalarType, cause: Span, value_span: Span) -> Result<(), CompileError> {
    _require_exact(ty, ScalarType::Float, cause, value_span)
}

fn _require_exact(ty: ScalarType, expected: ScalarType, cause: Span, value_span: Span) -> Result<(), CompileError> {
    if ty == expected {
        Ok(())
    } else {
        let mut error = Diagnostic::error();
        error.message(format!("type error"));
        error.primary(value_span, format!("{}", ty.descr()));
        if cause == value_span {
            error.note(format!("{} is required", expected.descr()));
        } else {
            error.secondary(cause, format!("expects {}", expected.descr()));
        }
        Err(error.into())
    }
}

/// Require int or float.
fn require_numeric(ty: ScalarType, cause: Span, value_span: Span) -> Result<(), CompileError> {
    match ty {
        ScalarType::Int => Ok(()),
        ScalarType::Float => Ok(()),
        _ => {
            let mut error = Diagnostic::error();
            error.message(format!("type error"));
            error.primary(value_span, format!("{}", ty.descr()));
            if cause == value_span {
                error.note(format!("a numeric type is required"));
            } else {
                error.secondary(cause, format!("requires a numeric type"));
            }
            Err(error.into())
        },
    }
}

/// Reject void types.
fn require_value(ty: Option<ScalarType>, cause: Span, span: Span) -> Result<ScalarType, CompileError> {
    ty.ok_or_else(|| {
        let mut error = Diagnostic::error();
        error.message(format!("type error"));
        error.primary(span, format!("void type"));
        if cause != span {
            error.secondary(cause, format!("expects a value"));
        }
        error.into()
    })
}

fn require_void(ty: Option<ScalarType>, span: Span, note: &str) -> Result<(), CompileError> {
    match ty {
        Some(ty) => Err(error!(
            message("type error"),
            primary(span, "{}", ty.descr()),
            note("{}", note),
        )),
        None => Ok(()),
    }
}
