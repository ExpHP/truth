//! Constant expression simplification pass.
//!
//! This pass identifies expressions in the AST that can be evaluated at compile-time and simplifies
//! them.  Expressions that cannot be simplified (e.g. calls of non-`const` functions or use of
//! non-`const` variables) will be left as-is.
//!
//! This is a crucial part of STD compilation, as STD has no mechanism for using variables at
//! runtime.  For other formats, it is moreso just an optimization.
//!
//! # Requirements
//!
//! * Expects that [type checking][`crate::passes::type_check`] has already been performed,
//!   and may panic or misbehave if a type error is encountered.
//! * Expects that [const vars have been evaluated][`crate::passes::evaluate_const_vars`].
//!
//! # Example
//! ```
//! use truth::{ast, pos::{Files, Sp}};
//! use truth::passes;
//!
//! let mut scope = truth::Builder::new().build();
//! let mut truth = scope.truth();
//!
//! let text = b"(3 == 3) ? (3.0 + 0.5) * %REG[100] : 4.0";
//! let mut expr: Sp<ast::Expr> = truth.parse("<input>", text).unwrap();
//!
//! passes::const_simplify::run(&mut expr, truth.ctx()).expect("failed to simplify");
//!
//! let text_simplified = b"3.5 * %REG[100]";
//! let expected: Sp<ast::Expr> = truth.parse("<input>", text_simplified).unwrap();
//! assert_eq!(expr, expected);
//! ```

use crate::value::ScalarValue;
use crate::ast;
use crate::error::{ErrorReported, ErrorFlag, GatherErrorIteratorExt};
use crate::pos::Sp;
use crate::context::CompilerContext;

#[track_caller]
fn uncaught_type_error() -> ! {
    panic!("(bug!) type_check should fail...")
}

impl ast::UnOpKind {
    pub fn const_eval(&self, b: ScalarValue) -> ScalarValue {
        match b {
            ScalarValue::Int(x) => match self {
                token![unop -] => ScalarValue::Int(i32::wrapping_neg(x)),
                token![unop !] => ScalarValue::Int((x == 0) as i32),
                token![unop sin] |
                token![unop cos] |
                token![unop sqrt] => uncaught_type_error(),
                token![unop _S] => uncaught_type_error(),
                token![unop _f] => ScalarValue::Float(x as f32),
            },

            ScalarValue::Float(x) => match self {
                token![unop -] => ScalarValue::Float(-x),
                token![unop !] => uncaught_type_error(),
                token![unop sin] => ScalarValue::Float(x.sin()),
                token![unop cos] => ScalarValue::Float(x.cos()),
                token![unop sqrt] => ScalarValue::Float(x.sqrt()),
                token![unop _S] => ScalarValue::Int(x as i32),
                token![unop _f] => uncaught_type_error(),
            },

            ScalarValue::String(_) => uncaught_type_error(),
        }
    }
}

impl ast::BinOpKind {
    pub fn const_eval(&self, a: ScalarValue, b: ScalarValue) -> ScalarValue {
        match (a, b) {
            (ScalarValue::Int(a), ScalarValue::Int(b)) => match self {
                token![binop +] => ScalarValue::Int(i32::wrapping_add(a, b)),
                token![binop -] => ScalarValue::Int(i32::wrapping_sub(a, b)),
                token![binop *] => ScalarValue::Int(i32::wrapping_mul(a, b)),
                token![binop /] => ScalarValue::Int(i32::wrapping_div(a, b)),
                token![binop %] => ScalarValue::Int(i32::wrapping_rem(a, b)),
                token![binop ==] => ScalarValue::Int((a == b) as i32),
                token![binop !=] => ScalarValue::Int((a != b) as i32),
                token![binop <] => ScalarValue::Int((a < b) as i32),
                token![binop <=] =>ScalarValue::Int( (a <= b) as i32),
                token![binop >] => ScalarValue::Int((a > b) as i32),
                token![binop >=] =>ScalarValue::Int( (a >= b) as i32),
                token![binop ||] => ScalarValue::Int(if a == 0 { b } else { a }),
                token![binop &&] => ScalarValue::Int(if a == 0 { 0 } else { b }),
                token![binop ^] => ScalarValue::Int(a ^ b),
                token![binop &] => ScalarValue::Int(a & b),
                token![binop |] => ScalarValue::Int(a | b),
                token![binop <<] => ScalarValue::Int(a << handle_shift_rhs(b)),
                token![binop >>] => ScalarValue::Int(a >> handle_shift_rhs(b)),
                token![binop >>>] => ScalarValue::Int((a as u32 >> handle_shift_rhs(b)) as i32),
            },

            (ScalarValue::Float(a), ScalarValue::Float(b)) => match self {
                token![binop +] => ScalarValue::Float(a + b),
                token![binop -] => ScalarValue::Float(a - b),
                token![binop *] => ScalarValue::Float(a * b),
                token![binop /] => ScalarValue::Float(a / b),
                token![binop %] => ScalarValue::Float(a % b),
                token![binop ==] => ScalarValue::Int((a == b) as i32),
                token![binop !=] => ScalarValue::Int((a != b) as i32),
                token![binop <] => ScalarValue::Int((a < b) as i32),
                token![binop <=] => ScalarValue::Int((a <= b) as i32),
                token![binop >] => ScalarValue::Int((a > b) as i32),
                token![binop >=] => ScalarValue::Int((a >= b) as i32),
                token![binop ||] => uncaught_type_error(),
                token![binop &&] => uncaught_type_error(),
                token![binop ^] => uncaught_type_error(),
                token![binop &] => uncaught_type_error(),
                token![binop |] => uncaught_type_error(),
                token![binop <<] => uncaught_type_error(),
                token![binop >>] => uncaught_type_error(),
                token![binop >>>] => uncaught_type_error(),
            },

            _ => uncaught_type_error(),
        }
    }
}

fn handle_shift_rhs(x: i32) -> u32 {
    // FIXME: we would ideally warn on x out of range but it's hard to get an emitter here...
    //        (also it might warn multiple times)
    x as u32 % u32::BITS
}

impl ast::Expr {
    /// Get the expression's value, if it is an integer literal.
    ///
    /// Because const simplification turns expressions into literals, this is the quickest way to
    /// inspect the final, evaluated result of a constant integer expression.
    pub fn as_const_int(&self) -> Option<i32> { match *self {
        ast::Expr::LitInt { value, .. } => Some(value),
        _ => None,
    }}

    /// Get the expression's value, if it is a float literal.
    ///
    /// Because const simplification turns expressions into literals, this is the quickest way to
    /// inspect the final, evaluated result of a constant float expression.
    pub fn as_const_float(&self) -> Option<f32> { match *self {
        ast::Expr::LitFloat { value, .. } => Some(value),
        _ => None,
    }}

    /// Get the expression's value, if it is a string literal.
    ///
    /// Because const simplification turns expressions into literals, this is the quickest way to
    /// inspect the final, evaluated result of a constant float expression.
    pub fn as_const_str(&self) -> Option<&str> { match self {
        ast::Expr::LitString(ast::LitString { string, .. }) => Some(string),
        _ => None,
    }}

    /// Get the expression's value, if it is a literal.
    ///
    /// Because const simplification turns expressions into literals, this is the quickest way to
    /// inspect the final, evaluated result of a constant expression.
    pub fn to_const(&self) -> Option<ScalarValue> { match *self {
        ast::Expr::LitInt { value, .. } => Some(ScalarValue::Int(value)),
        ast::Expr::LitFloat { value, .. } => Some(ScalarValue::Float(value)),
        ast::Expr::LitString(ast::LitString { ref string, .. }) => Some(ScalarValue::String(string.clone())),
        _ => None,
    }}
}

/// Performs const simplification.
///
/// See the [the module-level documentation][self] for more details.
pub fn run<V: ast::Visitable>(ast: &mut V, ctx: &CompilerContext) -> Result<(), ErrorReported> {
    let mut visitor = Visitor { errors: ErrorFlag::new(), ctx };
    ast.visit_mut_with(&mut visitor);
    visitor.errors.into_result(())
}

struct Visitor<'a, 'ctx> {
    ctx: &'a CompilerContext<'ctx>,
    errors: ErrorFlag,
}

impl ast::VisitMut for Visitor<'_, '_> {
    // !!! IMPORTANT !!!
    // This function must be updated in sync with the DFS const evaluator.
    // (it did not seem possible to factor the shared logic out...)
    fn visit_expr(&mut self, e: &mut Sp<ast::Expr>) {
        // simplify subexpressions first
        ast::walk_expr_mut(self, e);

        // now inspect this expression
        match &e.value {
            ast::Expr::Var(var) => match var.name {
                ast::VarName::Normal { ref ident, .. } => {
                    let def_id = self.ctx.resolutions.expect_def(ident);
                    if let Some(value) = self.ctx.consts.get_cached_value(def_id.into()) {
                        e.value = value.clone().apply_sigil(var.ty_sigil).expect("shoulda been type-checked").into();
                    }
                },
                ast::VarName::Reg { .. } => {}, // can't simplify register
            },

            ast::Expr::EnumConst { ident, .. } => {
                let def_id = self.ctx.resolutions.expect_def(ident);
                if let Some(value) = self.ctx.consts.get_cached_value(def_id.into()) {
                    e.value = value.clone().into();
                }
            },

            ast::Expr::UnOp(op, b) => {
                if let Some(b_value) = b.to_const() {
                    e.value = op.const_eval(b_value).into();
                }
            },

            ast::Expr::BinOp(a, op, b) => {
                if let (Some(a_value), Some(b_value)) = (a.to_const(), b.to_const()) {
                    e.value = op.const_eval(a_value, b_value).into();
                };
            },

            ast::Expr::Ternary { cond, left, right, .. } => match cond.to_const() {
                // FIXME it should be possible to move somehow instead of cloning here...
                Some(ScalarValue::Int(0)) => e.value = (***right).clone(),
                Some(ScalarValue::Int(_)) => e.value = (***left).clone(),
                Some(_) => uncaught_type_error(),
                _ => return, // can't simplify if subexpr is not const
            },

            ast::Expr::Call(call) => {
                // FIXME is this the right place to do this?
                validate_call_const_args(call, self.ctx).unwrap_or_else(|e| self.errors.set(e));
            },

            _ => return, // can't simplify other expressions
        }
    }
}

fn validate_call_const_args(call: &ast::ExprCall, ctx: &CompilerContext<'_>) -> Result<(), ErrorReported> {
    use crate::context::defs::{MatchedArgs, ConstArgReason};

    if !call.actually_has_args() {
        return Ok(());
    }

    let siggy = ctx.func_signature_from_ast(&call.name).expect("already type-checked");
    let MatchedArgs { positional_pairs } = siggy.match_params_to_args(&call.args);

    positional_pairs.map(|(param, arg)| {
        if let Some(const_arg_reason) = &param.const_arg_reason {
            // FIXME: I don't think this condition will work well for inline funcs?
            //        But we need to allow offsetof and timeof...
            if !arg.can_lower_to_immediate() {
                let mut diag = error!(
                    message("argument must be a compile-time constant"),
                    primary(arg, "not constant"),
                );

                match const_arg_reason {
                    ConstArgReason::Encoding(enc) => diag.note(format!("because the argument is a {}", enc.descr())),
                    ConstArgReason::EosdEcl => diag.note(format!("this is a limitation of calls in EoSD ECL")),
                };
                return Err(ctx.emitter.emit(diag));
            }
        }
        Ok(())
    }).collect_with_recovery()
}
