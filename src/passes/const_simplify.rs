//! Constant expression simplification pass.
//!
//! This pass identifies expressions in the AST that can be evaluated at compile-time and simplifies
//! them.  Expressions that cannot be simplified (e.g. calls of non-const functions or use of
//! non-const variables) will be left as-is.
//!
//! This is a crucial part of STD compilation, as STD has no mechanism for using variables at
//! runtime.  For other formats, it is moreso just an optimization.
//!
//! This pass expects that [type checking](`crate::passes::type_check`) has already been performed,
//! and may panic or misbehave if a type error is encountered.
//!
//! # Example
//! ```
//! use truth::{ast, pos::{Files, Sp}};
//! use truth::passes::const_simplify;
//!
//! let mut files = Files::new();
//!
//! let text = b"(3 == 3) ? (3.0 + 0.5) * x : 4";
//! let mut expr: Sp<ast::Expr> = files.parse("<input>", text).unwrap();
//!
//! const_simplify::run(&mut expr).expect("failed to simplify");
//!
//! let text_simplified = b"3.5 * x";
//! let expected: Sp<ast::Expr> = files.parse("<input>", text_simplified).unwrap();
//! assert_eq!(expr, expected);
//! ```

use crate::value::ScalarValue;
use crate::ast::{self, VisitMut, UnopKind, BinopKind, Expr};
use crate::error::{CompileError};
use crate::pos::Sp;

#[track_caller]
fn uncaught_type_error() -> ! {
    panic!("(bug!) type_check should fail...")
}

impl UnopKind {
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

impl BinopKind {
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
            },

            _ => uncaught_type_error(),
        }
    }
}

impl Expr {
    /// Get the expression's value, if it is an integer literal.
    ///
    /// Because const simplification turns expressions into literals, this is the quickest way to
    /// inspect the final, evaluated result of a constant integer expression.
    pub fn as_const_int(&self) -> Option<i32> { match *self {
        Expr::LitInt { value, .. } => Some(value),
        _ => None,
    }}

    /// Get the expression's value, if it is a float literal.
    ///
    /// Because const simplification turns expressions into literals, this is the quickest way to
    /// inspect the final, evaluated result of a constant float expression.
    pub fn as_const_float(&self) -> Option<f32> { match *self {
        Expr::LitFloat { value, .. } => Some(value),
        _ => None,
    }}

    /// Get the expression's value, if it is a literal.
    ///
    /// Because const simplification turns expressions into literals, this is the quickest way to
    /// inspect the final, evaluated result of a constant expression.
    pub fn to_const(&self) -> Option<ScalarValue> { match *self {
        Expr::LitInt { value, .. } => Some(ScalarValue::Int(value)),
        Expr::LitFloat { value, .. } => Some(ScalarValue::Float(value)),
        Expr::LitString(ast::LitString { ref string, .. }) => Some(ScalarValue::String(string.clone())),
        _ => None,
    }}
}

/// Performs const simplification.
///
/// See the [the module-level documentation][self] for more details.
pub fn run<V: ast::Visitable>(ast: &mut V) -> Result<(), CompileError> {
    let mut visitor = Visitor { errors: CompileError::new_empty() };
    ast.visit_mut_with(&mut visitor);
    visitor.errors.into_result(())
}

struct Visitor {
    errors: CompileError,
}

impl VisitMut for Visitor {
    fn visit_expr(&mut self, e: &mut Sp<Expr>) {
        // simplify subexpressions first
        ast::walk_expr_mut(self, e);

        // now inspect this expression
        match &e.value {
            Expr::Unop(op, b) => {
                if let Some(b_value) = b.to_const() {
                    e.value = op.const_eval(b_value).into();
                }
            },

            Expr::Binop(a, op, b) => {
                if let (Some(a_value), Some(b_value)) = (a.to_const(), b.to_const()) {
                    e.value = op.const_eval(a_value, b_value).into();
                };
            },

            Expr::Ternary { cond, left, right, .. } => match cond.to_const() {
                // FIXME it should be possible to move somehow instead of cloning here...
                Some(ScalarValue::Int(0)) => e.value = (***right).clone(),
                Some(ScalarValue::Int(_)) => e.value = (***left).clone(),
                Some(_) => uncaught_type_error(),
                _ => return, // can't simplify if subexpr is not const
            },
            _ => return, // can't simplify other expressions
        }
    }
}
