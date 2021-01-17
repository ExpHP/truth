//! Constant expression simplification pass.
//!
//! This pass identifies expressions in the AST that can be evaluated at compile-time and simplifies
//! them.  Expressions that cannot be simplified (e.g. calls of non-const functions or use of
//! non-const variables) will be left as-is.
//!
//! This is a crucial part of STD compilation, as STD has no mechanism for using variables at
//! runtime.  For other formats, it is moreso just an optimization.
//!
//! Use [`Visitor`]'s implementation of [`VisitMut`] to apply the pass. Call [`Visitor::finish`]
//! at the end to obtain errors; These will mostly be type errors that prevent evaluation of an
//! operation that could otherwise be computed at compile-time.
//!
//! # Example
//! ```
//! use truth::{VisitMut, ast, pos::{Files, Sp}};
//! use truth::passes::const_simplify;
//!
//! let mut files = Files::new();
//!
//! let text = b"(3 == 3) ? (3.0 + 0.5) * x : 4";
//! let mut expr: Sp<ast::Expr> = files.parse("<input>", text).unwrap();
//!
//! let mut visitor = const_simplify::Visitor::new();
//! visitor.visit_expr(&mut expr);
//! visitor.finish().expect("failed to simplify");
//!
//! let text_simplified = b"3.5 * x";
//! let expected: Sp<ast::Expr> = files.parse("<input>", text_simplified).unwrap();
//! assert_eq!(expr, expected);
//! ```

use crate::value::ScalarValue;
use crate::ast::{self, VisitMut, UnopKind, BinopKind, Expr};
use crate::error::{CompileError};
use crate::pos::Sp;

impl Sp<UnopKind> {
    pub fn const_eval(&self, b: Sp<ScalarValue>) -> Result<ScalarValue, CompileError> {
        self.type_check(b.ty(), b.span)?;
        match b.value {
            ScalarValue::Int(b) => Ok(self.const_eval_int(b).expect("(bug!) type_check should fail...")),
            ScalarValue::Float(b) => Ok(self.const_eval_float(b).expect("(bug!) type_check should fail...")),
        }
    }
}

impl UnopKind {
    pub fn const_eval_int(&self, x: i32) -> Option<ScalarValue> {
        match self {
            token![unop -] => Some(ScalarValue::Int(i32::wrapping_neg(x))),
            token![unop !] => Some(ScalarValue::Int((x != 0) as i32)),
            token![unop sin] |
            token![unop cos] |
            token![unop sqrt] => None,
            token![unop _S] => None,
            token![unop _f] => Some(ScalarValue::Float(x as f32)),
        }
    }

    pub fn const_eval_float(&self, x: f32) -> Option<ScalarValue> {
        match self {
            token![unop -] => Some(ScalarValue::Float(-x)),
            token![unop !] => None,
            token![unop sin] => Some(ScalarValue::Float(x.sin())),
            token![unop cos] => Some(ScalarValue::Float(x.cos())),
            token![unop sqrt] => Some(ScalarValue::Float(x.sqrt())),
            token![unop _S] => Some(ScalarValue::Int(x as i32)),
            token![unop _f] => None,
        }
    }
}

impl Sp<BinopKind> {
    pub fn const_eval(&self, a: Sp<ScalarValue>, b: Sp<ScalarValue>) -> Result<ScalarValue, CompileError> {
        self.type_check(a.ty(), b.ty(), (a.span, b.span))?;
        match (a.value, b.value) {
            (ScalarValue::Int(a), ScalarValue::Int(b)) => Ok(ScalarValue::Int(self.const_eval_int(a, b))),
            (ScalarValue::Float(a), ScalarValue::Float(b)) => Ok(self.const_eval_float(a, b).expect("(bug!) type_check should fail...")),
            _ => unreachable!("(bug!) type_check should fail..."),
        }
    }
}

impl BinopKind {
    pub fn const_eval_int(&self, a: i32, b: i32) -> i32 {
        match self {
            token![binop +] => i32::wrapping_add(a, b),
            token![binop -] => i32::wrapping_sub(a, b),
            token![binop *] => i32::wrapping_mul(a, b),
            token![binop /] => i32::wrapping_div(a, b),
            token![binop %] => i32::wrapping_rem(a, b),
            token![binop ==] => (a == b) as i32,
            token![binop !=] => (a != b) as i32,
            token![binop <] => (a < b) as i32,
            token![binop <=] => (a <= b) as i32,
            token![binop >] => (a > b) as i32,
            token![binop >=] => (a >= b) as i32,
            token![binop ||] => if a == 0 { b } else { a },
            token![binop &&] => if a == 0 { 0 } else { b },
            token![binop ^] => a ^ b,
            token![binop &] => a & b,
            token![binop |] => a | b,
        }
    }

    pub fn const_eval_float(&self, a: f32, b: f32) -> Option<ScalarValue> {
        match self {
            token![binop +] => Some(ScalarValue::Float(a + b)),
            token![binop -] => Some(ScalarValue::Float(a - b)),
            token![binop *] => Some(ScalarValue::Float(a * b)),
            token![binop /] => Some(ScalarValue::Float(a / b)),
            token![binop %] => Some(ScalarValue::Float(a % b)),
            token![binop ==] => Some(ScalarValue::Int((a == b) as i32)),
            token![binop !=] => Some(ScalarValue::Int((a != b) as i32)),
            token![binop <] => Some(ScalarValue::Int((a < b) as i32)),
            token![binop <=] => Some(ScalarValue::Int((a <= b) as i32)),
            token![binop >] => Some(ScalarValue::Int((a > b) as i32)),
            token![binop >=] => Some(ScalarValue::Int((a >= b) as i32)),
            token![binop ||] => None,
            token![binop &&] => None,
            token![binop ^] => None,
            token![binop &] => None,
            token![binop |] => None,
        }
    }
}

/// Visitor for const simplification.
///
/// See the [the module-level documentation][self] for more details.
pub struct Visitor {
    errors: CompileError,
}

impl Visitor {
    pub fn new() -> Self {
        Visitor { errors: CompileError::new_empty() }
    }

    pub fn finish(self) -> Result<(), CompileError> {
        self.errors.into_result(())
    }
}

impl VisitMut for Visitor {
    fn visit_expr(&mut self, e: &mut Sp<Expr>) {
        // simplify subexpressions first
        ast::walk_expr_mut(self, e);

        // now inspect this expression
        match &e.value {
            Expr::Unop(op, b) => {
                let b_const = match b.as_const() {
                    Some(b_value) => sp!(b.span => b_value),
                    _ => return, // can't simplify if subexpr is not const
                };

                match op.const_eval(b_const) {
                    Ok(new_value) => *e = sp!(e.span => new_value.into()),
                    Err(e) => {
                        self.errors.append(e);
                        return;
                    }
                }
            },

            Expr::Binop(a, op, b) => {
                let (a_const, b_const) = match (a.as_const(), b.as_const()) {
                    (Some(a_value), Some(b_value)) => (sp!(a.span => a_value), sp!(b.span => b_value)),
                    _ => return, // can't simplify if any subexpr is not const
                };

                match op.const_eval(a_const, b_const) {
                    Ok(new_value) => *e = sp!(e.span => new_value.into()),
                    Err(e) => {
                        self.errors.append(e);
                        return;
                    }
                }
            },

            Expr::Ternary { cond, left, right } => match cond.as_const() {
                // FIXME it should be possible to move somehow instead of cloning here...
                Some(ScalarValue::Int(0)) => e.value = (***right).clone(),
                Some(ScalarValue::Int(_)) => e.value = (***left).clone(),
                Some(_) => {
                    self.errors.append(error!(
                        message("type error"),
                        primary(cond, "ternary condition must be an integer")
                    ));
                    return;
                },
                _ => return, // can't simplify if subexpr is not const
            },
            _ => return, // can't simplify other expressions
        }
    }
}
