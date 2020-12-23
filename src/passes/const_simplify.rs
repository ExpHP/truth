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
//! use ecl_parser::{Parse, VisitMut, Expr, pos::{Files}};
//! use ecl_parser::passes::const_simplify;
//!
//! let mut files = Files::new();
//!
//! let text = b"(3 == 3) ? (3.0 + 0.5) * x : 4";
//! let file_id = files.add("<input>", text);
//!
//! let mut expr = Expr::parse_spanned(text).unwrap();
//! let mut visitor = const_simplify::Visitor::new(file_id);
//! visitor.visit_expr(&mut (expr));
//! visitor.finish().expect("failed to simplify");
//!
//! let text_simplified = b"3.5 * x";
//! let file_id = files.add("<input>", text_simplified);
//! let expected = Expr::parse_spanned(text_simplified).unwrap();
//! assert_eq!(expr, expected);
//! ```

use crate::ast::{self, VisitMut, UnopKind, BinopKind, Expr};
use crate::error::{CompileError, Diagnostic, Label};
use crate::pos::Spanned;

impl UnopKind {
    fn const_eval_int(&self, x: i32) -> i32 {
        match self {
            UnopKind::Neg => i32::wrapping_neg(x),
            UnopKind::Not => (x != 0) as i32,
        }
    }

    fn const_eval_float(&self, x: f32) -> Option<f32> {
        match self {
            UnopKind::Neg => Some(-x),
            UnopKind::Not => None,
        }
    }
}

impl BinopKind {
    fn const_eval_int(&self, a: i32, b: i32) -> i32 {
        match self {
            BinopKind::Add => i32::wrapping_add(a, b),
            BinopKind::Sub => i32::wrapping_sub(a, b),
            BinopKind::Mul => i32::wrapping_mul(a, b),
            BinopKind::Div => i32::wrapping_div(a, b),
            BinopKind::Rem => i32::wrapping_rem(a, b),
            BinopKind::Eq => (a == b) as i32,
            BinopKind::Ne => (a != b) as i32,
            BinopKind::Lt => (a < b) as i32,
            BinopKind::Le => (a <= b) as i32,
            BinopKind::Gt => (a > b) as i32,
            BinopKind::Ge => (a >= b) as i32,
            BinopKind::LogicOr => if a == 0 { b } else { a },
            BinopKind::LogicAnd => if a == 0 { 0 } else { b },
            BinopKind::BitXor => a ^ b,
            BinopKind::BitAnd => a & b,
            BinopKind::BitOr => a | b,
        }
    }

    fn const_eval_float(&self, a: f32, b: f32) -> Option<Expr> {
        match self {
            BinopKind::Add => Some(Expr::from(a + b)),
            BinopKind::Sub => Some(Expr::from(a - b)),
            BinopKind::Mul => Some(Expr::from(a * b)),
            BinopKind::Div => Some(Expr::from(a / b)),
            BinopKind::Rem => Some(Expr::from(a % b)),
            BinopKind::Eq => Some(Expr::from((a == b) as i32)),
            BinopKind::Ne => Some(Expr::from((a != b) as i32)),
            BinopKind::Lt => Some(Expr::from((a < b) as i32)),
            BinopKind::Le => Some(Expr::from((a <= b) as i32)),
            BinopKind::Gt => Some(Expr::from((a > b) as i32)),
            BinopKind::Ge => Some(Expr::from((a >= b) as i32)),
            BinopKind::LogicOr => None,
            BinopKind::LogicAnd => None,
            BinopKind::BitXor => None,
            BinopKind::BitAnd => None,
            BinopKind::BitOr => None,
        }
    }
}

/// Visitor for const simplification.
///
/// See the [the module-level documentation][self] for more details.
pub struct Visitor {
    file_id: crate::pos::FileId,
    errors: Vec<crate::error::Diagnostic>,
}

impl Visitor {
    pub fn new(file_id: crate::pos::FileId) -> Self {
        Visitor {
            file_id,
            errors: vec![],
        }
    }

    pub fn finish(self) -> Result<(), CompileError> {
        match self.errors.len() {
            0 => Ok(()),
            _ => Err(CompileError(self.errors)),
        }
    }
}

#[derive(Copy, Clone)]
enum ConstType { Int(i32), Float(f32) }
impl Expr {
    fn as_const(&self) -> Option<ConstType> {
        match *self {
            Expr::LitInt { value, .. } => Some(ConstType::Int(value)),
            Expr::LitFloat { value, .. } => Some(ConstType::Float(value)),
            _ => None,
        }
    }
}
impl ConstType {
    fn type_str(&self) -> &'static str {
        match self {
            ConstType::Int(_) => "integer",
            ConstType::Float(_) => "float",
        }
    }
}

impl VisitMut for Visitor {
    fn visit_expr(&mut self, e: &mut Spanned<Expr>) {
        // simplify subexpressions first
        ast::walk_mut_expr(self, e);

        // now inspect this expression
        match &e.value {
            Expr::Unop(op, b) => {
                let b_const = match b.as_const() {
                    Some(b) => b,
                    _ => return, // can't simplify if subexpr is not const
                };

                match b_const {
                    ConstType::Int(b) => {
                        let new_value = op.const_eval_int(b);
                        *e = Spanned::new_from(e.span, new_value);
                    },
                    ConstType::Float(b) => {
                        let new_value = match op.const_eval_float(b) {
                            Some(x) => x,
                            None => {
                                self.errors.push({
                                    Diagnostic::error().with_labels(vec![
                                        Label::primary(self.file_id, e.span).with_message("this operator requires an integer")
                                    ]).with_message("type error")
                                });
                                return;
                            },
                        };

                        *e = Spanned::new_from(e.span, new_value);
                    },
                }
            },

            Expr::Binop(a, op, b) => {
                let (a_const, b_const) = match (a.as_const(), b.as_const()) {
                    (Some(a), Some(b)) => (a, b),
                    _ => return, // can't simplify if any subexpr is not const
                };

                match (a_const, b_const) {
                    (ConstType::Int(a), ConstType::Int(b)) => {
                        let new_value = op.const_eval_int(a, b);
                        *e = Spanned::new_from(e.span, new_value);
                    },
                    (ConstType::Float(a), ConstType::Float(b)) => {
                        let new_value = match op.const_eval_float(a, b) {
                            Some(x) => x,
                            None => {
                                self.errors.push({
                                    Diagnostic::error().with_labels(vec![
                                        Label::primary(self.file_id, e.span).with_message("operation not supported by floats")
                                    ]).with_message("type error")
                                });
                                return;
                            },
                        };

                        *e = Spanned::new_from(e.span, new_value);
                    },
                    _ => {
                        self.errors.push({
                            Diagnostic::error().with_labels(vec![
                                Label::primary(self.file_id, e.span).with_message("mismatched types"),
                                Label::secondary(self.file_id, a.span).with_message(a_const.type_str()),
                                Label::secondary(self.file_id, b.span).with_message(b_const.type_str()),
                            ]).with_message("type error")
                        })
                    },
                }
            },

            Expr::Ternary { cond, left, right } => match cond.as_const() {
                // FIXME it should be possible to move somehow instead of cloning here...
                Some(ConstType::Int(0)) => e.value = (***right).clone(),
                Some(ConstType::Int(_)) => e.value = (***left).clone(),
                Some(cond_const) => {
                    self.errors.push({
                        Diagnostic::error().with_labels(vec![
                            Label::primary(self.file_id, cond.span).with_message(cond_const.type_str())
                        ]).with_message("ternary condition must be an integer")
                    });
                    return;
                },
                _ => return, // can't simplify if subexpr is not const
            },
            _ => return, // can't simplify other expressions
        }
    }
}
