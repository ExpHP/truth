#[macro_use]
mod util_macros;

pub use error::{CompileError};
#[macro_use]
#[doc(hidden)]
pub mod error;

pub use pos::{Files, Span, Sp};
#[macro_use]
pub mod pos;

#[macro_use]
pub mod quote;

pub use ast::{Visit, VisitMut};
pub mod ast;
pub use fmt::{Format, Formatter};
pub mod fmt;

pub mod parse;

pub use anm::AnmFile;
pub mod anm;
pub use self::std::StdFile;
pub mod std;

// FIXME make this part of `ast`
pub mod meta;

pub use eclmap::Eclmap;
pub mod eclmap;

pub use type_system::{TypeSystem, ScalarType};
pub mod type_system;

pub use passes::DecompileKind;
pub mod passes;

pub use ident::{Ident, ParseIdentError};
pub mod ident;

pub use game::Game;
mod game;

pub mod cli_helper;

pub use var::{RegId, VarId, LocalId, Variables};
mod var;

mod binary_io;

pub mod llir;

pub mod vm;

pub use value::ScalarValue;
mod value {
    use std::fmt;
    use crate::ast;
    use crate::type_system::ScalarType;

    #[derive(Debug, Copy, Clone, PartialEq, PartialOrd)]
    pub enum ScalarValue { Int(i32), Float(f32) }

    impl ast::Expr {
        pub fn as_const(&self) -> Option<ScalarValue> {
            match *self {
                ast::Expr::LitInt { value, .. } => Some(ScalarValue::Int(value)),
                ast::Expr::LitFloat { value, .. } => Some(ScalarValue::Float(value)),
                _ => None,
            }
        }
    }
    impl From<ScalarValue> for ast::Expr {
        fn from(value: ScalarValue) -> Self { match value {
            ScalarValue::Int(value) => ast::Expr::from(value),
            ScalarValue::Float(value) => ast::Expr::from(value),
        }}
    }

    impl ScalarValue {
        pub fn ty(&self) -> ScalarType { match self {
            ScalarValue::Int(_) => ScalarType::Int,
            ScalarValue::Float(_) => ScalarType::Float,
        }}

        /// Allows simulating the effect of e.g. `%INT_VAR` or `$FLOAT_VAR`.
        /// (basically, the game performs typecasts when variables are read as the other type)
        pub fn apply_sigil(self, ty_sigil: Option<ast::VarReadType>) -> ScalarValue {
            match ty_sigil {
                None => return self,
                Some(ast::VarReadType::Int) => ScalarValue::Int(self.read_as_int()),
                Some(ast::VarReadType::Float) => ScalarValue::Float(self.read_as_float()),
            }
        }

        /// Obtain an integer value, as if read with a `$` prefix.  (i.e. casting if float)
        pub fn read_as_int(self) -> i32 {
            match self {
                ScalarValue::Int(x) => x,
                ScalarValue::Float(x) => x as i32,
            }
        }

        /// Obtain a float value, as if read with a `%` prefix.  (i.e. casting if integer)
        pub fn read_as_float(self) -> f32 {
            match self {
                ScalarValue::Int(x) => x as f32,
                ScalarValue::Float(x) => x,
            }
        }
    }

    impl fmt::Display for ScalarValue {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                ScalarValue::Float(x) => write!(f, "{:?}", x),
                ScalarValue::Int(x) => write!(f, "{}", x),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ast;
    use crate::parse::Parse;
    use crate::error::CompileError;

    fn simplify_expr(expr: ast::Expr) -> Result<ast::Expr, CompileError> {
        use crate::ast::VisitMut;

        let mut expr = sp!(expr);
        let mut visitor = crate::passes::const_simplify::Visitor::new();
        visitor.visit_expr(&mut expr);
        visitor.finish()?;

        Ok(expr.value)
    }

    #[test]
    fn expr_parse() {
        macro_rules! check_exprs_same {
            ($a:expr, $with_parens:expr $(, $value:expr $(,)?)?) => {
                assert_eq!(
                    ast::Expr::parse($a).unwrap(),
                    ast::Expr::parse($with_parens).unwrap(),
                );
                $( assert_eq!(
                    simplify_expr(ast::Expr::parse($a).unwrap()).unwrap(),
                    ast::Expr::from($value),
                ); )?
            }
        };
        check_exprs_same!("1 + 1 * 2", "1 + (1 * 2)", 3);
        check_exprs_same!("2 * 2 + 1", "(2 * 2) + 1", 5);
        check_exprs_same!("-3 + 5 * 7", "(-3) + (5 * 7)", 32);
        check_exprs_same!("-(1 + 1) * 2", "(-(1 + 1)) * 2", -4);
        check_exprs_same!(
            "1 == 3 ? 1 : 3 == 3 ? 2 : 0",
            "(1 == 3) ? 1 : ((3 == 3) ? 2 : 0)",
            2,
        );
        check_exprs_same!("1 + [1]", "1 + [1]");
        check_exprs_same!("boo(1, 2, 3)", "boo(1, 2, 3,)");
    }

    #[test]
    fn expr_const_overflow() {
        assert_eq!(
            simplify_expr(ast::Expr::parse("0x100000 * 0xffff").unwrap()).unwrap(),
            ast::Expr::from(0xfff00000_u32 as i32),
        );
    }

    #[test]
    fn parse_color() {
        // Even if we don't gracefully handle arbitrarily large integer literals,
        // we should at least be able to parse unsigned ints with MSB = 1,
        // which often show up in colors.
        assert_eq!(
            simplify_expr(ast::Expr::parse("0xff000000").unwrap()).unwrap(),
            ast::Expr::from(0xff000000_u32 as i32),
        );
    }

    fn time_label_test(text: &'static str, expected_times: Vec<i32>) {
        let item = ast::Item::parse(text).unwrap();
        let parsed_times = {
            let block = match item {
                ast::Item::Func { code: Some(block), .. } => block,
                _ => unreachable!(),
            };
            block.0.iter().map(|s| s.time).collect::<Vec<_>>()
        };

        assert_eq!(parsed_times, expected_times);
    }

    #[test]
    fn time_labels() {
        time_label_test(r#"void main() {
                  // before all is a "super no-op" at t=0
            a();  // should start at t=0
        +2: a();  // relative label
            a();  // check this is still at t=2
        +3: a();  // should now be t=5
        2:  a();  // absolute label
        -1: a();  // should also be absolute (t=-1), not relative (t=1)
                  // another "super no-op" with the end time
        }"#, vec![0, 0, 2, 2, 5, 2, -1, -1])
    }

    #[test]
    fn bookend_time_label() {
        time_label_test(r#"void main() {
                  // "super no-op" is still t=0 despite starting with a label
        1:  a();  // t=1 as labeled
        2:        // "super no-op" at end here is t=2
        }"#, vec![0, 1, 2]);
    }

    #[test]
    fn block_outer_time_label() {
        // this checks the madness that is StmtLabelsWithTime
        time_label_test(
            r#"void main() {
                +10: loop { +2: a(); +3: }
            }"#,
            // if you get [0, 15, 15] then something in the parser is #[inline] when it shouldn't be
            vec![0, 10, 15],
        );
    }

    #[test]
    fn parse_trailing_comma() {
        use ast::Expr;

        assert_eq!(
            Expr::parse("foo(1)").unwrap(),
            Expr::parse("foo(1,)").unwrap(),
        );
        assert_eq!(
            Expr::parse("foo(1, 2, 3)").unwrap(),
            Expr::parse("foo(1, 2, 3,)").unwrap(),
        );
        assert!(Expr::parse("foo(1, 2, ,)").is_err());
        assert!(Expr::parse("foo(,1, 2)").is_err());
        assert!(Expr::parse("foo(,)").is_err());
        assert!(Expr::parse("foo()").is_ok());
    }

    #[test]
    fn var_parse() {
        use ast::{Var, VarReadType};
        use crate::var::RegId;

        assert_eq!(Var::parse("[244]"), Ok(Var::Resolved { ty_sigil: Some(VarReadType::Int), var_id: RegId(244).into() }));
        assert_eq!(Var::parse("[-99998]"), Ok(Var::Resolved { ty_sigil: Some(VarReadType::Int), var_id: RegId(-99998).into() }));
        assert_eq!(Var::parse("[244f]"), Ok(Var::Resolved { ty_sigil: Some(VarReadType::Float), var_id: RegId(244).into() }));
        assert_eq!(Var::parse("[-99998.0]"), Ok(Var::Resolved { ty_sigil: Some(VarReadType::Float), var_id: RegId(-99998).into() }));
        assert!(Var::parse("[-99998.5]").is_err());
        assert!(Var::parse("[-99998e5]").is_err());
        // FIXME: don't panic
        // assert!(parse("[12412151261243414]").is_err());
        assert_eq!(Var::parse("lmao"), Ok(Var::Named { ty_sigil: None, ident: "lmao".parse().unwrap() }));
        assert_eq!(Var::parse("$lmao"), Ok(Var::Named { ty_sigil: Some(VarReadType::Int), ident: "lmao".parse().unwrap() }));
        assert_eq!(Var::parse("%lmao"), Ok(Var::Named { ty_sigil: Some(VarReadType::Float), ident: "lmao".parse().unwrap() }));
    }
}
