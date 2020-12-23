
pub use error::CompileError;
#[macro_use]
mod error {
    pub use ::codespan_reporting::diagnostic::{Diagnostic, Label};

    // Lazy-ass macros to generate Diagnostics until we have something better.
    // TODO: get rid of these
    macro_rules! bail_span {
        ($file_id:expr, $span:expr, $($fmt_args:tt)+) => {{
            return Err(CompileError({
                crate::error::Diagnostic::error()
                    .with_labels(vec![
                        crate::error::Label::primary($file_id, $span.span)
                            .with_message(format!($($fmt_args)+))
                    ])
            }));
        }};
    }
    macro_rules! bail_nospan {
        ($($fmt_args:tt)+) => {{
            return Err(CompileError({
                crate::error::Diagnostic::error()
                    .with_message(format!($($fmt_args)+))
            }));
        }};
    }

    #[derive(thiserror::Error, Debug)]
    #[error("{}", .0.message)]
    pub struct CompileError(pub Diagnostic<crate::pos::FileId>);
}


pub use ast::*;
mod ast;
pub use fmt::Format;
pub mod fmt;

pub use parse::Parse;
pub mod parse;

pub mod std;

pub mod meta;

pub use eclmap::Eclmap;
pub mod eclmap;

pub mod signature;

pub use pos::{Span, Spanned};
pub mod pos;

pub use ident::{Ident, ParseIdentError};
mod ident;

#[cfg(test)]
mod tests {
    use crate::{ast, Parse};

    #[test]
    fn expr_parse() {
        macro_rules! check_exprs_same {
            ($a:expr, $with_parens:expr $(, $value:expr $(,)?)?) => {
                assert_eq!(
                    ast::Expr::parse($a).unwrap(),
                    ast::Expr::parse($with_parens).unwrap(),
                );
                $( assert_eq!(
                    ast::Expr::parse($a).unwrap().const_eval_int(),
                    $value,
                ); )?
            }
        };
        check_exprs_same!("1 + 1 * 2", "1 + (1 * 2)", Some(3));
        check_exprs_same!("2 * 2 + 1", "(2 * 2) + 1", Some(5));
        check_exprs_same!("-3 + 5 * 7", "(-3) + (5 * 7)", Some(32));
        check_exprs_same!("-(1 + 1) * 2", "(-(1 + 1)) * 2", Some(-4));
        check_exprs_same!(
            "1 == 3 ? 1 : 3 == 3 ? 2 : 0",
            "(1 == 3) ? 1 : ((3 == 3) ? 2 : 0)",
            Some(2),
        );
        check_exprs_same!("1 + [1]", "1 + [1]", None);
        check_exprs_same!("boo(1, 2, 3)", "boo(1, 2, 3,)", None);
    }

    #[test]
    fn expr_const_overflow() {
        assert_eq!(
            ast::Expr::parse("0x100000 * 0xffff").unwrap().const_eval_int(),
            Some(0xfff00000_u32 as i32),
        );
    }

    #[test]
    fn parse_color() {
        // Even if we don't gracefully handle arbitrarily large integer literals,
        // we should at least be able to parse unsigned ints with MSB = 1,
        // which often show up in colors.
        assert_eq!(
            ast::Expr::parse("0xff000000").unwrap().const_eval_int(),
            Some(0xff000000_u32 as i32),
        );
    }

    #[test]
    fn time_labels() {
        let item = ast::Item::parse(r#"void main() {
            a();  // should start at t=0
        +2: a();  // relative label
            a();  // check this is still at t=2
        +3: a();  // should now be t=5
        2:  a();  // absolute label
        -1: a();  // should also be absolute (t=-1), not relative (t=1)
        }"#).unwrap();
        let expected_times = vec![0, 2, 2, 5, 2, -1];

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

        assert_eq!(Var::parse("[244]"), Ok(Var::Unnamed { ty: VarReadType::Int, number: 244 }));
        assert_eq!(Var::parse("[-99998]"), Ok(Var::Unnamed { ty: VarReadType::Int, number: -99998 }));
        assert_eq!(Var::parse("[244f]"), Ok(Var::Unnamed { ty: VarReadType::Float, number: 244 }));
        assert_eq!(Var::parse("[-99998.0]"), Ok(Var::Unnamed { ty: VarReadType::Float, number: -99998 }));
        assert!(Var::parse("[-99998.5]").is_err());
        assert!(Var::parse("[-99998e5]").is_err());
        // FIXME: don't panic
        // assert!(parse("[12412151261243414]").is_err());
        assert_eq!(Var::parse("lmao"), Ok(Var::Named { ty: None, ident: "lmao".parse().unwrap() }));
        assert_eq!(Var::parse("$lmao"), Ok(Var::Named { ty: Some(VarReadType::Int), ident: "lmao".parse().unwrap() }));
        assert_eq!(Var::parse("%lmao"), Ok(Var::Named { ty: Some(VarReadType::Float), ident: "lmao".parse().unwrap() }));
    }
}
