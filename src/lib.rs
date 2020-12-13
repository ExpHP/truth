use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub lalrparser);
mod lalrparser_util;

pub use ast::*;
mod ast;
pub use fmt::Format;
pub mod fmt;
pub mod lexer;

pub use parse::Parse;
pub mod parse;

#[cfg(test)]
mod tests {
    use crate::ast::{Expr, Var, TypeKind};
    use crate::Parse;

    #[test]
    fn expr_parse() {
        macro_rules! check_exprs_same {
            ($a:expr, $with_parens:expr $(, $value:expr $(,)?)?) => {
                assert_eq!(
                    Expr::parse($a).unwrap(),
                    Expr::parse($with_parens).unwrap(),
                );
                $( assert_eq!(
                    Expr::parse($a).unwrap().const_eval_int(),
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
            Expr::parse("0x100000 * 0xffff").unwrap().const_eval_int(),
            Some(0xfff00000_u32 as i32),
        );
    }

    #[test]
    fn parse_trailing_comma() {
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
        assert_eq!(Var::parse("[244]"), Ok(Var::Unnamed { ty: TypeKind::Int, number: 244 }));
        assert_eq!(Var::parse("[-99998]"), Ok(Var::Unnamed { ty: TypeKind::Int, number: -99998 }));
        assert_eq!(Var::parse("[244f]"), Ok(Var::Unnamed { ty: TypeKind::Float, number: 244 }));
        assert_eq!(Var::parse("[-99998.0]"), Ok(Var::Unnamed { ty: TypeKind::Float, number: -99998 }));
        assert!(Var::parse("[-99998.5]").is_err());
        assert!(Var::parse("[-99998e5]").is_err());
        // FIXME: don't panic
        // assert!(parse("[12412151261243414]").is_err());
        assert_eq!(Var::parse("lmao"), Ok(Var::Named { ty: None, ident: "lmao".into() }));
        assert_eq!(Var::parse("$lmao"), Ok(Var::Named { ty: Some(TypeKind::Int), ident: "lmao".into() }));
        assert_eq!(Var::parse("%lmao"), Ok(Var::Named { ty: Some(TypeKind::Float), ident: "lmao".into() }));
    }
}
