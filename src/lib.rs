use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub parser); // synthesized by LALRPOP
pub mod ast;

#[cfg(test)]
type ParseResult<'input, T> = Result<T, lalrpop_util::ParseError<usize, parser::Token<'input>, &'static str>>;

#[test]
fn expr_parse() {
    macro_rules! check_exprs_same {
        ($a:expr, $with_parens:expr $(, $value:expr $(,)?)?) => {
            assert_eq!(
                parser::ExprParser::new().parse($a).unwrap(),
                parser::ExprParser::new().parse($with_parens).unwrap(),
            );
            $( assert_eq!(
                parser::ExprParser::new().parse($a).unwrap().const_eval_int(),
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
}

#[test]
fn var_parse() {
    use crate::ast::{Var, TypeKind};

    fn parse(s: &str) -> ParseResult<'_, Var> {
        parser::VarParser::new().parse(s)
    };

    assert_eq!(parse("[244]"), Ok(Var::Unnamed { ty: TypeKind::Int, number: 244 }));
    assert_eq!(parse("[-99998]"), Ok(Var::Unnamed { ty: TypeKind::Int, number: -99998 }));
    assert_eq!(parse("[244f]"), Ok(Var::Unnamed { ty: TypeKind::Float, number: 244 }));
    assert_eq!(parse("[-99998.0]"), Ok(Var::Unnamed { ty: TypeKind::Float, number: -99998 }));
    assert!(parse("[-99998.5]").is_err());
    assert!(parse("[-99998e5]").is_err());
    assert!(parse("[12412151261243414]").is_err());
    assert_eq!(parse("lmao"), Ok(Var::Named { ty: None, ident: "lmao".into() }));
    assert_eq!(parse("$lmao"), Ok(Var::Named { ty: Some(TypeKind::Int), ident: "lmao".into() }));
    assert_eq!(parse("%lmao"), Ok(Var::Named { ty: Some(TypeKind::Float), ident: "lmao".into() }));
}
