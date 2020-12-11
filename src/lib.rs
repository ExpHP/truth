use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub parser); // synthesized by LALRPOP
pub mod ast;

#[test]
fn calculator1() {
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
    check_exprs_same!("1 + 1 * 2", "1 + (1 * 2)", 3);
    check_exprs_same!("2 * 2 + 1", "(2 * 2) + 1", 5);
    check_exprs_same!("-3 + 5 * 7", "(-3) + (5 * 7)", 32);
    check_exprs_same!("-(1 + 1) * 2", "(-(1 + 1)) * 2", -4);
    check_exprs_same!(
        "1 == 3 ? 1 : 3 == 3 ? 2 : 0",
        "(1 == 3) ? 1 : ((3 == 3) ? 2 : 0)",
        2,
    );
}
