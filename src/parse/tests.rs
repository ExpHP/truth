use crate::ast;
use crate::parse::Parse;
use crate::error::ErrorReported;

// This is for quick-and-dirty use only; the spans in the output will have incomplete information
// as it is not connected to any Files object.
fn parse<A: Parse>(s: &str) -> super::Result<'_, A> {
    let mut state = super::State::new();
    super::Parse::parse_stream(&mut state, super::Lexer::new(None, s.as_ref()))
        .map(|x| x.value)
}

// This extremely hasty const simplification pass won't handle const vars at all, but is
// still useful for checking how expressions are parsed (especially w.r.t. precedence).
fn simplify_expr(expr: ast::Expr) -> Result<ast::Expr, ErrorReported> {
    let mut scope = crate::Builder::new().build();
    let mut truth = scope.truth();
    let mut ctx = truth.ctx();

    let mut expr = sp!(expr);
    crate::passes::const_simplify::run(&mut expr, &mut ctx)?;

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
    }
    check_exprs_same!("1 + 1 * 2", "1 + (1 * 2)", 3);
    check_exprs_same!("2 * 2 + 1", "(2 * 2) + 1", 5);
    check_exprs_same!("-3 + 5 * 7", "(-3) + (5 * 7)", 32);
    check_exprs_same!("-(1 + 1) * 2", "(-(1 + 1)) * 2", -4);
    check_exprs_same!(
        "1 == 3 ? 1 : 3 == 3 ? 2 : 0",
        "(1 == 3) ? 1 : ((3 == 3) ? 2 : 0)",
        2,
    );
    check_exprs_same!("1 + $REG[1]", "1 + $REG[1]");
}

#[test]
fn expr_const_overflow() {
    assert_eq!(
        simplify_expr(parse::<ast::Expr>("0x100000 * 0xffff").unwrap()).unwrap(),
        ast::Expr::from(0xfff00000_u32 as i32),
    );
}

#[test]
fn parse_color() {
    // Even if we don't gracefully handle arbitrarily large integer literals,
    // we should at least be able to parse unsigned ints with MSB = 1,
    // which often show up in colors.
    assert_eq!(
        simplify_expr(parse::<ast::Expr>("0xff000000").unwrap()).unwrap(),
        ast::Expr::from(0xff000000_u32 as i32),
    );
}

fn time_label_test(text: &'static str, expected_times: Vec<i32>) {
    let item = parse::<ast::Item>(text).unwrap();
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
    assert!(parse::<ast::Expr>("foo(1)").is_ok());
    assert!(parse::<ast::Expr>("foo(1,)").is_ok());
    assert!(parse::<ast::Expr>("foo(1, 2, 3)").is_ok());
    assert!(parse::<ast::Expr>("foo(1, 2, 3,)").is_ok());
    assert!(parse::<ast::Expr>("foo(1, 2, ,)").is_err());
    assert!(parse::<ast::Expr>("foo(,1, 2)").is_err());
    assert!(parse::<ast::Expr>("foo(,)").is_err());
    assert!(parse::<ast::Expr>("foo()").is_ok());
}

#[test]
fn parse_escape() {
    assert_eq!(
        parse::<ast::Expr>(r#" "\r\n\\\"\0" "#).unwrap(),
        ast::Expr::LitString(ast::LitString { string: "\r\n\\\"\0".to_string() }),
    );
}

#[test]
fn var_parse() {
    use ast::{Var, VarSigil};
    use crate::resolve::RegId;

    fn reg(reg: i32) -> ast::VarName {
        ast::VarName::Reg { reg: RegId(reg), language: None }
    }

    assert_eq!(parse::<Var>("$REG[244]").unwrap(), Var { ty_sigil: Some(VarSigil::Int), name: reg(244) });
    assert_eq!(parse::<Var>("$REG[-99998]").unwrap(), Var { ty_sigil: Some(VarSigil::Int), name: reg(-99998) });
    assert_eq!(parse::<Var>("REG[244]").unwrap(), Var { ty_sigil: None, name: reg(244) });
    assert_eq!(parse::<Var>("%REG[-99998]").unwrap(), Var { ty_sigil: Some(VarSigil::Float), name: reg(-99998) });
    assert!(parse::<Var>("REG[-99998999999]").is_err());
    assert!(matches!(parse::<Var>("lmao").unwrap(), Var { ty_sigil: None, .. }));
    assert!(matches!(parse::<Var>("$lmao").unwrap(), Var { ty_sigil: Some(VarSigil::Int), .. }));
    assert!(matches!(parse::<Var>("%lmao").unwrap(), Var { ty_sigil: Some(VarSigil::Float), .. }));
}

#[test]
fn string_escape() {
    use ast::LitString;

    assert_eq!(parse::<LitString>(r#" "ab\\\"\r\nd" "#).unwrap(), LitString { string: "ab\\\"\r\nd".into() });
}

#[track_caller]
fn expect_parse_error<T: Parse>(expected: &str, source: &str) -> String {
    let mut scope = crate::Builder::new().capture_diagnostics(true).build();
    let mut truth = scope.truth();

    let _ = truth.parse::<T>("<input>", source.as_bytes()).err().unwrap();
    let err_str = truth.get_captured_diagnostics().unwrap();

    if !err_str.contains(expected) {
        panic!("expected not found in error message!  error: `{}`  expected: {:?}", err_str, expected)
    }
    err_str
}

macro_rules! parse_error_snapshot_test {
    ($name:ident, expect($expected:literal), <$ty:ty> $source:literal) => {
        #[test]
        fn $name() { assert_snapshot!(expect_parse_error::<$ty>($expected, $source).trim()); }
    };
}

parse_error_snapshot_test!(invalid_token, expect("token"), <ast::Expr> "(32 + \u{306F})");
parse_error_snapshot_test!(integer_overflow, expect("too large"), <ast::Expr> "124712894724479");
parse_error_snapshot_test!(unexpected_token, expect("unexpected"), <ast::Stmt> "int x = int;");
parse_error_snapshot_test!(unexpected_eof, expect("EOF"), <ast::Stmt> "int x = 3");
parse_error_snapshot_test!(big_reg, expect("too large"), <ast::Stmt> "float x = %REG[1234258905623];");
parse_error_snapshot_test!(bad_escape, expect("escape"), <ast::Expr> r#" "abc\jefg" "#);
parse_error_snapshot_test!(bad_escape_end, expect("token"), <ast::Expr> r#" "abcefg\"#);
parse_error_snapshot_test!(bad_ins_identifier, expect("instruction"), <ast::Expr> r#" ins_04() "#);
parse_error_snapshot_test!(bad_ins_identifier_2, expect("instruction"), <ast::Expr> r#" ins_a() "#);
parse_error_snapshot_test!(bad_ins_empty, expect("instruction"), <ast::Expr> r#" ins_() "#);
parse_error_snapshot_test!(bad_ins_overflow, expect("instruction"), <ast::Expr> r#" ins_99999999999999() "#);
parse_error_snapshot_test!(unclosed_comment, expect("token"), <ast::ScriptFile> r#" /* comment "#);
parse_error_snapshot_test!(duplicate_meta_key, expect("duplicate"), <ast::Meta> r#"{
  a: {
    thing: 100,
    another: 101,
    yet_another: 102,
    thing: 103,
  },
}"#);
