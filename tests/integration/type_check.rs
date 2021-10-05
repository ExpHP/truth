use crate::integration_impl::formats::*;
use crate::integration_impl::expected;

// NOTE: 'stackless__' is a prefix for things that used to be type-checked during lowering
//       (so they were special cases handled by the stackless lowerer), and 'const__' is a
//       prefix for things that used to be type-checked during const folding.
//
//       All of these things are now type-checked during the dedicated type-checking pass,
//       but we keep both of them in case that situation were to change again.

source_test!(
    ANM_10, bad_declaration,
    main_body: r#"  int %x;  "#,
    expect_error: expected::PARSE_ERROR,  // currently 'int $x' is invalid too, but never say never...
);

// =========================
// Stackless expression assignments

source_test!(
    ANM_10, stackless__assign_literal,
    main_body: r#"  I0 = 4.0;  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, stackless__assign_var,
    main_body: r#"  I0 = F0;  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, stackless__assign_var_sigil,
    main_body: r#"  I0 = %I1;  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, stackless__binop_arg,
    main_body: r#"  F0 = F1 + 4;  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, stackless__binop_out,
    main_body: r#"  I0 = F1 + 2.0;  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    MSG_06, stackless__binop_two_strings,
    main_body: r#"  textSet(0, 0, "F1" - "2.0");  "#,
    expect_error: "string",
);

source_test!(
    ANM_10, const__binop,
    main_body: r#"  I0 = 1 + 2.0;  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, stackless__sine_arg,
    main_body: r#"  float x = sin(I0);  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, stackless__sine_out,
    main_body: r#"  int x = sin(F0);  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, const__sine,
    main_body: r#"  F0 = sin(1);  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, const__sprite,
    main_body: r#"  F0 = sprite0;  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, stackless__ternary_cond,
    main_body: r#"  F0 = F2 ? 1.0 : 2.0;  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, stackless__ternary_arg,
    main_body: r#"  F0 = I1 ? F1 : I0;  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, stackless__ternary_out,
    main_body: r#"  I0 = I0 ? F0 : F1;  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, const__ternary_cond,
    main_body: r#"  F0 = 1.5 ? 1.0 : 2.0;  "#,
    expect_error: expected::TYPE_ERROR,
);

// for ternary branch type mismatch in a const context, see the "short-circuit" tests below

source_test!(
    ANM_10, stackless__binop_str,
    main_body: r#"  int x = I0 + "abc";  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, stackless__neg_str,
    main_body: r#"  int x = -"abc";  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    // ...hang on, should casting int to int really be an error?
    ANM_10, stackless__cast,
    main_body: r#"  int x = _S(I2);  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    // ...hang on, should casting int to int really be an error?
    ANM_10, const__cast,
    main_body: r#"  int x = _S(2);  "#,
    expect_error: expected::TYPE_ERROR,
);

// =========================
// stackless jumps

source_test!(
    ANM_10, stackless__jump_comparison_arg,
    main_body: r#"
        if (2 == 3.0) goto label;
      label:
    "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, stackless__jump_general_expr,
    main_body: r#"
        if (3.0) goto label;
      label:
    "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, stackless__jump_logical_arg,
    main_body: r#"
        if (2 && 3.0) goto label;
      label:
    "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, stackless__jump_logical_result,
    main_body: r#"
        if (2.0 && 3.0) goto label;
      label:
    "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, stackless__jump_predec_float,
    main_body: r#"
        if (--F0) goto label;
      label:
    "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, stackless__jump_time,
    main_body: r#"
        if (2 == 2) goto label @ 2.4;
      label:
    "#,
    expect_error: expected::PARSE_ERROR,
);

// =========================
// stackless times

source_test!(
    ANM_10, stackless__times_count,
    main_body: r#"  times(F0) {}  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, stackless__times_clobber,
    main_body: r#"  times(F0 = 4) {}  "#,
    expect_error: expected::TYPE_ERROR,
);

// =========================
// stackless instruction arguments

source_test!(
    ANM_10, stackless__ins_arg_var,
    main_body: r#"  pos(0.0, I0, 3.0);  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, stackless__ins_arg_literal,
    main_body: r#"  pos(0.0, 5, 3.0);  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, stackless__ins_arg_complex,
    main_body: r#"  pos(0.0, I0 + I2, 3.0);  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    MSG_06, stackless__func_arg_neg_str,
    main_body: r#"  textSet(0, 0, -"abc");  "#,
    expect_error: "string",
);

source_test!(
    ANM_10, stackless__pseudo,
    main_body: r#"  pos(@blob=12);  "#,
    expect_error: expected::TYPE_ERROR,
);

// =========================
// expression statements

source_test!(
    ANM_10, stackless__non_void_expr_statement,
    main_body: r#"  3.0;  "#,
    expect_error: expected::TYPE_ERROR,
);

// FIXME: Once we have ECL we should try `I0 ? "abc" : "def"` as an argument;
//        this is more or less the only way guaranteed to hit a "no runtime string temporaries"
//        check.  (at the time of writing, `-"abc"` and `"a" + "b"` currently hit it but, that's
//        only because it's not currently caught during in const folding or shallow typing)

// =========================
// short-circuited const expressions

// These tests look at subexpressions that get completely deleted from the AST during
// constant folding.  We want to make sure they are still typechecked!

source_test!(
    ANM_10, const__short_circuit__ternary_left,
    main_body: r#"  F0 = 5 ? 1.0 : 0;  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, const__short_circuit__ternary_right,
    main_body: r#"  F0 = 0 ? "lol" : 1.0;  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, const__short_circuit__and,
    main_body: r#"  I0 = 1 && "lmao";  "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, const__short_circuit__or,
    main_body: r#"  I0 = 0.0 || 1;  "#,
    expect_error: expected::TYPE_ERROR,
);

// =========================
// return

source_test!(
    ANM_10, return__value_from_void,
    items: r#"
        inline void foo() { return 0; }
    "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, return__none_from_void,
    items: r#"
        inline void foo() { return; }
    "#,
    // FIXME: Inline funcs should be supported eventually.
    //        Once they are, this should become a compile-succeed test.
    expect_error: expected::NOT_SUPPORTED_BY_FORMAT,
);

// (if we want to allow this to compile, then each lowerer will need tests to check that this
//  doesn't panic, since they might unwittingly expect the expression to have a value)
source_test!(
    ANM_10, return__void_from_void,
    items: r#"
        inline void foo() { return sprite(0); }
    "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, return__value_from_value,
    items: r#"
        inline float foo() { return 0; }
    "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, return__none_from_value,
    items: r#"
        inline float foo() { return; }
    "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, return__void_from_value,
    items: r#"
        inline float foo() { return sprite(0); }
    "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, return__missing_from_value,
    items: r#"
        inline int foo() { }
    "#,
    expect_error: "has no return",
);

source_test!(
    ANM_10, return__missing_from_void,
    items: r#"
        inline void foo() { }
    "#,
    // FIXME: Inline funcs should be supported eventually.
    //        Once they are, this should become a compile-succeed test.
    expect_error: expected::NOT_SUPPORTED_BY_FORMAT,
);
