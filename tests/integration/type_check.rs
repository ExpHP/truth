#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

source_test!(
    ANM_10, bad_declaration,
    // NOTE: currently 'int $x' is invalid too, but never say never...
    main_body: r#"  int %x;  //~ ERROR unexpected token "#,
);

// =========================
// Expression assignments

source_test!(
    ANM_10, simple_expr_types,
    main_body: r#"
        I0 = 4.0;  //~ ERROR type error
        I0 = F0;   //~ ERROR type error
        I0 = %I1;  //~ ERROR type error
    "#,
);

source_test!(
    ANM_10, basic_type_checking,
    items: r#"
script binops {
    F0 = F1 + 4;        // arg     //~ ERROR type error
    I0 = F1 + 2.0;      // output  //~ ERROR type error
    int x = I0 + "abc"; // string  //~ ERROR type error
}

script ternaries {
    F0 = F2 ? 1.0 : 2.0;  // cond   //~ ERROR type error
    F0 = I1 ? F1 : I0;    // cases  //~ ERROR type error
    I0 = I0 ? F0 : F1;    // output //~ ERROR type error
}

script functionUnops {
    float f = sin(I0); // arg    //~ ERROR type error
    int x = sin(F0);   // output //~ ERROR type error
}

script unaries {
    int x = -"abc";  //~ ERROR type error
    int z = $("abc");  //~ ERROR type error
}

script assign_op {
    F0 += I0;  //~ ERROR type error
    F0 += F1 < 2.0;  //~ ERROR type error
}
    "#,
);

source_test!(
    MSG_06, binop_two_strings,
    main_body: r#"
        textSet(0, 0, "F1" - "2.0");  //~ ERROR string
    "#,
);

source_test!(
    ANM_10, sprite_is_int,
    main_body: r#"
        F0 = sprite0;  //~ ERROR type error
    "#,
);

// =========================
// jumps

source_test!(
    ANM_10, jumps,
    items: r#"
script compare {
    if (2 == 3.0) goto label;  //~ ERROR type error
label:
}

script simpleCond {
    if (3.0) goto label;  //~ ERROR type error
label:
}

script logical {
    // argument
    if (2 && 3.0) goto label1;  //~ ERROR type error
label1:
    // result
    if (2.0 && 3.0) goto label2;  //~ ERROR type error
label2:
}

script predec {
    if (--F0) goto label;  //~ ERROR type error
label:
}
    "#,
);

source_test!(
    ANM_10, jump_time,
    main_body: r#"
        if (2 == 2) goto label @ 2.4;  //~ ERROR unexpected token
    label:
    "#,
);

// =========================
// times

source_test!(
    ANM_10, times,
    main_body: r#"
        times(F0) {}  // count  //~ ERROR type error
        times(F0 = 4) {}  // clobber  //~ ERROR type error
    "#,
);

// =========================
// instruction arguments

source_test!(
    ANM_10, ins_arg_var,
    main_body: r#"
        pos(0.0, I0, 3.0);       // var      //~ ERROR type error
        pos(0.0, 5, 3.0);        // literal  //~ ERROR type error
        pos(0.0, I0 + I2, 3.0);  // complex  //~ ERROR type error
    "#,
);

source_test!(
    MSG_06, ins_arg_neg_str,
    main_body: r#"
        textSet(0, 0, -"abc");  //~ ERROR string
    "#,
);

source_test!(
    // this test is basically the only way that is guaranteed to hit a
    // "no runtime string temporaries" check
    ECL_06, ins_arg_binop_str__stackless,
    main_body: r#"
        spellcard_start(0, 0, 20 ? "abc" : "def");  // this is okay (const eval)
        spellcard_start(0, 0, I0 ? "abc" : "def");  //~ ERROR temporary string
    "#,
    // FIXME: When stackful ECL is added, we should add a copy of this test for TH10+
);


source_test!(
    ANM_10, pseudo,
    main_body: r#"
        pos(@blob=12);  //~ ERROR type error
    "#,
);

// =========================
// difficulty

source_test!(
    ECL_06, diffswitch__missing_first,
    main_body: r#"
        int x = :4:4:6;  //~ ERROR unexpected token
    "#,
);

source_test!(
    ECL_06, diffswitch,
    main_body: r#"
        int x = 3::4.5:;               // arg       //~ ERROR type error
        float a = 3:4::4;              // out       //~ ERROR type error
        int y = ins_0():::;            // void expr //~ ERROR type error
        int z = (3.0:4.0:3.0 + 1:5.0); // interior  //~ ERROR type error
        (ins_0():::);                  // void stmt //~ ERROR type error
    "#,
);

// =========================
// expression statements

source_test!(
    ANM_10, non_void_expr_statement,
    main_body: r#"
        3.0;  //~ ERROR type error
    "#,
);

// =========================
// short-circuited const expressions

// These tests look at subexpressions that get completely deleted from the AST during
// constant folding.  We want to make sure they are still typechecked!
source_test!(
    ANM_10, const_short_circuit,
    main_body: r#"
        F0 = 5 ? 1.0 : 0;      // ternary left   //~ ERROR type error
        F0 = 0 ? "lol" : 1.0;  // ternary right  //~ ERROR type error
        I0 = 1 && "lmao";      // and            //~ ERROR type error
        I0 = 0.0 || 1;         // or             //~ ERROR type error
    "#,
);

// =========================
// return

source_test!(
    ANM_10, return__value_from_void,
    items: r#"
inline void foo() { return 0; }  //~ ERROR type error
    "#,
);

source_test!(
    ANM_10, return__none_from_void,
    // FIXME: Inline funcs should be supported eventually.
    //        Once they are, this should become a compile-succeed test.
    items: r#"
inline void foo() { return; }  //~ ERROR not supported
    "#,
);

// (if we want to allow this to compile, then each lowerer will need tests to check that this
//  doesn't panic, since they might unwittingly expect the expression to have a value)
source_test!(
    ANM_10, return__void_from_void,
    items: r#"
inline void foo() { return sprite(0); }  //~ ERROR type error
    "#,
);

source_test!(
    ANM_10, return__value_from_value,
    items: r#"
inline float foo() { return 0; }  //~ ERROR type error
    "#,
);

source_test!(
    ANM_10, return__none_from_value,
    items: r#"
inline float foo() { return; }  //~ ERROR type error
    "#,
);

source_test!(
    ANM_10, return__void_from_value,
    items: r#"
inline float foo() { return sprite(0); }  //~ ERROR type error
    "#,
);

source_test!(
    ANM_10, return__missing_from_value,
    items: r#"
inline int foo() { }
//~^ WARNING has no return
//~| ERROR not supported
    "#,
);

source_test!(
    ANM_10, return__missing_from_void__stackless,
    // FIXME: Inline funcs should be supported eventually.
    //        Once they are, this should become a compile-succeed test.
    items: r#"
inline void foo() { }  //~ ERROR not supported
    "#,
    // FIXME: This needs a stackful version
);
