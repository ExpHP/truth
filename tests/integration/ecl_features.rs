#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

source_test!(
    ECL_08, olde_unsupported_return_type,
    items: r#"
int bouba() {  //~ ERROR return types are not supported
    return 0;
}
"#,
);

source_test!(
    ECL_08, olde_unsupported_extern,
    items: r#"
void externFunc();  //~ ERROR unsupported extern function
"#,
);

source_test!(
    ECL_06, decompile_eosd_cmp_jmp_success,
    main_body: r#"
label:
    cmp_int(I0, 5);
    jump_lss(timeof(label), offsetof(label));
"#,
    check_decompiled: |decompiled| {
        assert!(decompiled.contains("while"));
        assert!(decompiled.contains("< 5"));
    },
);

source_test!(
    ECL_06, decompile_eosd_cmp_jmp_blocked_by_time,
    main_body: r#"
label:
    cmp_int(I0, 5);
+1:
    jump_lss(timeof(label), offsetof(label));
"#,
    check_decompiled: |decompiled| {
        assert!(!decompiled.contains("while"));
    },
);

source_test!(
    ECL_06, decompile_eosd_cmp_jmp_blocked_by_difficulty,
    main_body: r#"
label1:
    cmp_int(I0, 5);
    {"H"}: jump_lss(timeof(label1), offsetof(label1));
    nop();
label2:
    {"H"}: cmp_int(I0, 5);
    jump_lss(timeof(label2), offsetof(label2));
"#,
    check_decompiled: |decompiled| {
        assert!(!decompiled.contains("while"));
    },
);

source_test!(
    ECL_06, decompile_eosd_cmp_jmp_blocked_by_label,
    main_body: r#"
label:
    cmp_int(I0, 5);
otherLabelLol:
    jump_lss(timeof(label), offsetof(label));
    goto otherLabelLol;
"#,
    check_decompiled: |decompiled| {
        assert!(!decompiled.contains("while"));
    },
);

source_test!(
    ECL_06, eosd_var_float_scratch_allocation,
    main_body: r#"
    // complex enough to require both F1 and F2
    F3 = (F0 + 1.0) * ((F0 + 2.0) * (F0 + 3.0));
"#,
    check_decompiled: |decompiled| {
        // should use F1 and F2 for temporaries, and not integer variables
        // (even though the instructions written to file use integer outputs)
        assert!(decompiled.contains("%REG[-10006]"));
        assert!(decompiled.contains("%REG[-10007]"));
    },
);

source_test!(
    ECL_06, eosd_patchy_is_goddamn_dangerous,
    items: r#"
    void Sub10() {
        F2 = 1.0;
        ins_130(1);  // that one that disables the call stack
        call(Sub11, 0, 1.0);
    }

    void Sub11() {
        // Even though this sub has no mention of F2, it is NOT safe to
        // use it for scratch purposes.
        F3 = (F0 + 1.0) * ((F0 + 2.0) * (F0 + 3.0));
        //~^ ERROR scratch registers are disabled

        call(Sub12, 0, 1.0);
    }

    void Sub12() {
        F0 = F2;  // this uses the value of F2 set in Sub10
    }
"#,
);

// source_test!(
//     ECL_10, extern_conflict,
//     full_source: r#"
// timeline 0 {}

// void sub0();
// void sub0() {}
// void sub1() {}
// "#,
//     expect_warning: "conflicting extern definition",
// );

// source_test!(
//     ECL_10, double_extern_okay,
//     full_source: r#"
// timeline 0 {}

// void externFunc();
// void externFunc();
// void main() {}
// "#,
//     check_compiled: |_| {
//         panic!("TODO: add a call to externFunc and check it here")
//     },
// );

source_test!(
    ECL_06, eosd_cant_cast,
    main_body: r#"
        int a = int(F0 + 2.0);  //~ ERROR not supported
        float x = float(I0 + 2);  //~ ERROR not supported
    "#,
);

source_test!(
    ECL_06, eosd_allowed_casts,
    main_body: r#"
        // these casts are trivial so they are okay!
        int b = int(I0 + 2);
        float y = float(F0 + 2.0);
    "#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.subs[0].len(), 2);
    },
);

source_test!(
    ECL_06, eosd_user_provided_cast,
    mapfile: r#"!eclmap
!ins_signatures
1000 Sf
1001 SS
!ins_intrinsics
1000 UnOp(int,float)
1001 UnOp(float,int)
"#,
    main_body: r#"
        int x = int(F0 + 2.0);
        float y = float(I0 + 2);
    "#,
    check_decompiled: |decompiled| {
        assert!(decompiled.contains(" = float("));
        assert!(decompiled.contains(" = int("));
    },
);

// source_test!(
//     ECL_06, eosd_user_provided_cast_doesnt_reuse_bad_type,
//     mapfile: r#"!eclmap
// !ins_signatures
// 1000 Sf
// 1001 SS
// !ins_intrinsics
// 1000 UnOp(int,float)
// 1001 UnOp(float,int)
// "#,
//     main_body: r#"
//         int x = int(F0 + 2.0);
//         float y = float(I0 + 2);
//     "#,
//     check_decompiled: |decompiled| {
//         assert!(decompiled.contains(" = float("));
//         assert!(decompiled.contains(" = int("));
//     },
// );

// =============================================================================

// ---------------
// call signatures
source_test!(
    ECL_06, eosd_exported_fn_bad_siggy_string,
    // FIXME this has to be separate from the next test because currently it's a PARSE ERROR?!?!
    //       WHY DID I IMPLEMENT THIS IN THE PARSER
    items: r#"
void bad1(string arg) {}  //~ ERROR only possible for const
"#,
);

source_test!(
    ECL_06, eosd_exported_fn_bad_siggies,
    items: r#"
void bad2(var x) {}  //~ ERROR EoSD

void bad3(int x, int y) {}  //~ ERROR EoSD

void bad4(float x, int y, float z) {}  //~ ERROR EoSD
"#,
);

source_test!(
    ECL_06, eosd_exported_fn_bad_siggy_return_type,
    items: r#"
int bad5(int x) { return 2; }  //~ ERROR not supported
"#,
);

source_test!(
    ECL_06, eosd_exported_fn_const_fn_name_clash,
    items: r#"
    void name() {}
    const void name() {}  //~ ERROR redefinition
    "#,
);

// -------------
// call sites

const EOSD_CALL_TEST_FUNCS: &'static str = r#"
void i_f(int x, float y) {}
void f_i(float y, int x) {}
void i(int x) {}
void f(float x) {}
"#;

source_test!(
    ECL_06, eosd_exported_fn_param_order,
    items: EOSD_CALL_TEST_FUNCS,
    main_body: r#"
    i_f(30, 1.0);
    f_i(1.0, 40);
    i(50);
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.subs.last().unwrap().1[0].args_blob, blobify![0, 30, 1.0]);
        assert_eq!(ecl.subs.last().unwrap().1[1].args_blob, blobify![1, 40, 1.0]);
        assert_eq!(ecl.subs.last().unwrap().1[2].args_blob, blobify![2, 50, 0.0]);
    },
);

source_test!(
    ECL_06, eosd_simplifiable_const_arg,
    items: EOSD_CALL_TEST_FUNCS,
    main_body: r#"
    i((20 * 5) + 37);
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.subs.last().unwrap().1[0].args_blob, blobify![2, 137, 0]);
    },
);

source_test!(
    ECL_06, eosd_exported_fn_no_blob,
    items: EOSD_CALL_TEST_FUNCS,
    main_body: r#"
    i(@blob="ffffffff");  //~ ERROR not an instruction
"#,
);

source_test!(
    ECL_06, eosd_exported_fn_no_pseudos,
    items: EOSD_CALL_TEST_FUNCS,
    main_body: r#"
    i(@mask=3, 4);  //~ ERROR not an instruction
"#,
);

source_test!(
    ECL_06, eosd_exported_fn_offsetof,
    items: EOSD_CALL_TEST_FUNCS,
    // not sure what this should do but make sure it doesn't panic
    main_body: r#"
        i(offsetof(label));
    label:
"#,
    check_compiled: |_, _| {},
);

// -------------
// param use in function bodies

source_test!(
    ECL_06, eosd_param_assignment,
    items: r#"
void i_f(int a, float x) {
    $REG[-10003] = a;
    %REG[-10006] = x;
}

void f_i(float x, int a) {
    $REG[-10003] = a;
    %REG[-10006] = x;
}
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        for index in 0..2 {
            let sub = &ecl.subs[index];
            // what we're checking here is the -10001 and -10005
            assert_eq!(sub[0].args_blob, blobify!(-10003, -10001));
            assert_eq!(sub[1].args_blob, blobify!(-10006, -10005.0));
        }
    },
);

source_test!(
    ECL_06, eosd_param_alias_warning_reg,
    items: r#"
void foo(float x, int a) {  //~ WARNING multiple names
    %REG[-10005] = 24.0;
    %REG[-10002] = x;
}
"#,
);

source_test!(
    ECL_06, eosd_param_alias_warning_named,
    items: r#"
void foo(float x, int a) {  //~ WARNING multiple names
    %F0 = 24.0;
    %F2 = x;
}
"#,
);

source_test!(
    // make sure scratch regs cannot clobber a parameter
    ECL_06, eosd_param_is_not_scratch,
    items: r#"
void i_f(int a, float x) {
    float t1 = 1.0;
    float t2 = 2.0;
    float t3 = 3.0;
    float t4 = 4.0;  //~ ERROR too complex
}
"#,
);

// -------------
// decompiling params

source_test!(
    ECL_06, eosd_param_decompile,
    items: r#"
void foo(int a, float x) {
    float t1 = x;
}
"#,
    check_decompiled: |decompiled| assert!(decompiled.contains("= FPAR")),
);

source_test!(
    ECL_06, eosd_param_decompile_as_other_type,
    items: r#"
void foo(int a, float x) {
    float t1 = %a;
}
"#,
    check_decompiled: |decompiled| assert!(decompiled.contains("= %IPAR")),
);

// -------------
// decompiling calls

source_test!(
    ECL_06, eosd_param_decompile_calls,
    items: r#"
void foo(int a) {
    int t1 = a;
}
void bar(float x) {
    float t1 = x;
}
void baz(int a, float x) {
    float t1 = x;
    int t2 = a;
}
"#,
    main_body: r#"
    foo(3);
    bar(6.0);
    baz(2, 1.5);
    "#,
    check_decompiled: |_| { /* just need it to round-trip */ },
);

source_test!(
    // too difficult to implement right now, needs more infrastructure in signatures
    #[ignore]
    ECL_06, eosd_arg_must_be_immediate,
    items: r#"
void baz(int a, float x) {
    float t1 = x;
    int t2 = a;
}
"#,
    // note: not an error because zero wants to abuse this or something and
    //       we can't control lint levels yet.  _/o\_
    main_body: r#"
    baz(2, F1);  //~ WARNING constant
    "#,
);

source_test!(
    // This one doesn't contain reads so the decompiler might have more trouble
    // inferring the params.  Make sure it still roundtrips.
    ECL_06, eosd_param_decompile_calls_without_reads,
    items: r#"
void foo(int a) {}
void bar(float x) {}
void baz(int a, float x) {}
"#,
    main_body: r#"
    foo(3);
    bar(6.0);
    baz(2, 1.5);
    "#,
    check_decompiled: |_| { /* just need it to round-trip */ },
);

source_test!(
    ECL_07, pcb_param_decompile_calls,
    items: r#"
void neither() {}
void anInt(int a) {}
void twoInts(int a, int b) {}
void aFloat(float a) {}
void mixed(int a, int b, float x, int c, float y) {}
"#,
    main_body: r#"
    neither();
    anInt(7);
    twoInts(2, 4);
    aFloat(4.0);
    mixed(2, I0, 2.0, 7, F0);
    "#,
    check_decompiled: |decompiled| {
        assert!(decompiled.contains("();"));
        assert!(decompiled.contains("(7);"));
        assert!(decompiled.contains("(2, 4);"));
        assert!(decompiled.contains("(4.0);"));
        assert!(decompiled.contains(" 2.0, ")); // check for a big argument list
    },
);

source_test!(
    // you know, in case somebody added PCB style calls to EoSD,
    // make sure it doesn't get tripped up by the funky signature.
    ECL_07, pcb_param_decompile_calls_eosd_assign,
    mapfile: r#"!eclmap
!ins_signatures
5  Sf  # set_float
"#,
    items: r#"
void foo(int a, int b, float x, int c, float y) {
    int t1 = a;
}
"#,
    main_body: r#"
    foo(2, I0, 2.0, 7, F0);
    "#,
    check_decompiled: |decompiled| {
        assert!(decompiled.contains(" 2.0, ")); // check for a big argument list
    },
);

macro_rules! pcb_funky_call_decomp_rt_test {
    ($test_name:ident, $body:expr) => {
        source_test!(
            ECL_07, $test_name,
            items: r#"void testSub() {}"#,
            main_body: $body,
            check_decompiled: |_| {
                // just roundtrip
            },
        );
    };
}

pcb_funky_call_decomp_rt_test!(pcb_param_decomp_call_not_too_funky, r#"
    ARG_A = 7;
    call(testSub);
"#);

pcb_funky_call_decomp_rt_test!(pcb_param_decomp_call_funky_full_house, r#"
    ARG_R = 7.0;
    ARG_S = 8.0;
    ARG_M = 9.0;
    ARG_N = 10.0;
    ARG_A = 7;
    ARG_B = 8;
    ARG_C = 9;
    ARG_D = 10;
    call(testSub);
"#);

pcb_funky_call_decomp_rt_test!(pcb_param_decomp_call_funky_skip, r#"
    ARG_B = 8;
    call(testSub);
"#);

pcb_funky_call_decomp_rt_test!(pcb_param_decomp_call_funky_expr, r#"
    ARG_A = 3;
    ARG_B = (I0 * 2) + 3;
    call(testSub);
"#);

pcb_funky_call_decomp_rt_test!(pcb_param_decomp_call_funky_order_1, r#"
    ARG_B = 7;
    ARG_A = 3;
    call(testSub);
"#);

pcb_funky_call_decomp_rt_test!(pcb_param_decomp_call_funky_order_2, r#"
    ARG_R = 2.0;
    ARG_A = 5;
    call(testSub);
"#);

pcb_funky_call_decomp_rt_test!(pcb_param_decomp_call_funky_order_3, r#"
    ARG_A = 5;
    ARG_R = 2.0;
    ARG_B = 7;
    call(testSub);
"#);

pcb_funky_call_decomp_rt_test!(pcb_param_decomp_call_funky_diff_differ, r#"
    ARG_A = 5;
    {"EN"}: ARG_B = 7;
    call(testSub);
"#);

pcb_funky_call_decomp_rt_test!(pcb_param_decomp_call_funky_diff_same, r#"
    {"EN"}: ARG_A = 5;
    {"EN"}: ARG_B = 7;
    {"EN"}: call(testSub);
"#);

pcb_funky_call_decomp_rt_test!(pcb_param_decomp_call_funky_time, r#"
    ARG_A = 5;
+10:
    call(testSub);
"#);

pcb_funky_call_decomp_rt_test!(pcb_param_decomp_call_funky_label, r#"
    ARG_A = 5;
label:
    call(testSub);
    goto label;
"#);

pcb_funky_call_decomp_rt_test!(pcb_param_decomp_call_funky_sigil, r#"
    %ARG_A = 3.0;
    call(testSub);
"#);

pcb_funky_call_decomp_rt_test!(pcb_param_decomp_call_funky_end_of_script, r#"
    ARG_A = 3;
"#);

pcb_funky_call_decomp_rt_test!(pcb_param_decomp_call_funky_mismatch, r#"
    ARG_A = 3;
    ARG_B = 4;
    call(testSub);

    ARG_A = 3;
    call(testSub);
"#);


// =============================================================================

#[test]
#[ignore]
fn need_tests_for_eosd_reg_that_looks_like_literal() {
    panic!()
}

#[test]
#[ignore]
fn need_tests_for_eosd_literal_whose_value_is_a_reg() {
    panic!()
}
