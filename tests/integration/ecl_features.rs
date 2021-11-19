use crate::integration_impl::{expected, formats::*};

const TIMELINE_DEBUGGING_ECLMAP: &'static str = r#"!eclmap
!ins_names
10 eclOnly

!ins_signatures
10 SS

!timeline_ins_names
10 timelineOnly
11 hasSubArg0
12 hasMsgArg0
13 hasUnusedArg0

!timeline_ins_signatures
10 T(_)ff
11 T(e)SS
12 T(m)SS
13 T(_)SS
"#;

source_test!(
    ECL_08, signature_with_arg0_in_not_timeline,
    mapfile: r#"!eclmap
!ins_signatures
1000 T(m)
    "#,
    main_body: "",
    expect_error: "invalid outside of timeline",
);

source_test!(
    ECL_08, signature_without_arg0_in_not_timeline,
    mapfile: r#"!eclmap
!timeline_ins_signatures
1000 SS
    "#,
    main_body: "",
    expect_error: "is missing",
);

source_test!(
    ECL_08, wrong_lang,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
timeline 0 {
    eclOnly(0, 3, 3);
}

void bouba() {
    timelineOnly(0, 3, 3);
}
"#,
    expect_error: "defined in ECL Timeline",
);

source_test!(
    ECL_TIMELINE_08, successful_sub_arg0s,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    items: r#"
    void bouba() {}
    void kiki() {}
"#,
    main_body: r#"
    hasSubArg0(kiki, 3, 3);
    hasMsgArg0(10, 3, 3);
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.timelines[0][0].extra_arg, Some(1));
    },
);

source_test!(
    ECL_TIMELINE_08, successful_msg_arg0s,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasMsgArg0(10, 3, 3);
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.timelines[0][0].extra_arg, Some(10));
    },
);

source_test!(
    ECL_TIMELINE_08, successful_unused_arg0s,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasUnusedArg0(3, 3);
    hasUnusedArg0(@arg0=5, 3, 3);
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.timelines[0][0].extra_arg, Some(0));
        assert_eq!(ecl.timelines[0][1].extra_arg, Some(5));
    },
);

source_test!(
    ECL_TIMELINE_08, bad_arity_with_required_arg0,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    // arg0 cannot stand in for a positional arg, even if that positional arg technically serves the role of arg0
    hasMsgArg0(@arg0=10, 3, 3);
"#,
    expect_error: "expects 3 arguments, got 2",
);

source_test!(
    ECL_TIMELINE_08, warn_arg0_collision,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasMsgArg0(@arg0=10, 5, 3, 3);
"#,
    expect_warning: "overrides value supplied naturally",
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.timelines[0][0].extra_arg, Some(10));  // i.e. not 5
    },
);

source_test!(
    ECL_TIMELINE_08, bad_type_for_optional_arg0,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasUnusedArg0(@arg0=5.5, 3, 3);
"#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ECL_TIMELINE_08, blob_without_optional_arg0,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasUnusedArg0(@blob="FFFFFFFF FFFFFFFF");
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.timelines[0][0].extra_arg, Some(0));
    },
);

source_test!(
    ECL_TIMELINE_08, optional_arg0_zero,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasUnusedArg0(3, 3);
"#,
    sbsb: |decompiled| assert!(decompiled.contains("(3, 3)")),
);

source_test!(
    ECL_TIMELINE_08, optional_arg0_nonzero,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasUnusedArg0(@arg0=5, 3, 3);
"#,
    sbsb: |decompiled| assert!(decompiled.contains("(@arg0=5, 3, 3)")),
);

source_test!(
    ECL_TIMELINE_08, optional_arg0_padding_edge_case,
    mapfile: r#"!eclmap
!timeline_ins_signatures
200 T(m)S__
"#,
    // this is an edge case that arose in decompilation where the presence of a timeline
    // arg could make the code that trims padding look at the wrong values
    main_body: r#"
    ins_200(1, 3, 0, 0);
    ins_200(1, 4, 4, 0);
    ins_200(1, 5, 5, 5);
"#,
    sbsb: |decompiled| {
        // make sure it cut the padding off at the right index each time
        assert!(decompiled.contains("(1, 3)"));
        assert!(decompiled.contains("(1, 4, 4)"));
        assert!(decompiled.contains("(1, 5, 5, 5)"));
    },
);

source_test!(
    ECL_TIMELINE_08, blob_without_required_arg0,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasSubArg0(@blob="FFFFFFFF FFFFFFFF");
"#,
    // even though arg0 is required in the signature here, code using @blob should
    // be compiled as if the signature is unknown, so it's allowed to be omitted here as well.
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.timelines[0][0].extra_arg, Some(0));
    },
);

source_test!(
    ECL_TIMELINE_08, expr_as_positional_arg0,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasMsgArg0(10 + 5, 3, 3);
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.timelines[0][0].extra_arg, Some(15));
    },
);

source_test!(
    ECL_TIMELINE_08, reg_as_positional_arg0,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasMsgArg0($REG[20], 3, 3);
"#,
    expect_error: "constant",
);

source_test!(
    ECL_TIMELINE_08, reg_as_other_timeline_arg,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasMsgArg0(3, $REG[20], 3);
"#,
    expect_error: "non-const",
);

source_test!(
    ECL_08, olde_unsupported_return_type,
    items: r#"
int bouba() {
    return 0;
}
"#,
    expect_error: "return types are not supported",
);

source_test!(
    ECL_08, olde_unsupported_extern,
    items: r#"
void externFunc();
"#,
    expect_error: "unsupported extern function",
);

source_test!(
    ECL_06, decompile_eosd_cmp_jmp_success,
    main_body: r#"
label:
    cmp_int(I0, 5);
    jump_lss(timeof(label), offsetof(label));
"#,
    sbsb: |decompiled| {
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
    sbsb: |decompiled| {
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
    sbsb: |decompiled| {
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
    sbsb: |decompiled| {
        assert!(!decompiled.contains("while"));
    },
);

source_test!(
    ECL_06, eosd_var_float_scratch_allocation,
    main_body: r#"
    // complex enough to require both F1 and F2
    F3 = (F0 + 1.0) * ((F0 + 2.0) * (F0 + 3.0));
"#,
    sbsb: |decompiled| {
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
        call(Sub12, 0, 1.0);
    }

    void Sub12() {
        F0 = F2;  // this uses the value of F2 set in Sub10
    }
"#,
    expect_error: "scratch registers are disabled",
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

// =============================================================================

// ---------------
// call signatures
source_test!(
    ECL_06, eosd_exported_fn_bad_siggy_string,
    // FIXME this has to be separate from the next test because currently it's a PARSE ERROR?!?!
    //       WHY DID I IMPLEMENT THIS IN THE PARSER
    items: r#"
void bad1(string arg) {}
"#,
    expect_error: "only possible for const",
);

source_test!(
    ECL_06, eosd_exported_fn_bad_siggies,
    items: r#"
void bad2(var x) {}

void bad3(int x, int y) {}

void bad4(float x, int y, float z) {}
"#,
    expect_error: "EoSD",
);

source_test!(
    ECL_06, eosd_exported_fn_bad_siggy_return_type,
    items: r#"
int bad5(int x) { return 2; }
"#,
    expect_error: "not supported",
);

source_test!(
    ECL_06, eosd_exported_fn_const_fn_name_clash,
    items: r#"
    void name() {}
    const void name() {}
    "#,
    expect_error: "redefinition",
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
    i(@blob="ffffffff");
"#,
    expect_error: "not an instruction",
);

source_test!(
    ECL_06, eosd_exported_fn_no_pseudos,
    items: EOSD_CALL_TEST_FUNCS,
    main_body: r#"
    i(@mask=3, 4);
"#,
    expect_error: "not an instruction",
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
void foo(float x, int a) {
    %REG[-10005] = 24.0;
    %REG[-10002] = x;
}
"#,
    expect_warning: "multiple names",
);

source_test!(
    ECL_06, eosd_param_alias_warning_named,
    items: r#"
void foo(float x, int a) {
    %F0 = 24.0;
    %F2 = x;
}
"#,
    expect_warning: "multiple names",
);

source_test!(
    // make sure scratch regs cannot clobber a parameter
    ECL_06, eosd_param_is_not_scratch,
    items: r#"
void i_f(int a, float x) {
    float t1 = 1.0;
    float t2 = 2.0;
    float t3 = 3.0;
    float t4 = 4.0;
}
"#,
    expect_error: "too complex",
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
    sbsb: |decompiled| assert!(decompiled.contains("= FPAR")),
);

source_test!(
    ECL_06, eosd_param_decompile_as_other_type,
    items: r#"
void foo(int a, float x) {
    float t1 = %a;
}
"#,
    sbsb: |decompiled| assert!(decompiled.contains("= %IPAR")),
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
    sbsb: |_| { /* just need it to round-trip */ },
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
    sbsb: |_| { /* just need it to round-trip */ },
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
    sbsb: |decompiled| {
        decompiled.contains("();");
        decompiled.contains("(7);");
        decompiled.contains("(2, 4);");
        decompiled.contains("(4.0);");
        decompiled.contains(" 2.0, "); // check for a big argument list
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
    sbsb: |decompiled| {
        decompiled.contains(" 2.0, "); // check for a big argument list
    },
);

macro_rules! pcb_funky_call_decomp_rt_test {
    ($test_name:ident, $body:expr) => {
        source_test!(
            ECL_07, $test_name,
            items: r#"void testSub() {}"#,
            main_body: $body,
            sbsb: |_| {
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
    ARG_A = 5;
    ARG_R = 2;
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
    goto label
"#);

pcb_funky_call_decomp_rt_test!(pcb_param_decomp_call_funky_sigil, r#"
    %ARG_A = 3.0;
    call(testSub);
"#);

pcb_funky_call_decomp_rt_test!(pcb_param_decomp_call_funky_end_of_script, r#"
    ARG_A = 3;
"#);

// =============================================================================

source_test!(
    ECL_06, diff_label_nesting_semantics,
    main_body: r#"
    nop();
    {"ENH"}: {
        nop();
        {"HL"}: nop();
        nop();
    }
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.subs[0][0].difficulty, 0xFF);
        assert_eq!(ecl.subs[0][1].difficulty, 0b111);
        assert_eq!(ecl.subs[0][2].difficulty, 0b1100);
        assert_eq!(ecl.subs[0][3].difficulty, 0b111);
    },
);

source_test!(
    ECL_06, diff_label_with_time_label_bad_1,
    main_body: r#"
    nop();
    {"ENH"}: {
        nop();
        if (I0 == 0) {
+10:
            nop();
        }
    }
"#,
    expect_warning: "surprising",
);

source_test!(
    // in this one the `if` is directly annotated
    ECL_06, diff_label_with_time_label_bad_2,
    main_body: r#"
    {"ENH"}: if (I0 == 0) {
        {"L"}: nop();
    }
"#,
    expect_warning: "surprising",
);

source_test!(
    ANM_10, diff_label_in_non_ecl,
    main_body: r#"
    {"012"}: int x = 1;
"#,
    expect_error: expected::NOT_SUPPORTED_BY_FORMAT,
);

source_test!(
    ECL_06, eosd_diff_switch_compile,
    main_body: r#"
    I0 = 3:4:5:6;
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.subs[0].len(), 4);  // one for each difficulty
        assert_eq!(ecl.subs[0][0].args_blob, blobify![-10001, 3]);
        assert_eq!(ecl.subs[0][2].args_blob, blobify![-10001, 5]);
    },
);

source_test!(
    ECL_06, eosd_diff_switch_omission,
    main_body: r#"
    I0 = 3::5:;
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.subs[0][0].args_blob, blobify![-10001, 3]);
        assert_eq!(ecl.subs[0][0].difficulty, 0b11);
        assert_eq!(ecl.subs[0][1].args_blob, blobify![-10001, 5]);
        assert_eq!(ecl.subs[0][1].difficulty, 0b1100);
    },
);

source_test!(
    ECL_06, eosd_diff_switch_multiple,
    main_body: r#"
    I0 = (3::5:) + (I2:I3::);
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.subs[0][0].args_blob, blobify![-10001, 3, -10003]);
        assert_eq!(ecl.subs[0][0].difficulty, 0b1);
        assert_eq!(ecl.subs[0][1].args_blob, blobify![-10001, 3, -10004]);
        assert_eq!(ecl.subs[0][1].difficulty, 0b10);
        assert_eq!(ecl.subs[0][2].args_blob, blobify![-10001, 5, -10004]);
        assert_eq!(ecl.subs[0][2].difficulty, 0b1100);
    },
);

source_test!(
    ECL_06, eosd_diff_switch_multiple_complex,
    main_body: r#"
    I0 = 3::5:I2+3;
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.subs[0].len(), 3);  // EN, H, L
    },
);

source_test!(
    ECL_06, eosd_diff_switch_offset,
    main_body: r#"
    jump(30, offsetof(label):::);
label:
"#,
    sbsb: |_| { /* just checking that it doesn't crash tbh */ },
);

source_test!(
    ECL_06, diff_switch_in_const_fn_call,
    items: r#"
const int foo(int a) {
    return 2 * a;
}

void bar() {
    I0 = foo(2:3:4:5);
}
"#,
    // Eventually const funcs will be supported, at which point this should hopefully
    // get caught by another error
    expect_error: expected::NOT_SUPPORTED_BY_FORMAT,
);

source_test!(
    ECL_06, diff_switch_in_inline_fn_call,
    items: r#"
inline void foo(int a) {
    I1 = 2 * a;
}

void bar() {
    foo(2:3:4:5);
}
"#,
    // Eventually inline funcs will be supported.
    // I'm not sure what this should do in that case.
    expect_error: expected::NOT_SUPPORTED_BY_FORMAT,
);

source_test!(
    ECL_06, diff_switch_significance_of_num_cases,
    main_body: r#"
    I0 = (2:3:4:5);
    I1 = (2:3:4);
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.subs[0].len(), 7);
    },
);

source_test!(
    ECL_06, diff_switch_too_many_cases,
    main_body: r#"
    I0 = (2::::::::);
"#,
    expect_error: "too many",
);

source_test!(
    ECL_06, diff_switch_mismatched_number_of_cases,
    main_body: r#"
    I0 = (2:3:4:5) + (1:2:3:4:5);
"#,
    expect_error: "switch lengths",
);

source_test!(
    ECL_06, diff_switch_different_num_cases_in_block,
    main_body: r#"
    {"ENHL"}: {
        I0 = (2:3:4:5);
        I1 = (2:3:4);
    }
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.subs[0].len(), 7);
    },
);

source_test!(
    ECL_06, diff_switch_decomp_assign,
    // this test is basically a control for 'diff_switch_decomp_bad_output'
    main_body: r#"
    {"EN"}: I0 = 2;
    {"HL"}: I0 = 3;
"#,
    sbsb: |decompiled| {
        assert!(decompiled.contains(": 3 :"));
    },
);

source_test!(
    ECL_06, diff_switch_decomp_bad_output,
    main_body: r#"
    {"EN"}: I0 = 2;
    {"HL"}: I1 = 2;
"#,
    sbsb: |decompiled| {
        assert_eq!(decompiled.matches("= 2").count(), 2);
    },
);

source_test!(
    ECL_06, diff_switch_decomp_sub_id,
    items: r#"
void foo(int x) {}
void bar(int x) {}
    "#,
    main_body: r#"
    {"EN"}: foo(1337);
    {"HL"}: bar(1337);
"#,
    sbsb: |decompiled| {
        assert!(decompiled.contains("(1337,"), "didn't decomp intrinsic");
        // other than that, just roundtrip
    },
);

source_test!(
    ECL_06, diff_switch_decomp_jump_time,
    items: r#"
void foo(int x) {}
void bar(int x) {}
    "#,
    main_body: r#"
    {"EN"}: jump(30, offsetof(label));
    {"HL"}: jump(50, offsetof(label));
label:
    nop();
"#,
    sbsb: |decompiled| {
        assert!(decompiled.contains("goto"), "didn't decomp intrinsic");
        // other than that, just roundtrip
    },
);

source_test!(
    ECL_06, diff_switch_decomp_jump_offset,
    items: r#"
void foo(int x) {}
void bar(int x) {}
    "#,
    main_body: r#"
    {"EN"}: jump(30, offsetof(label1));
    {"HL"}: jump(30, offsetof(label2));
label1:
    nop();
label2:
    nop();
"#,
    sbsb: |decompiled| {
        assert!(decompiled.contains("goto"), "didn't decomp intrinsic");
        // other than that, just roundtrip
    },
);

source_test!(
    ECL_06, diff_switch_decomp_ins_padding,
    mapfile: r#"!eclmap
!ins_signatures
200 SS__
    "#,
    main_body: r#"
    {"EN"}: ins_200(I0, 10, 0);
    {"HL"}: ins_200(I0, 10, 16);
"#,
    sbsb: |decompiled| {
        assert_eq!(decompiled.matches("ins_200").count(), 1);
        assert!(!decompiled.contains(", 0)"));  // check that the second padding arg was dropped
    },
);

source_test!(
    ECL_06, diff_switch_decomp_intrinsic_padding,
    mapfile: r#"!eclmap
!ins_signatures
10 SS_
!ins_intrinsics
10 AssignOp(=,int)
    "#,
    main_body: r#"
    {"EN"}: ins_10(I0, 10, 0);
    {"HL"}: ins_10(I0, 10, 16);
    ins_10(I0, 15, 0);
"#,
    sbsb: |decompiled| {
        // specificity: show that the second instance does decompile
        assert!(decompiled.contains("= 15;"));
        // doesn't really matter how this decompiles as long as it round-trips.
        // (it might expand the diff switch, or it might put a switch in padding)
    },
);

source_test!(
    ECL_06, diff_switch_decomp_offsetof_timeof,
    mapfile: r#"!eclmap
!ins_signatures
200 ot     # a non-intrinsic to force offsetof and timeof
    "#,
    main_body: r#"
    {"EN"}: ins_200(offsetof(label1), timeof(label1));
    {"HL"}: ins_200(offsetof(label2), timeof(label2));
+10:
label1:
    nop();
+10:
label2:
    nop();
"#,
    sbsb: |decompiled| {
        assert!(decompiled.contains("offsetof"));
        assert!(decompiled.contains("timeof"));
        // other than that, just roundtrip
    },
);

source_test!(
    ECL_06, diff_switch_decomp_label_in_middle,
    main_body: r#"
label1:
    {"EN"}: I0 = I1 + 2;
label2:
    {"HL"}: I0 = I1 + 3;
    goto label1;
    goto label2;
"#,
    sbsb: |_decompiled| {
        // just roundtrip
    },
);

source_test!(
    ECL_06, diff_switch_decomp_label_at_front,
    main_body: r#"
    nop();
label:
    {"EN"}: I0 = I1 + 2;
    {"HL"}: I0 = I1 + 3;
    goto label;
"#,
    sbsb: |_decompiled| {
        // just roundtrip
    },
);

source_test!(
    ANM_10, diff_switch_in_non_ecl,
    main_body: r#"
    int x = (1:2:3:4);
"#,
    expect_error: expected::NOT_SUPPORTED_BY_FORMAT,
);

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
