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
label:
    cmp_int(I0, 5);
difficulty[0x8]:
    jump_lss(timeof(label), offsetof(label));
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
    %REG[-10004] = 24.0;
    %REG[-10002] = x;
}
"#,
    expect_warning: "aliases",
);

source_test!(
    ECL_06, eosd_param_alias_warning_named,
    items: r#"
void foo(float x, int a) {
    %F0 = 24.0;
    %F2 = x;
}
"#,
    expect_warning: "aliases",
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
