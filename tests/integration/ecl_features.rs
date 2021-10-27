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
    expect_error: "non-const",
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
    ECL_08, olde_unsupported_param,
    items: r#"
void bouba(int x) {}
"#,
    expect_error: "parameters are not supported",
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

#[test]
#[ignore]
fn test_olde_ecl_register_allocation_correctly_uses_float_regs() {
    panic!()
}
