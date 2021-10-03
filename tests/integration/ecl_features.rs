use crate::integration_impl::{expected, formats::*};

source_test!(
    ECL_08, wrong_lang,
    full_source: r#"
timeline 0 {
    eclOnly(0, 3, 3);
}

void sub0() {
    timelineOnly(0, 3, 3);
}
"#,
    expect_fail: expected::UNIMPLEMENTED,
    // expect_fail: "there is a ECL Timeline",
);

source_test!(
    ECL_08, successful_arg0s,
    full_source: r#"
timeline 0 {
    hasSubArg0(sub1, 3, 3);
    hasMsgArg0(10, 3, 3);
    hasUnusedArg0(3, 3);
    hasUnusedArg0(@arg0=5, 3, 3);
}

void sub0() {}
void sub1() {}
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.timelines[0][0].extra_arg, Some(1));
        assert_eq!(ecl.timelines[0][1].extra_arg, Some(10));  // 3
        assert_eq!(ecl.timelines[0][2].extra_arg, Some(0));
        assert_eq!(ecl.timelines[0][3].extra_arg, Some(5));
    },
);

source_test!(
    ECL_08, bad_arity_with_required_arg0,
    full_source: r#"
timeline 0 {
    // arg0 cannot stand in for a positional arg, even if that positional arg technically serves the role of arg0
    hasMsgArg0(@arg0=10, 3, 3);
}
"#,
    expect_fail: expected::TYPE_ERROR,
);

source_test!(
    ECL_08, warn_arg0_collision,
    full_source: r#"
timeline 0 {
    hasMsgArg0(@arg0=10, 5, 3, 3);
}
"#,
    // FIXME: why doesn't this work
    // check_compiled: |output, format| {
    //     let ecl = output.read_ecl(format);
    //     assert_eq!(ecl.timelines[0][0].extra_arg, Some(10));
    // },
    expect_warning: "overrides value supplied naturally",
);

source_test!(
    ECL_08, bad_type_for_optional_arg0,
    full_source: r#"
timeline 0 {
    hasUnusedArg0(@arg0=5.5, 3, 3);
}
"#,
    expect_fail: expected::TYPE_ERROR,
);

source_test!(
    ECL_08, blob_without_required_arg0,
    full_source: r#"
timeline 0 {
    hasSubArg0(@blob="FFFFFFFF FFFFFFFF");
}

void sub0() {}
void sub1() {}
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.timelines[0][0].extra_arg, Some(1));
        assert_eq!(ecl.timelines[0][1].extra_arg, Some(10));  // 3
        assert_eq!(ecl.timelines[0][2].extra_arg, Some(0));
        assert_eq!(ecl.timelines[0][3].extra_arg, Some(5));
    },
);

source_test!(
    ECL_08, blob_without_optional_arg0,
    full_source: r#"
timeline 0 {
    hasUnusedArg0(@blob="FFFFFFFF FFFFFFFF");
}

void sub0() {}
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.timelines[0][0].extra_arg, Some(0));
    },
);

source_test!(
    ECL_08, reg_as_positional_arg0,
    full_source: r#"
timeline 0 {
    hasMsgArg0($REG[20], 3, 3);
}

void sub0() {}
void sub1() {}
"#,
    expect_fail: "TODO: what message lol",
);
