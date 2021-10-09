use crate::integration_impl::{expected, formats::*};

source_test!(
    ECL_08, wrong_lang,
    full_source: r#"
#pragma mapfile "map/debug.eclm"

timeline 0 {
    eclOnly(0, 3, 3);
}

void sub0() {
    timelineOnly(0, 3, 3);
}
"#,
    expect_error: "there is a ECL Timeline",
);

source_test!(
    ECL_08, successful_arg0s,
    full_source: r#"
#pragma mapfile "map/debug.eclm"

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
#pragma mapfile "map/debug.eclm"

timeline 0 {
    // arg0 cannot stand in for a positional arg, even if that positional arg technically serves the role of arg0
    hasMsgArg0(@arg0=10, 3, 3);
}
"#,
    expect_error: "expects 3 arguments, got 2",
);

source_test!(
    ECL_08, warn_arg0_collision,
    full_source: r#"
#pragma mapfile "map/debug.eclm"

timeline 0 {
    hasMsgArg0(@arg0=10, 5, 3, 3);
}
"#,
    expect_warning: "overrides value supplied naturally",
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.timelines[0][0].extra_arg, Some(10));
    },
);

source_test!(
    ECL_08, bad_type_for_optional_arg0,
    full_source: r#"
#pragma mapfile "map/debug.eclm"

timeline 0 {
    hasUnusedArg0(@arg0=5.5, 3, 3);
}
"#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ECL_08, blob_without_required_arg0,
    full_source: r#"
#pragma mapfile "map/debug.eclm"

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
#pragma mapfile "map/debug.eclm"

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
#pragma mapfile "map/debug.eclm"

timeline 0 {
    hasMsgArg0($REG[20], 3, 3);
}

void sub0() {}
void sub1() {}
"#,
    // expect_error: "TODO: what message lol",
    expect_error: expected::UNIMPLEMENTED,
);

source_test!(
    ECL_08, olde_unsupported_param,
    items: r#"
void sub0(int x) {}
"#,
    expect_error: "parameters are not supported",
);

source_test!(
    ECL_08, olde_unsupported_return_type,
    items: r#"
int sub0() {
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
    expect_warning: "extern functions are not supported",
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
