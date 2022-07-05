#[allow(unused)]
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
10 ff
11 s(arg0;enum="EclSub")SS
12 s(arg0;enum="MsgScript")SS
13 SS
"#;

source_test!(
    ECL_06, signature_with_arg0_in_not_timeline,
    mapfile: r#"!eclmap
!ins_signatures
1000 s(arg0; enum="MsgScript")  //~ ERROR only valid in
    "#,
    main_body: "",
);

source_test!(
    ECL_08, signature_with_arg0_in_th08_timeline,
    mapfile: r#"!eclmap
!timeline_ins_signatures
1000 s(arg0; enum="MsgScript")  //~ ERROR only valid in
    "#,
    main_body: "",
);

source_test!(
    ECL_08, signature_without_arg0_in_th08_timeline,
    mapfile: r#"!eclmap
!timeline_ins_signatures
1000 SS
    "#,
    main_body: "",
    check_compiled: |_, _| {},
);

source_test!(
    ECL_06, wrong_lang,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
script timeline {
    eclOnly(0, 3, 3);   //~ ERROR defined in ECL
}

void bouba() {
    timelineOnly(0, 3, 3);   //~ ERROR defined in ECL Timeline
}
"#,
);

source_test!(
    ECL_TIMELINE_06, successful_sub_arg0s,
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
        let ecl = output.read_olde_ecl(format);
        assert_eq!(ecl.timelines[0][0].extra_arg, Some(1));
    },
);

source_test!(
    ECL_TIMELINE_06, successful_msg_arg0s,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasMsgArg0(10, 3, 3);
"#,
    check_compiled: |output, format| {
        let ecl = output.read_olde_ecl(format);
        assert_eq!(ecl.timelines[0][0].extra_arg, Some(10));
    },
);

source_test!(
    ECL_TIMELINE_06, successful_unused_arg0s,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasUnusedArg0(3, 3);
    hasUnusedArg0(@arg0=5, 3, 3);
"#,
    check_compiled: |output, format| {
        let ecl = output.read_olde_ecl(format);
        assert_eq!(ecl.timelines[0][0].extra_arg, Some(0));
        assert_eq!(ecl.timelines[0][1].extra_arg, Some(5));
    },
);

source_test!(
    ECL_TIMELINE_06, bad_arity_with_required_arg0,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    // arg0 cannot stand in for a positional arg, even if that positional arg technically serves the role of arg0
    hasMsgArg0(@arg0=10, 3, 3);  //~ ERROR expects 3 arguments, got 2
"#,
);

source_test!(
    ECL_TIMELINE_06, warn_arg0_collision,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasMsgArg0(@arg0=10, 5, 3, 3);  //~ WARNING overrides value supplied naturally
"#,
    check_compiled: |output, format| {
        let ecl = output.read_olde_ecl(format);
        assert_eq!(ecl.timelines[0][0].extra_arg, Some(10));  // i.e. not 5
    },
);

source_test!(
    ECL_TIMELINE_06, bad_type_for_explicit_arg0,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasUnusedArg0(@arg0=5.5, 3, 3);  //~ ERROR type error
"#,
);

source_test!(
    ECL_TIMELINE_06, blob_without_unused_arg0,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasUnusedArg0(@blob="FFFFFFFF FFFFFFFF");
"#,
    check_compiled: |output, format| {
        let ecl = output.read_olde_ecl(format);
        assert_eq!(ecl.timelines[0][0].extra_arg, Some(0));
    },
);

source_test!(
    ECL_TIMELINE_06, unused_arg0_zero,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasUnusedArg0(3, 3);
"#,
    check_decompiled: |decompiled| assert!(decompiled.contains("(3, 3)")),
);

source_test!(
    ECL_TIMELINE_06, unused_arg0_nonzero,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasUnusedArg0(@arg0=5, 3, 3);
"#,
    check_decompiled: |decompiled| assert!(decompiled.contains("(@arg0=5, 3, 3)")),
);

source_test!(
    ECL_TIMELINE_06, unused_arg0_padding_edge_case,
    mapfile: r#"!eclmap
!timeline_ins_signatures
200 s(arg0;enum="MsgScript")S__
"#,
    // this is an edge case that arose in decompilation where the presence of a timeline
    // arg could make the code that trims padding look at the wrong values
    main_body: r#"
    ins_200(1, 3, 0, 0);
    ins_200(1, 4, 4, 0);
    ins_200(1, 5, 5, 5);
"#,
    check_decompiled: |decompiled| {
        // make sure it cut the padding off at the right index each time
        assert!(decompiled.contains("(1, 3)"));
        assert!(decompiled.contains("(1, 4, 4)"));
        assert!(decompiled.contains("(1, 5, 5, 5)"));
    },
);

source_test!(
    ECL_TIMELINE_06, blob_without_required_arg0,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasSubArg0(@blob="FFFFFFFF FFFFFFFF");
"#,
    // even though arg0 is required in the signature here, code using @blob should
    // be compiled as if the signature is unknown, so it's allowed to be omitted here as well.
    check_compiled: |output, format| {
        let ecl = output.read_olde_ecl(format);
        assert_eq!(ecl.timelines[0][0].extra_arg, Some(0));
    },
);

source_test!(
    ECL_TIMELINE_06, expr_as_positional_arg0,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasMsgArg0(10 + 5, 3, 3);
"#,
    check_compiled: |output, format| {
        let ecl = output.read_olde_ecl(format);
        assert_eq!(ecl.timelines[0][0].extra_arg, Some(15));
    },
);

source_test!(
    ECL_TIMELINE_06, reg_as_positional_arg0,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    main_body: r#"
    hasMsgArg0($REG[20], 3, 3);  //~ ERROR constant
"#,
);

source_test!(
    ECL_TIMELINE_06, timeline_sub_decomp,
    main_body: r#"
    ins_0(0, 1.0, 2.0, 3.0, 4, 5, 6);
    ins_0(1, 1.0, 2.0, 3.0, 4, 5, 6);
    ins_0(2, 1.0, 2.0, 3.0, 4, 5, 6);
"#,
    items: r#"
void sub0() {}
void sub1() {}
"#,
    check_decompiled: |s| {
        assert!(s.contains("(sub0,"));
        assert!(s.contains("(sub1,"));
        assert!(s.contains("(2,"));
    },
);

source_test!(
    ECL_TIMELINE_08, timeline_sub_decomp_not_arg0,
    main_body: r#"
    ins_0(0, 1.0, 2.0, 4, 5, 6);
    ins_0(1, 1.0, 2.0, 4, 5, 6);
    ins_0(2, 1.0, 2.0, 4, 5, 6);
"#,
    items: r#"
void sub0() {}
void sub1() {}
"#,
    check_decompiled: |s| {
        assert!(s.contains("(sub0,"));
        assert!(s.contains("(sub1,"));
        assert!(s.contains("(2,"));
    },
);
