#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

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
    ECL_06, diff_switch_decomp_disabled,
    main_body: r#"
    {"EN"}: I0 = 2;
    {"HL"}: I0 = 3;
"#,
    decompile_args: ["--no-diff-switches"],
    sbsb: |decompiled| {
        // decomp should NOT have occurred due to --no-diff-switches
        assert_eq!(decompiled.matches(" = ").count(), 2);
    },
);

source_test!(
    ECL_06, diff_switch_decomp_bad_output,
    main_body: r#"
    {"EN"}: I0 = 2;
    {"HL"}: I1 = 2;
"#,
    sbsb: |decompiled| {
        // decomp should NOT have occurred due to the output reg changing
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
    sbsb: |_| { /* just round-trip */ },
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

const ECL_IN_DIFFICULTY_MAPFILE: &'static str = r#"!eclmap
!difficulty_flags
0 E-
1 N-
2 H-
3 L-
4 4+
5 F+
6 U+
7 7+
"#;

source_test!(
    ECL_06_NO_DEFAULT_MAP, diff_switch_simple_aux_bits_all_on,
    mapfile: ECL_IN_DIFFICULTY_MAPFILE,
    main_body: r#"
    ins_4($REG[-10001], (2 : : 3 : ));
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);

        assert_eq!(ecl.subs[0].len(), 2);
        assert_eq!(ecl.subs[0][0].difficulty, 0b1111_0011);
        assert_eq!(ecl.subs[0][1].difficulty, 0b1111_1100);
    },
);

source_test!(
    ECL_06_NO_DEFAULT_MAP, diff_switch_simple_aux_bit_off,
    mapfile: ECL_IN_DIFFICULTY_MAPFILE,
    main_body: r#"
    {"*-F"}: ins_4($REG[-10001], (2 : : 3 : ));
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);

        assert_eq!(ecl.subs[0].len(), 2);
        assert_eq!(ecl.subs[0][0].difficulty, 0b1101_0011);
        assert_eq!(ecl.subs[0][1].difficulty, 0b1101_1100);
    },
);

source_test!(
    ECL_06_NO_DEFAULT_MAP, diff_switch_complex_aux_bits_all_on,
    mapfile: ECL_IN_DIFFICULTY_MAPFILE,
    main_body: r#"
    ins_4($REG[-10001], (2 : : 3 + $REG[-10003] : ));
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);

        assert_eq!(ecl.subs[0].len(), 3);
        assert_eq!(ecl.subs[0][0].difficulty, 0b1111_0011);
        assert_eq!(ecl.subs[0][1].difficulty, 0b1111_1100);
    },
);

source_test!(
    ECL_06_NO_DEFAULT_MAP, diff_switch_complex_aux_bit_off,
    mapfile: ECL_IN_DIFFICULTY_MAPFILE,
    main_body: r#"
    {"*-F"}: ins_4($REG[-10001], (2 : : 3 + $REG[-10003] : ));
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);

        assert_eq!(ecl.subs[0].len(), 3);
        assert_eq!(ecl.subs[0][0].difficulty, 0b1101_0011);
        assert_eq!(ecl.subs[0][1].difficulty, 0b1101_1100);
    },
);

source_test!(
    ECL_06_NO_DEFAULT_MAP, diff_switch_decomp_aux_bits_all_on,
    mapfile: ECL_IN_DIFFICULTY_MAPFILE,
    main_body: r#"
    {"EN"}: ins_4($REG[-10001], 2);
    {"HL"}: ins_4($REG[-10001], 3);
"#,
    sbsb: |decompiled| {
        assert!(!decompiled.contains("EN"));  // no diff flags
        assert!(decompiled.contains(": 3 :"));
    },
);

source_test!(
    ECL_06_NO_DEFAULT_MAP, diff_switch_decomp_aux_bit_off,
    mapfile: ECL_IN_DIFFICULTY_MAPFILE,
    main_body: r#"
    {"EN-F"}: ins_4($REG[-10001], 2);
    {"HL-F"}: ins_4($REG[-10001], 3);
"#,
    sbsb: |decompiled| {
        assert!(decompiled.contains(r#"{"*-F"}"#));
        assert!(decompiled.contains(": 3 :"));
    },
);

source_test!(
    ECL_06_NO_DEFAULT_MAP, diff_switch_decomp_aux_bit_mismatch,
    mapfile: ECL_IN_DIFFICULTY_MAPFILE,
    main_body: r#"
    {"EN-F"}: ins_4($REG[-10001], 2);
    {"HL"}:  ins_4($REG[-10001], 3);
"#,
    sbsb: |decompiled| {
        assert!(!decompiled.contains(": 3 :"));
    },
);

source_test!(
    ANM_10, diff_switch_in_non_ecl,
    main_body: r#"
    int x = (1:2:3:4);
"#,
    expect_error: expected::NOT_SUPPORTED_BY_FORMAT,
);
