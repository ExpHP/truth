use crate::integration_impl::formats::*;
use crate::integration_impl::expected;

source_test!(
    ANM_10, mapfile_does_not_exist,
    items: r#"
        #pragma mapfile "this/is/a/bad/path"
    "#,
    expect_fail: "while resolving",
);

source_test!(
    ANM_10, unknown_instr_signature,
    main_body: r#"  ins_6000(0, 0, 0);  "#,
    expect_fail: "signature",
);

source_test!(
    ANM_10, unknown_instr_name,
    main_body: r#"  iMadeThisUpYesterday(0, 0, 0);  "#,
    expect_fail: "unknown function",
);

source_test!(
    ANM_10, unknown_variable,
    main_body: r#"  int x = y;  "#,
    expect_fail: "unknown variable",
);

source_test!(
    // even with explicit sigils, untyped vars simply can't exist in stackless langs
    ANM_10, stackless__untyped_var,
    main_body: r#"
        var x;
        $x = 4;
    "#,
    expect_fail: expected::NOT_SUPPORTED_BY_FORMAT,
);

source_test!(
    ANM_10, anm_bitwise,
    main_body: r#"
        I0 = I0 | I1;
    "#,
    expect_fail: expected::NOT_SUPPORTED_BY_FORMAT,
);

source_test!(
    ANM_10, bad_signature_in_mapfile,
    items: r#"
        #pragma mapfile "tests/mapfile-with-bad-signature.anmm"
    "#,
    expect_fail: "opcode 1000",
);

source_test!(
    STD_08, jump_missing_label,
    main_body: r#"
        goto label;
    "#,
    expect_fail: "undefined label",
);

source_test!(
    STD_08, duplicate_label,
    main_body: r#"
    label:
    label:
    "#,
    expect_fail: "duplicate label",
);

source_test!(
    STD_08, local_in_std,
    main_body: r#"
        int x = 4;
    "#,
    expect_fail: expected::NOT_SUPPORTED_BY_FORMAT,
);

source_test!(
    ANM_10, local_string,
    main_body: r#"
        string x = "hi";
    "#,
    expect_fail: "non-const",
);

source_test!(
    ANM_10, local_void,
    main_body: r#"
        void x = delete();
    "#,
    expect_fail: "must have a value",
);

source_test!(
    ANM_10, const_void,
    items: r#"
        const void x = delete();
    "#,
    expect_fail: "must have a value",
);

source_test!(
    ANM_10, const_untyped,
    items: r#"
        const var x = 3;
    "#,
    expect_fail: "untyped",
);

source_test!(
    ANM_10, func_untyped,
    items: r#"
        var foo() { return 1; }
    "#,
    expect_fail: "var-typed",
);

// FIXME: change this test to ECL once that is available
source_test!(
    // this is going to become grammatically correct eventually; the test is here to make
    // sure it fails gracefully from the getgo
    ANM_10, func_nonconst_string,
    items: r#"
        string foo() { return "hi"; }
    "#,
    expect_fail: expected::NOT_SUPPORTED_BY_FORMAT,
);

source_test!(
    ANM_10, func_inline_const,
    items: r#"
        inline const int foo() { return 1; }
    "#,
    expect_fail: "extra qualifier",
);

source_test!(
    // this may become grammatically correct at some point; the test is here to make
    // sure it fails gracefully from the getgo
    ANM_10, local_named_after_reg,
    main_body: r#"
        int REG[100] = 3;
    "#,
    expect_fail: expected::PARSE_ERROR,
);

source_test!(
    // this may become grammatically correct at some point; the test is here to make
    // sure it fails gracefully from the getgo
    ANM_10, func_param_named_after_reg,
    items: r#"
        void foo(int REG[100]) {}
    "#,
    expect_fail: expected::PARSE_ERROR,
);

source_test!(
    ANM_10, const_string_to_int,
    items: r#"
        const string x = "hi";
        const int y = $x;
    "#,
    expect_fail: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, uninitialized_const,
    items: r#"
        const int y = 3, z, w = 4;
    "#,
    expect_fail: "uninitialized const",
);

source_test!(
    STD_08, recursive_const,
    items: r#"
        const int NO_ERROR_HERE = UH_OH;  // <-- this one should not be part of the error
        const int UH_OH = UMMMM;
        const int UMMMM = HALP;
        const int HALP = UH_OH;
    "#,
    expect_fail: "depends on its own value",
);

source_test!(
    ANM_06, eosd_anm_early_end,
    main_body: r#"
        ins_0();
        pos(0f, 0f, 0f);
    "#,
    expect_fail: "after end",
);

source_test!(
    STD_08, interrupt_new_lines,
    // This tests that a user provided @mask overrides the one that gets automatically computed.
    main_body: r#"
        interrupt[1]:
        posKeyframe(0.0, 0.0, 0.0);
        interrupt[2]:
        interrupt[3]:
        posKeyframe(0.0, 0.0, 0.0);
    "#,
    sbsb: |decompiled| {
        // test for blank line before interrupt[2] but NOT before interrupt[3]
        assert!(decompiled.contains("\n\ninterrupt[2]:\ninterrupt[3]:\n"), "{:?}", decompiled);
    },
);

source_test!(
    STD_08, arg_count_range,
    main_body: r#"
        ins_2();
    "#,
    expect_fail: "expects 1 to 3 arguments",
);

source_test!(
    STD_08, arg_count_fixed,
    main_body: r#"
        posKeyframe(0f, 0f, 0f, 0f);
    "#,
    expect_fail: "expects 3 arguments",
);

// TODO: STD script requirements (single sub called main...)

source_test!(
    ANM_10, pseudo_blob,
    // This tests that a user provided @mask overrides the one that gets automatically computed.
    main_body: r#"
        anchor(@blob="01000200");
    "#,
    sbsb: |decompiled| {
        assert!(decompiled.contains("(1, 2)"));  // turned into words
    },
);

source_test!(
    ANM_10, pseudo_mask_override,
    // This tests that a user provided @mask overrides the one that gets automatically computed.
    main_body: r#"
        color(@mask=0b100, I2, 10, 20);
    "#,
    sbsb: |decompiled| {
        assert!(decompiled.contains("[20]"));  // turned into reg
        assert!(decompiled.contains("10002,"));  // turned into immediate
    },
);

source_test!(
    ANM_10, pseudo_in_const_call,
    items: r#"
        const int foo(int x) { return x; }
    "#,
    main_body: r#"
        int x = foo(@mask=0b1, 12);
    "#,
    // FIXME: Eventually, const funcs in anm will be supported.
    expect_fail: expected::NOT_SUPPORTED_BY_FORMAT,
);

source_test!(
    ANM_10, pseudo_in_inline_call,
    items: r#"
        inline void foo(int x) { wait(x); }
    "#,
    main_body: r#"
        foo(@mask=0b1, 12);
    "#,
    // FIXME: Eventually, inline funcs in anm will be supported.
    expect_fail: expected::NOT_SUPPORTED_BY_FORMAT,
);

source_test!(
    ANM_10, pseudo_after_arg,
    main_body: r#"
        wait(12, @mask=0b1);
    "#,
    expect_fail: "before",
);

source_test!(
    ANM_10, pseudo_blob_with_arg,
    main_body: r#"
        wait(@blob="0f000000", 15);
    "#,
    expect_fail: "redundant",
);

source_test!(
    ANM_10, pseudo_bad_name,
    main_body: r#"
        wait(@blobloblob="0f000000");
    "#,
    expect_fail: "pseudo",
);

source_test!(
    ANM_10, pseudo_len_ndiv_4,
    main_body: r#"
        wait(@blob="0f0000");
    "#,
    expect_fail: "by 4",
);

source_test!(
    ANM_10, pseudo_dupe,
    main_body: r#"
        wait(@blob="0f000000", @blob="0f000000");
    "#,
    expect_fail: "duplicate",
);

source_test!(
    ANM_10, pseudo_non_const,
    main_body: r#"
        I0 = 1;
        wait(@mask=I0, @blob="10270000");
    "#,
    expect_fail: "const",
);


source_test!(
    STD_08, shift_jis_in_source_file,
    full_source: {
        let mut text = vec![];
        text.extend(r#"
#pragma mapfile "map/any.stdm"

meta {
    unknown: 0,
    stage_name: "#.bytes());
        text.extend(b"\"\x82\xB1\x82\xF1\x82\xC9\x82\xBF\x82\xCD\"".iter().copied());
        text.extend(r#",
    bgm: [
        {path: "bgm/th08_08.mid", name: "dm"},
        {path: "bgm/th08_09.mid", name: "dm"},
        {path: " ", name: " "},
        {path: " ", name: " "},
    ],
    objects: {},
    instances: [],
}

sub main() {}
    "#.bytes());
        text
    },
    expect_fail: "UTF-8",
);

source_test!(
    MSG_06, encoding_error_in_arg,
    main_body: r#"  textSet(0, 0, "⏄");  "#,  // character not available in SJIS
    expect_fail: "JIS",
);

source_test!(
    STD_08, encoding_error_in_meta,
    full_source: r#"
#pragma mapfile "map/any.stdm"

meta {
    unknown: 0,
    stage_name: "⏄",
    bgm: [
        {path: "bgm/th08_08.mid", name: "dm"},
        {path: "bgm/th08_09.mid", name: "dm"},
        {path: " ", name: " "},
        {path: " ", name: " "},
    ],
    objects: {},
    instances: [],
}

script main {}
    "#,
    expect_fail: "JIS",
);

source_test!(
    STD_08, std_string128_overflow,
    full_source: r#"
#pragma mapfile "map/any.stdm"

meta {
    unknown: 0,
    stage_name: "
0123456789abcdef 0123456789abcdef 0123456789abcdef
0123456789abcdef 0123456789abcdef 0123456789abcdef
0123456789abcdef 0123456789abcdef 0123456789abcdef
0123456789abcdef 0123456789abcdef 0123456789abcdef
0123456789abcdef 0123456789abcdef 0123456789abcdef
0123456789abcdef 0123456789abcdef 0123456789abcdef
",
    bgm: [
        {path: "bgm/th08_08.mid", name: "dm"},
        {path: "bgm/th08_09.mid", name: "dm"},
        {path: " ", name: " "},
        {path: " ", name: " "},
    ],
    objects: {},
    instances: [],
}

script main {}
    "#,
    expect_fail: "too long",
);
