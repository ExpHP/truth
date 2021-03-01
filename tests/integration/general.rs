use crate::integration_impl::formats::*;
use crate::integration_impl::expected;

compile_fail_test!(
    ANM_10, mapfile_does_not_exist,
    items_before: r#"
        #pragma mapfile "this/is/a/bad/path"
    "#,
    main_body: "",
    expected: "loading mapfile",
);

compile_fail_test!(
    ANM_10, unknown_instr_signature,
    main_body: r#"  ins_6000(0, 0, 0);  "#,
    expected: "signature",
);

compile_fail_test!(
    ANM_10, unknown_instr_name,
    main_body: r#"  iMadeThisUpYesterday(0, 0, 0);  "#,
    expected: "unknown function",
);

compile_fail_test!(
    ANM_10, unknown_variable,
    main_body: r#"  int x = y;  "#,
    expected: "unknown variable",
);

compile_fail_test!(
    // even with explicit sigils, untyped vars simply can't exist in stackless langs
    ANM_10, stackless__untyped_var,
    main_body: r#"
        var x;
        $x = 4;
    "#,
    expected: expected::NOT_SUPPORTED_BY_FORMAT,
);

compile_fail_test!(
    ANM_10, anm_bitwise,
    main_body: r#"
        I0 = I0 | I1;
    "#,
    expected: expected::NOT_SUPPORTED_BY_FORMAT,
);

compile_fail_test!(
    ANM_10, bad_signature_in_mapfile,
    items_before: r#"
        #pragma mapfile "tests/mapfile-with-bad-signature.anmm"
    "#,
    main_body: "",
    expected: "opcode 1000",
);

compile_fail_test!(
    STD_08, jump_missing_label,
    main_body: r#"
        goto label;
    "#,
    expected: "undefined label",
);

compile_fail_test!(
    STD_08, duplicate_label,
    main_body: r#"
    label:
    label:
    "#,
    expected: "duplicate label",
);

compile_fail_test!(
    STD_08, local_in_std,
    main_body: r#"
        int x = 4;
    "#,
    expected: expected::NOT_SUPPORTED_BY_FORMAT,
);

compile_fail_test!(
    // this is going to become grammatically correct soon; the test is here to make
    // sure it fails gracefully from the getgo
    ANM_10, local_string,
    main_body: r#"
        string x = "hi";
    "#,
    expected: expected::PARSE_ERROR,
);

compile_fail_test!(
    // this is going to become grammatically correct soon; the test is here to make
    // sure it fails gracefully from the getgo
    ANM_10, local_named_after_reg,
    main_body: r#"
        int REG[100] = 3;
    "#,
    expected: expected::PARSE_ERROR,
);

compile_fail_test!(
    // this is going to become grammatically correct soon; the test is here to make
    // sure it fails gracefully from the getgo
    ANM_10, func_param_named_after_reg,
    items_before: r#"
        void foo(int REG[100]) {}
    "#,
    main_body: "",
    expected: expected::PARSE_ERROR,
);

compile_fail_test!(
    ANM_10, const_string_to_int,
    main_body: r#"
        const string x = "hi";
        const int y = $x;
    "#,
    // FIXME: this test might not be ready for a while.  Ultimately, the desired result
    //        is that it should parse successfully, and then get a type error at $x
    //        for being unable to cast a string to int.
    expected: expected::PARSE_ERROR,
);

compile_fail_test!(
    ANM_06, eosd_anm_early_end,
    main_body: r#"
        ins_0();
        pos(0f, 0f, 0f);
    "#,
    expected: "after end",
);

compile_fail_test!(
    STD_08, arg_count_range,
    main_body: r#"
        ins_2();
    "#,
    expected: "expects 1 to 3 arguments",
);

compile_fail_test!(
    STD_08, arg_count_fixed,
    main_body: r#"
        posKeyframe(0f, 0f, 0f, 0f);
    "#,
    expected: "expects 3 arguments",
);

// TODO: STD script requirements (single sub called main...)

// FIXME: ADDTEST pseudo blob success

#[test]
fn pseudo_mask_override() {
    // This tests that a user provided @mask overrides the one that gets automatically computed.
    ANM_10.sbsb_test(r#"
        color(@mask=0b100, I2, 10, 20);
    "#, |decompiled| {
        assert!(decompiled.contains("[20]"));  // turned into reg
        assert!(decompiled.contains("10002,"));  // turned into immediate
    });
}

compile_fail_test!(
    ANM_10, pseudo_in_const_call,
    items_before: r#"
        const int foo(int x) { return x; }
    "#,
    main_body: r#"
        int x = foo(@mask=0b1, 12);
    "#,
    // FIXME: Eventually, this should parse.
    expected: expected::PARSE_ERROR,
);

compile_fail_test!(
    ANM_10, pseudo_in_inline_call,
    items_before: r#"
        inline void foo(int x) { wait(x); }
    "#,
    main_body: r#"
        foo(@mask=0b1, 12);
    "#,
    // FIXME: Eventually, inline funcs in anm will be supported.
    expected: expected::UNIMPLEMENTED,
);

compile_fail_test!(
    ANM_10, pseudo_after_arg,
    main_body: r#"
        wait(12, @mask=0b1);
    "#,
    expected: "before",
);

compile_fail_test!(
    ANM_10, pseudo_blob_with_arg,
    main_body: r#"
        wait(@blob="0f000000", 15);
    "#,
    expected: "redundant",
);

compile_fail_test!(
    ANM_10, pseudo_bad_name,
    main_body: r#"
        wait(@blobloblob="0f000000");
    "#,
    expected: "pseudo",
);

compile_fail_test!(
    ANM_10, pseudo_len_ndiv_4,
    main_body: r#"
        wait(@blob="0f0000");
    "#,
    expected: "by 4",
);

compile_fail_test!(
    ANM_10, pseudo_dupe,
    main_body: r#"
        wait(@blob="0f000000", @blob="0f000000");
    "#,
    expected: "duplicate",
);

compile_fail_test!(
    ANM_10, pseudo_non_const,
    main_body: r#"
        I0 = 1;
        wait(@mask=I0, @blob="10270000");
    "#,
    expected: "const",
);


compile_fail_test!(
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
    expected: "UTF-8",
);

compile_fail_test!(
    MSG_06, encoding_error_in_arg,
    main_body: r#"  textSet(0, 0, "⏄");  "#,  // character not available in SJIS
    expected: "JIS",
);

compile_fail_test!(
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
    expected: "JIS",
);

compile_fail_test!(
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
    expected: "too long",
);
