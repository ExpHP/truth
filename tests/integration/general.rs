use crate::integration_impl::formats::*;
use crate::integration_impl::expected;

source_test!(
    ANM_10, mapfile_does_not_exist,
    items: r#"
        #pragma mapfile "this/is/a/bad/path"
    "#,
    expect_error: "while resolving",
);

source_test!(
    ANM_10, unknown_instr_signature,
    main_body: r#"  ins_6000(0, 0, 0);  "#,
    expect_error: "signature",
);

source_test!(
    ANM_10, unknown_instr_name,
    main_body: r#"  iMadeThisUpYesterday(0, 0, 0);  "#,
    expect_error: "instruction or function",
);

source_test!(
    ANM_10, unknown_variable,
    main_body: r#"  int x = y;  "#,
    expect_error: "register or variable",
);

source_test!(
    // even with explicit sigils, untyped vars simply can't exist in stackless langs
    ANM_10, stackless__untyped_var,
    main_body: r#"
        var x;
        $x = 4;
    "#,
    expect_error: expected::NOT_SUPPORTED_BY_FORMAT,
);

source_test!(
    ANM_10, anm_bitwise,
    main_body: r#"
        I0 = I0 | I1;
    "#,
    expect_error: expected::NOT_SUPPORTED_BY_FORMAT,
);

source_test!(
    ANM_10, shift_const_eval,
    main_body: r#"
        const int SHL = 0xFFABCD01 << 4;
        const int SAR = 0xFFABCD01 >> 4;
        const int SHR = 0xFFABCD01 >>> 4;
        int x = SHL;
        int y = SAR;
        int z = SHR;
    "#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        assert_eq!(&anm.entries[0].scripts[0].instrs[0].args_blob[4..], &blobify![0xFABCD010u32 as i32][..]);
        assert_eq!(&anm.entries[0].scripts[0].instrs[1].args_blob[4..], &blobify![0xFFFABCD0u32 as i32][..]);
        assert_eq!(&anm.entries[0].scripts[0].instrs[2].args_blob[4..], &blobify![0x0FFABCD0u32 as i32][..]);
    },
);

source_test!(
    ANM_10, bad_signature_in_mapfile,
    mapfile: r#"!anmmap
!ins_signatures
1000 z(bs=4)S
"#,
    main_body: "",
    expect_error: "can only appear at the very end",
);

source_test!(
    STD_08, jump_missing_label,
    main_body: r#"
        goto label;
    "#,
    expect_error: "undefined label",
);

source_test!(
    STD_08, duplicate_label,
    main_body: r#"
    label:
    label:
    "#,
    expect_error: "duplicate label",
);

source_test!(
    STD_08, break_outside_loop,
    main_body: r#"
        break;
    "#,
    expect_error: "outside of a loop",
);

source_test!(
    STD_08, break_used_properly,
    main_body: r#"
        loop {
            break;
        }
    "#,
    // more in-depth tests of break semantics in expr_compile.rs,
    // this is just here as a test control
    check_compiled: |_, _| {},
);

source_test!(
    STD_08, break_outside_loop_in_nested_func,
    main_body: r#"
        loop {
            const void nowHeyWhatsThis() {
                break;
            }
        }
    "#,
    expect_error: "outside of a loop",
);

source_test!(
    STD_08, local_in_std,
    main_body: r#"
        int x = 4;
    "#,
    expect_error: expected::NOT_SUPPORTED_BY_FORMAT,
);

source_test!(
    ANM_10, local_string,
    main_body: r#"
        string x = "hi";
    "#,
    expect_error: "non-const",
);

source_test!(
    ANM_10, local_void,
    main_body: r#"
        void x = delete();
    "#,
    expect_error: "must have a value",
);

source_test!(
    ANM_10, const_void,
    items: r#"
        const void x = delete();
    "#,
    expect_error: "must have a value",
);

source_test!(
    ANM_10, const_untyped,
    items: r#"
        const var x = 3;
    "#,
    expect_error: "untyped",
);

source_test!(
    ANM_10, const_reg,
    items: r#"
        const int y = $REG[10000];
    "#,
    expect_error: "const context",
);

source_test!(
    ANM_10, func_untyped,
    items: r#"
        var foo() { return 1; }
    "#,
    expect_error: "var-typed",
);

// FIXME: change this test to ECL once that is available
source_test!(
    // this is going to become grammatically correct eventually; the test is here to make
    // sure it fails gracefully from the getgo
    ANM_10, func_nonconst_string,
    items: r#"
        string foo() { return "hi"; }
    "#,
    expect_error: expected::NOT_SUPPORTED_BY_FORMAT,
);

source_test!(
    ANM_10, func_inline_const,
    items: r#"
        inline const int foo() { return 1; }
    "#,
    expect_error: "extra qualifier",
);

source_test!(
    ANM_10, func_const_reg,
    items: r#"
        const int foo() {
            int x = 3 + $REG[10000];
            return x;
        }
    "#,
    expect_error: "const context",
);

source_test!(
    ANM_10, func_const_ins,
    items: r#"
        const int foo() {
            ins_23();
            return 5;
        }
    "#,
    expect_error: "const context",
);

source_test!(
    ANM_10, local_variable,
    main_body: r#"
        int x = 3;
        float y = 3.0;
    "#,
    check_compiled: |_, _| {},
);

source_test!(
    // this may become grammatically correct at some point; the test is here to make
    // sure it fails gracefully from the getgo
    ANM_10, local_named_after_reg,
    main_body: r#"
        int REG[100] = 3;
    "#,
    expect_error: expected::PARSE_ERROR,
);

source_test!(
    // this may become grammatically correct at some point; the test is here to make
    // sure it fails gracefully from the getgo
    ANM_10, func_param_named_after_reg,
    items: r#"
        void foo(int REG[100]) {}
    "#,
    expect_error: expected::PARSE_ERROR,
);

source_test!(
    ANM_10, builtin_consts_decomp,
    main_body: r#"
        F0 = INF;
        F0 = -INF;
        F0 = NAN;
    "#,
    sbsb: |decompiled| {
        assert!(decompiled.contains("= INF;"));
        assert!(decompiled.contains("= -INF;"));
        assert!(decompiled.contains("= NAN;"));
    },
);

source_test!(
    ECL_06, builtin_consts_in_exprs,
    main_body: r#"
        F0 = 1.0 + INF;

        const float Q = 1.0 + INF;
        F1 = Q;
    "#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(&ecl.subs[0][0].args_blob[4..], &blobify![f32::INFINITY][..]);
        assert_eq!(&ecl.subs[0][1].args_blob[4..], &blobify![f32::INFINITY][..]);
    },
);

source_test!(
    ANM_10, const_string_to_int,
    items: r#"
        const string x = "hi";
        const int y = $x;
    "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, uninitialized_const,
    items: r#"
        const int y = 3, z, w = 4;
    "#,
    expect_error: "uninitialized const",
);

source_test!(
    STD_08, recursive_const,
    items: r#"
        const int NO_ERROR_HERE = UH_OH;  // <-- this one should not be part of the error
        const int UH_OH = UMMMM;
        const int UMMMM = HALP;
        const int HALP = UH_OH;
    "#,
    expect_error: "depends on its own value",
);

source_test!(
    ANM_06, eosd_anm_early_end,
    main_body: r#"
        ins_0();
        pos(0f, 0f, 0f);
    "#,
    expect_error: "after end",
);

source_test!(
    ECL_06, jump_offsetof_expression,
    // this check is currently preventing this from compiling into some weird multistatement thing
    // that tries to stick a register in an offset argument and that doesn't even really use the
    // correct offset to begin with (since ECL offsets are relative)
    main_body: r#"
        jump(30, (offsetof(label) + 4) * 2);
    label:
    "#,
    expect_error: "constant",
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
    ANM_12, interrupt_register,
    main_body: r#"
        ins_64(45);
        ins_64($REG[10000]);
    "#,
    sbsb: |decompiled| {
        // the second one should have fallen back to raw syntax
        assert!(decompiled.contains("($REG[10000])"));
        // specificity (prove that we have the right opcode)
        assert!(decompiled.contains("interrupt[45]"));
    },
);

source_test!(
    STD_08, arg_count_range,
    main_body: r#"
        ins_2();
    "#,
    expect_error: "expects 1 to 3 arguments",
);

source_test!(
    STD_08, arg_count_fixed,
    main_body: r#"
        posKeyframe(0f, 0f, 0f, 0f);
    "#,
    expect_error: "expects 3 arguments",
);

source_test!(
    MSG_06, reg_in_unsupported_lang,
    main_body: r#"  textSet(0, $REG[0], "cheese");  "#,
    expect_error: "constant",
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
    expect_error: "not an instruction",
);

source_test!(
    ANM_10, pseudo_in_inline_call,
    items: r#"
        inline void foo(int x) { wait(x); }
    "#,
    main_body: r#"
        foo(@mask=0b1, 12);
    "#,
    expect_error: "not an instruction",
);

source_test!(
    ANM_10, pseudo_after_arg,
    main_body: r#"
        wait(12, @mask=0b1);
    "#,
    expect_error: "before",
);

source_test!(
    ANM_10, pseudo_blob_with_arg,
    main_body: r#"
        wait(@blob="0f000000", 15);
    "#,
    expect_error: "redundant",
);

source_test!(
    ANM_10, pseudo_bad_name,
    main_body: r#"
        wait(@blobloblob="0f000000");
    "#,
    expect_error: "pseudo",
);

source_test!(
    ANM_10, pseudo_len_ndiv_4,
    main_body: r#"
        wait(@blob="0f0000");
    "#,
    expect_error: "by 4",
);

source_test!(
    ANM_10, pseudo_dupe,
    main_body: r#"
        wait(@blob="0f000000", @blob="0f000000");
    "#,
    expect_error: "duplicate",
);

source_test!(
    ANM_10, pseudo_non_const,
    main_body: r#"
        I0 = 1;
        wait(@mask=I0, @blob="10270000");
    "#,
    expect_error: "const",
);

// A snippet to try decompiling with several decreasing levels of features.
const SNIPPET_WITH_SEVERAL_INTRINSICS: &'static str = r#"
interrupt[10]:
label:
    I0 = I2 + 3;
    goto label @ 0;
"#;

source_test!(
    ANM_12, decompile_no_nothing,  // "control group" test that keeps it all enabled
    main_body: SNIPPET_WITH_SEVERAL_INTRINSICS,
    sbsb: |decompiled| {
        assert!(!decompiled.contains("goto "));
        assert!(decompiled.contains("loop"));
    },
);

source_test!(
    ANM_12, decompile_no_blocks,
    main_body: SNIPPET_WITH_SEVERAL_INTRINSICS,
    decompile_args: ["--no-blocks"],
    sbsb: |decompiled| {
        assert!(decompiled.contains("goto "));
        assert!(!decompiled.contains("loop"));
    },
);

source_test!(
    ANM_12, decompile_no_intrinsics,
    main_body: SNIPPET_WITH_SEVERAL_INTRINSICS,
    decompile_args: ["--no-intrinsics"],
    sbsb: |decompiled| {
        assert!(decompiled.contains("ins_64(10)"));
        assert!(decompiled.contains("ins_4(offsetof("));
        assert!(decompiled.contains("ins_18($REG[10000], $REG[10002], 3)"));
    },
);

source_test!(
    ANM_12, decompile_no_arguments,
    main_body: SNIPPET_WITH_SEVERAL_INTRINSICS,
    decompile_args: ["--no-arguments"],
    sbsb: |decompiled| {
        assert_eq!(decompiled.matches("@blob").count(), 3);
        assert_eq!(decompiled.matches("@mask").count(), 1);
    },
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
    expect_error: "UTF-8",
);

source_test!(
    MSG_06, encoding_error_in_arg,
    main_body: r#"  textSet(0, 0, "⏄");  "#,  // character not available in SJIS
    expect_error: "JIS",
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
    expect_error: "JIS",
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
    expect_error: "too long",
);
