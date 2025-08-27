#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

source_test!(
    STD_08, shift_jis_in_source_file,
    full_source: {
        // this input is invalid utf-8; build it from a byte vec
        let mut text = vec![];
        text.extend(r#"
#pragma mapfile "map/any.stdm"

meta {
    unknown: 0,
    stage_name: "#.bytes());
        text.extend(b"\"\x82\xB1\x82\xF1\x82\xC9\x82\xBF\x82\xCD\"".iter().copied());
        text.extend(r#",  //~ ERROR UTF-8
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
);

source_test!(
    MSG_06, encoding_error_in_arg,
    // character not available in SJIS
    main_body: r#"  textSet(0, 0, "⏄");  //~ ERROR JIS "#,
);

source_test!(
    STD_08, encoding_error_in_meta,
    full_source: r#"
#pragma mapfile "map/any.stdm"

meta {
    unknown: 0,
    stage_name: "⏄",  //~ ERROR JIS
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
",                                    //~^^^^^^^ ERROR too long
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
);

source_test!(
    #[ignore = "FIXME:  Test is known broken because currently the implementation of 'imm' in signatures obscures the param mask"]
    ANM_10, decompile_string_reg,
    mapfile: r#"!anmmap
!ins_signatures
444  z(bs=4)
    "#,
    main_body: r#"
    ins_444(@mask=0b1, "abc");
    "#,
    expect_decompile_error: "register bit",
);

const STRING_ABI_TEST_SIGNATURES: &'static str = r#"!eclmap
!ins_names
444 block
555 fixed
666 nulless
!ins_signatures
444  z(bs=4)
555  z(len=8)
666  z(len=8;nulless)
"#;

source_test!(
    ECL_06, compile_string_arg_with_null,
    mapfile: STRING_ABI_TEST_SIGNATURES,
    main_body: r#"
    block("abc\0");
    block("a\0b");
    block("abc\0abd"); // null at end of interior block
    fixed("abc\0def");
    "#,
    check_compiled: |output, format| {
        let ecl = output.read_olde_ecl(format);
        assert_eq!(&ecl.subs[0][0].args_blob[..4], "abc\0".as_bytes());
        assert_eq!(ecl.subs[0][1].args_blob, "a\0b\0".as_bytes().to_vec());
        assert_eq!(ecl.subs[0][2].args_blob, "abc\0abd\0".as_bytes().to_vec());
        assert_eq!(ecl.subs[0][3].args_blob, "abc\0def\0".as_bytes().to_vec());
    },
);

source_test!(
    ECL_06, decompile_string_arg_with_null_1,
    mapfile: STRING_ABI_TEST_SIGNATURES,
    main_body: r#" block("a\0b"); "#,
    expect_decompile_warning: "first null",
    require_roundtrip: false,
);

source_test!(
    ECL_06, decompile_string_arg_with_null_2,
    mapfile: STRING_ABI_TEST_SIGNATURES,
    // null at end of interior block
    main_body: r#" block("abc\0abd"); "#,
    expect_decompile_warning: "first null",
    require_roundtrip: false,
);

source_test!(
    ECL_06, decompile_string_arg_with_null_3,
    mapfile: STRING_ABI_TEST_SIGNATURES,
    main_body: r#" fixed("abc\0def"); "#,
    expect_decompile_warning: "first null",
    require_roundtrip: false,
);

source_test!(
    ECL_06, decompile_string_arg_with_null_4,
    mapfile: STRING_ABI_TEST_SIGNATURES,
    main_body: r#" nulless("abc\0def"); "#,
    expect_decompile_warning: "first null",
    require_roundtrip: false,
);

source_test!(
    ECL_06, decompile_string_arg_without_null_bs,
    mapfile: STRING_ABI_TEST_SIGNATURES,
    main_body: r#" block(@blob="40404040"); "#,
    expect_decompile_warning: "missing null terminator",
    require_roundtrip: false,
);

source_test!(
    ECL_06, decompile_string_arg_without_null_fixed,
    mapfile: STRING_ABI_TEST_SIGNATURES,
    main_body: r#" fixed(@blob="40404040 40404040"); "#,
    expect_decompile_warning: "missing null terminator",
    recompile: false,
);

source_test!(
    ECL_06, decompile_string_arg_without_null_nulless,
    mapfile: STRING_ABI_TEST_SIGNATURES,
    main_body: r#" nulless(@blob="40404040 40404040"); "#,
    check_decompiled: |text| assert!(text.contains("\"@@@@@@@@\"")),
);

source_test!(
    ECL_06, compile_string_arg_too_big_eq,
    mapfile: STRING_ABI_TEST_SIGNATURES,
    main_body: r#"
    fixed("abcdefgh");  //~ ERROR too large
    "#,
);

source_test!(
    ECL_06, compile_string_arg_too_big_gt,
    mapfile: STRING_ABI_TEST_SIGNATURES,
    main_body: r#"
    fixed("abcdefghi");  //~ ERROR too large
    "#,
);

source_test!(
    ECL_06, compile_string_arg_too_big_eq_nulless,
    mapfile: STRING_ABI_TEST_SIGNATURES,
    main_body: r#"
    nulless("abcdefgh");
    "#,
    check_compiled: |output, format| {
        let ecl = output.read_olde_ecl(format);
        assert_eq!(ecl.subs[0][0].args_blob, b"abcdefgh");
    }
);

source_test!(
    ECL_06, compile_string_arg_too_big_gt_nulless,
    mapfile: STRING_ABI_TEST_SIGNATURES,
    main_body: r#"
    nulless("abcdefghi");  //~ ERROR too large
    "#,
);
