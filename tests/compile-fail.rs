//! Tests for non-language-related features of anm-compile (notably image sources)
#![allow(non_snake_case)]

use std::ffi::OsStr;
use std::process::Command;

use assert_cmd::prelude::*;

use common::source_gen::*;
mod common;

lazy_static::lazy_static! {
    static ref TEMP_FILE_REGEX: regex::Regex = regex::Regex::new(r#"┌─ .+[/\\]original\.spec"#).unwrap();
}
const TEMP_FILE_REPLACEMENT: &'static str = "┌─ <input>";

impl Format {
    fn compile_fail_stderr(&self, other_items: &str, main_body: &str) -> String {
        truth::setup_for_test_harness();

        self.compile_fail_stderr_no_transform(format!(
            "{}\n{}\n{}",
            self.script_head,
            other_items,
            (self.make_main)(main_body),
        ))
    }

    fn compile_fail_stderr_no_transform<S: AsRef<[u8]>>(&self, full_source: S) -> String {
        use std::fs::{write};

        truth::setup_for_test_harness();

        let temp = tempfile::tempdir().unwrap();
        let temp = temp.path();

        write(temp.join("original.spec"), full_source).unwrap();
        self._compile_fail_stderr(temp.join("original.spec"))
    }

    fn _compile_fail_stderr(&self, src: impl AsRef<OsStr>) -> String {
        let output = {
            Command::cargo_bin(self.cmd).unwrap()
                .arg("compile")
                .arg("-g").arg(format!("{}", self.game))
                .arg(src)
                .arg("-o").arg("/dev/null")
                .output().expect("failed to execute process")
        };
        assert!(!output.status.success());

        self.make_output_deterministic(std::str::from_utf8(&output.stderr).unwrap())
    }

    fn make_output_deterministic(&self, stderr: &str) -> String {
        TEMP_FILE_REGEX.replace_all(stderr, TEMP_FILE_REPLACEMENT).into_owned()
    }
}

macro_rules! snapshot_path {
    () => { concat!(env!("CARGO_MANIFEST_DIR"), "/tests/compile-fail") }
}

// used to implement defaults for some optional macro parts by writing `first_token!( $($thing)?  "" )`
macro_rules! first_token {
    ($tok:tt $($rest:tt)*) => { $tok };
}

macro_rules! compile_fail_test {
    (
        $format:expr, $test_name:ident

        // (optional) other items you want in the script
        $(, items_before: $items_before:expr)?

        // the statements to compile into a function body
        , main_body: $main_body:expr

        // (optional) check that the STDERR text contains a substring.
        // This helps ensure that compilation is failing for a legitimate reason.
        //
        // It's okay if a change to the compiler breaks a test by causing it to produce a different error!
        // (e.g. because the order of passes changed, or something formerly unparseable is now parseable).
        // Whenever this occurs, just review the new outputs and make sure that the new errors are still
        // related to what they were originally testing.
        // This is intended to be a slightly larger speed-bump than other cases of insta-snapshot test breakage.
        $(, expected: $expected:expr)?
        $(,)?
    ) => {
        #[test]
        fn $test_name() {
            let stderr = $format.compile_fail_stderr(
                first_token!( $($items_before)? "" ),
                $main_body,
            );
            _check_compile_fail_output!(stderr $(, expected: $expected)?);
        }
    };
}

macro_rules! compile_fail_no_transform_test {
    (
        // This one is like compile_fail_test but takes the full source instead of just items and stmts.
        $format:expr, $test_name:ident

        , full_source: $main_body:expr

        $(, expected: $expected:expr)?
        $(,)?
    ) => {
        #[test]
        fn $test_name() {
            let stderr = $format.compile_fail_stderr_no_transform($main_body);
            _check_compile_fail_output!(stderr $(, expected: $expected)?);
        }
    };
}

macro_rules! _check_compile_fail_output {
    ($stderr:expr $(, expected: $expected:expr)?) => {{
        #![allow(unused_mut)]

        let stderr = $stderr;

        // we don't want internal compiler errors.
        let is_ice = (
            stderr.contains("panicked at") || stderr.contains("RUST_BACKTRACE=1")
            || stderr.contains("bug!") || stderr.contains("BUG!")
        );
        // hitting `unimplemented!` macro is okay if that's the expected error
        let is_accepted_ice = false $(|| ($expected == EXPECTED_UNIMPLEMENTED && stderr.contains($expected)))?;
        let is_bad_ice = is_ice && !is_accepted_ice;
        assert!(!is_bad_ice, "INTERNAL COMPILER ERROR:\n{}", stderr);

        $( assert!(stderr.contains($expected), "Error did not contain expected! error: {}", stderr); )?
        insta::with_settings!{{snapshot_path => snapshot_path!()}, {
            insta::assert_snapshot!{stderr};
        }}
    }}
}

// stderr search strings for ubiquitous error messages
const EXPECTED_TYPE_ERROR: &'static str = "type error";
const EXPECTED_PARSE_ERROR: &'static str = "unexpected token";
const EXPECTED_UNIMPLEMENTED: &'static str = "not implemented";
const EXPECTED_NOT_SUPPORTED_BY_FORMAT: &'static str = "not supported";

// =============================================================================

compile_fail_test!(
    ANM_10, mapfile_does_not_exist,
    items_before: r#"
        #pragma mapfile "this/is/a/bad/path"
    "#,
    main_body: "",
    expected: "loading mapfile",
);

compile_fail_test!(
    ANM_10, image_source_does_not_exist,
    items_before: r#"
        #pragma image_source "this/is/a/bad/path"
    "#,
    main_body: "",
    expected: "reading file",
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
    expected: EXPECTED_NOT_SUPPORTED_BY_FORMAT,
);

compile_fail_test!(
    ANM_10, anm_bitwise,
    main_body: r#"
        I0 = I0 | I1;
    "#,
    expected: EXPECTED_NOT_SUPPORTED_BY_FORMAT,
);

compile_fail_test!(
    ANM_10, bad_signature_in_mapfile,
    items_before: r#"
        #pragma mapfile "tests/mapfile-with-bad-signature.anmm"
    "#,
    main_body: "",
    expected: "opcode 1000",
);

// FIXME somehow group these image_source tests so that new formats are automatically tested?
compile_fail_test!(
    STD_08, image_source_in_std,
    items_before: r#"
        #pragma image_source "tests/anm-compile/th12-embedded-image-source.anm"
    "#,
    main_body: "",
    expected: "unexpected image_source",
);
compile_fail_test!(
    MSG_06, image_source_in_msg,
    items_before: r#"
        #pragma image_source "tests/anm-compile/th12-embedded-image-source.anm"
    "#,
    main_body: "",
    expected: "unexpected image_source",
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
    expected: EXPECTED_NOT_SUPPORTED_BY_FORMAT,
);

compile_fail_test!(
    // this is going to become grammatically correct soon; the test is here to make
    // sure it fails gracefully from the getgo
    ANM_10, local_string,
    main_body: r#"
        string x = "hi";
    "#,
    expected: EXPECTED_PARSE_ERROR,
);

compile_fail_test!(
    // this is going to become grammatically correct soon; the test is here to make
    // sure it fails gracefully from the getgo
    ANM_10, local_named_after_reg,
    main_body: r#"
        int REG[100] = 3;
    "#,
    expected: EXPECTED_PARSE_ERROR,
);

compile_fail_test!(
    // this is going to become grammatically correct soon; the test is here to make
    // sure it fails gracefully from the getgo
    ANM_10, func_param_named_after_reg,
    items_before: r#"
        void foo(int REG[100]) {}
    "#,
    main_body: "",
    expected: EXPECTED_PARSE_ERROR,
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
    expected: EXPECTED_PARSE_ERROR,
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

compile_fail_test!(
    ANM_10, pseudo_in_const_call,
    items_before: r#"
        const int foo(int x) { return x; }
    "#,
    main_body: r#"
        int x = foo(@mask=0b1, 12);
    "#,
    // FIXME: Eventually, this should parse.
    expected: EXPECTED_PARSE_ERROR,
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
    expected: EXPECTED_UNIMPLEMENTED,
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
    ANM_10, meta_non_const,
    items_before: r#"
entry {
    path: "subdir/file-2.png",
    has_data: false,
    memory_priority: 3 * I0,
    low_res_scale: false,
    sprites: {
        sprite200: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 200},
    },
}
    "#,
    main_body: "",
    // NOTE: be careful changing this.  If the new error complains about missing fields
    // or missing image data, fix the test input instead.
    expected: "const",
);

compile_fail_test!(
    ANM_10, meta_sprite_id_non_const,
    items_before: r#"
entry {
    path: "subdir/file-2.png",
    has_data: false,
    memory_priority: 3 * I0,
    low_res_scale: false,
    sprites: {
        sprite200: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 3 * I0},
    },
}
    "#,
    main_body: "",
    expected: EXPECTED_NOT_SUPPORTED_BY_FORMAT, // FIXME:  eventually this should instead error about not being const
);

mod type_error {
    use super::*;

    // NOTE: 'stackless__' is a prefix for things that used to be type-checked during lowering
    //       (so they were special cases handled by the stackless lowerer), and 'const__' is a
    //       prefix for things that used to be type-checked during const folding.
    //
    //       All of these things are now type-checked during the dedicated type-checking pass,
    //       but we keep both of them in case that situation were to change again.

    compile_fail_test!(
        ANM_10, bad_declaration,
        main_body: r#"  int %x;  "#,
        expected: EXPECTED_PARSE_ERROR,  // currently 'int $x' is invalid too, but never say never...
    );

    // =========================
    // Stackless expression assignments

    compile_fail_test!(
        ANM_10, stackless__assign_literal,
        main_body: r#"  I0 = 4.0;  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, stackless__assign_var,
        main_body: r#"  I0 = F0;  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, stackless__assign_var_sigil,
        main_body: r#"  I0 = %I1;  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, stackless__binop_arg,
        main_body: r#"  F0 = F1 + 4;  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, stackless__binop_out,
        main_body: r#"  I0 = F1 + 2.0;  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        MSG_06, stackless__binop_two_strings,
        main_body: r#"  textSet(0, 0, "F1" - "2.0");  "#,
        expected: "string",
    );

    compile_fail_test!(
        ANM_10, const__binop,
        main_body: r#"  I0 = 1 + 2.0;  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, stackless__sine_arg,
        main_body: r#"  float x = sin(I0);  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, stackless__sine_out,
        main_body: r#"  int x = sin(F0);  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, const__sine,
        main_body: r#"  F0 = sin(1);  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, const__sprite,
        main_body: r#"  F0 = sprite0;  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, stackless__ternary_cond,
        main_body: r#"  F0 = F2 ? 1.0 : 2.0;  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, stackless__ternary_arg,
        main_body: r#"  F0 = I1 ? F1 : I0;  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, stackless__ternary_out,
        main_body: r#"  I0 = I0 ? F0 : F1;  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, const__ternary_cond,
        main_body: r#"  F0 = 1.5 ? 1.0 : 2.0;  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    // for ternary branch type mismatch in a const context, see the "short-circuit" tests below

    compile_fail_test!(
        ANM_10, stackless__binop_str,
        main_body: r#"  int x = I0 + "abc";  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, stackless__neg_str,
        main_body: r#"  int x = -"abc";  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        // ...hang on, should casting int to int really be an error?
        ANM_10, stackless__cast,
        main_body: r#"  int x = _S(I2);  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        // ...hang on, should casting int to int really be an error?
        ANM_10, const__cast,
        main_body: r#"  int x = _S(2);  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    // =========================
    // stackless jumps

    compile_fail_test!(
        ANM_10, stackless__jump_comparison_arg,
        main_body: r#"
            if (2 == 3.0) goto label;
          label:
        "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, stackless__jump_general_expr,
        main_body: r#"
            if (3.0) goto label;
          label:
        "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, stackless__jump_logical_arg,
        main_body: r#"
            if (2 && 3.0) goto label;
          label:
        "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, stackless__jump_logical_result,
        main_body: r#"
            if (2.0 && 3.0) goto label;
          label:
        "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, stackless__jump_predec_float,
        main_body: r#"
            if (--F0) goto label;
          label:
        "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, stackless__jump_time,
        main_body: r#"
            if (2 == 2) goto label @ 2.4;
          label:
        "#,
        expected: EXPECTED_PARSE_ERROR,
    );

    // =========================
    // stackless times

    compile_fail_test!(
        ANM_10, stackless__times_count,
        main_body: r#"  times(F0) {}  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, stackless__times_clobber,
        main_body: r#"  times(F0 = 4) {}  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    // =========================
    // stackless instruction arguments

    compile_fail_test!(
        ANM_10, stackless__ins_arg_var,
        main_body: r#"  pos(0.0, I0, 3.0);  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, stackless__ins_arg_literal,
        main_body: r#"  pos(0.0, 5, 3.0);  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, stackless__ins_arg_complex,
        main_body: r#"  pos(0.0, I0 + I2, 3.0);  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        MSG_06, stackless__func_arg_neg_str,
        main_body: r#"  textSet(0, 0, -"abc");  "#,
        expected: "string",
    );

    compile_fail_test!(
        ANM_10, stackless__pseudo,
        main_body: r#"  pos(@blob=12);  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    // =========================
    // expression statements

    compile_fail_test!(
        ANM_10, stackless__non_void_expr_statement,
        main_body: r#"  3.0;  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    // FIXME: Once we have ECL we should try `I0 ? "abc" : "def"` as an argument;
    //        this is more or less the only way guaranteed to hit a "no runtime string temporaries"
    //        check.  (at the time of writing, `-"abc"` and `"a" + "b"` currently hit it but, that's
    //        only because it's not currently caught during in const folding or shallow typing)

    // =========================
    // short-circuited const expressions

    // These tests look at subexpressions that get completely deleted from the AST during
    // constant folding.  We want to make sure they are still typechecked!

    compile_fail_test!(
        ANM_10, const__short_circuit__ternary_left,
        main_body: r#"  F0 = 5 ? 1.0 : 0;  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, const__short_circuit__ternary_right,
        main_body: r#"  F0 = 0 ? "lol" : 1.0;  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, const__short_circuit__and,
        main_body: r#"  I0 = 1 && "lmao";  "#,
        expected: EXPECTED_TYPE_ERROR,
    );

    compile_fail_test!(
        ANM_10, const__short_circuit__or,
        main_body: r#"  I0 = 0.0 || 1;  "#,
        expected: EXPECTED_TYPE_ERROR,
    );
}

compile_fail_no_transform_test!(
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

compile_fail_no_transform_test!(
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

compile_fail_no_transform_test!(
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
