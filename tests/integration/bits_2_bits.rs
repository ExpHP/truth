//! A test that decompiles and recompile a file to test that the result is bit-for-bit identical.
//!
//! This is primarily for regression testing against changes that would break bit-for-bit recompilation.
//!
//! Typically used via the [`b2b_test`] macro which also does an insta snapshot of the text; this
//! can give clues on possible causes of trouble.
//!
//! Tests for things like loop- and if- decompilation (which used to be here) are better suited to the
//! [`Self::sbsb_test`], which start from a readable script file.

use crate::integration_impl::formats::*;

#[track_caller]
fn file(fname: &str) -> std::path::PathBuf {
    let mut path = std::path::PathBuf::from("tests/integration/bits-2-bits");
    path.push(fname);
    assert!(path.exists());
    path
}

macro_rules! b2b_test {
    (   $format:expr, $map:expr, $test_name:ident, $fname:literal
        // Expected strings, all of which must be contained somewhere in the output for the test to succeed.
        // These can serve to help clarify what the test is actually testing for, and they serve as an
        // additional speed-bump against accidentally accepting a broken snapshot.
        //
        // Some tests don't have any expected strings; those tests are most likely only concerned that the
        // data can be round-tripped back to binary.
        $(, expected=$expected:literal)*
        $(,)?
    ) => {
        #[test]
        fn $test_name() {
            $format.bits_to_bits(file($fname), $map, |s| {
                $( assert!(s.contains($expected)); )*
                insta::assert_snapshot!(s)
            });
        }
    }
}

// a dumb test to make sure that we don't just dump files in the input directory and
// forget to add tests for them.
#[test]
fn all_files_tested() {
    let mut not_mentioned = vec![];
    let this_file_src = std::fs::read_to_string(file!()).unwrap();
    for entry in std::fs::read_dir("tests/integration/bits-2-bits").unwrap() {
        let path = entry.unwrap().path();
        if path.is_file() {
            let file_name = path.file_name().unwrap().to_str().unwrap();

            if !this_file_src.contains(file_name) {
                not_mentioned.push(file_name.to_string());
            }
        }
    }

    if !not_mentioned.is_empty() {
        panic!("Files not mentioned in {}: {:?}", file!(), not_mentioned);
    }
}

// STD metadata.
b2b_test!(STD_08, "map/any.stdm", std08_rects, "th08-rects.std");
b2b_test!(STD_08, "map/any.stdm", std08_strip, "th08-strip.std");
b2b_test!(STD_08, "map/any.stdm", std08_instance_order, "th08-instance-order.std");
b2b_test!(STD_08, "map/any.stdm", std08_nonzero_padding, "th08-nonzero-padding.std");
b2b_test!(STD_08, "map/any.stdm", std08_empty_script, "th08-empty-script.std");
b2b_test!(STD_06, "map/any.stdm", std06_general, "th06-general.std");
b2b_test!(STD_12, "map/any.stdm", std12_general, "th12-general.std");

// Test that named regs use are named in the output.
b2b_test!(
    ANM_12, "map/any.anmm", anm12_registers, "th12-registers.anm",
    expected="I1",
);
// Decompilation of instructions with no signature.
b2b_test!(
    ANM_12, file("th12-unknown-signature.anmm"), anm12_unknown_signature, "th12-unknown-signature.anm",
    expected="hasNameButNoSignature",  // there's a named instr with no signature in the mapfile...
    expected="ins_1011",  // ...as well as an unnamed one.
);

// Decompilation of word-sized arguments.
b2b_test!(ANM_12, "map/any.anmm", anm12_anchor_ss_signature, "th12-anchor-ss-signature.anm");

// Decompilation of sprite/script args to use names when appropriate.
b2b_test!(
    ANM_12, "map/any.anmm", anm12_sprite_script_args, "th12-sprite-script-args.anm",
    expected="scriptNew(script1)",
    expected="sprite(sprite0)",
);
b2b_test!(
    ANM_12, "map/any.anmm", anm12_sprite_unset, "th12-sprite-unset.anm",
    expected="sprite(-1)",
);
b2b_test!(
    ANM_12, "map/any.anmm", anm12_sprite_non_sequential, "th12-sprite-non-sequential.anm",
    expected="sprite47",
);
b2b_test!(
    ANM_12, "map/any.anmm", anm12_sprite_duplicates, "th12-sprite-duplicates.anm",
);

// MSG script table funny business.
b2b_test!(MSG_06, "map/any.msgm", msg06_multiple_scripts, "th06-multiple-scripts.msg");

// Decoding of string arguments.
b2b_test!(MSG_06, "map/any.msgm", msg06_z_string, "th06-z-string.msg");
b2b_test!(MSG_08, "map/any.msgm", msg08_m_string, "th08-m-string.msg");
b2b_test!(MSG_09, "map/any.msgm", msg09_m_string, "th09-m-string.msg");
b2b_test!(MSG_09, "map/any.msgm", msg09_default_mismatched_flags, "th09-default-mismatched-flags.msg");
b2b_test!(MSG_09, "map/any.msgm", msg09_default_zero_with_flags, "th09-default-zero-with-flags.msg");
b2b_test!(MSG_09, "map/any.msgm", msg09_default_zero, "th09-default-zero.msg");
b2b_test!(MSG_09, "map/any.msgm", msg09_no_default, "th09-no-default.msg");

// TH11 MSG has furigana but does not yet have the furigana encoding bug in masked strings.
b2b_test!(MSG_11, "map/any.msgm", msg11_furibug_not_applicable, "th11-furibug-not-applicable.msg");
// Typical furigana bug example.
b2b_test!(MSG_12, "map/any.msgm", msg12_furibug, "th12-furibug.msg");
// Example with particular string length that caused a bug in TH17 Extra.
b2b_test!(MSG_17, "map/any.msgm", msg17_furibug_ex_regression, "th17-furibug-ex-regression.msg");
