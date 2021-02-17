// Tests that decompile and recompile a file to test that the result is bit-for-bit identical.
//
// This is primarily for regression testing against changes that would break bit-for-bit recompilation.
//
// They also do insta snapshots to give clues on possible causes of trouble.
//
// Tests for things like loop- and if- decompilation (which used to be here) are better suited to the
// `sbsb` test, which start from a readable script file.

use std::path::Path;
use std::process::Command;

use truth::Game;

use assert_cmd::prelude::*;

fn bits_to_bits(
    command: &str,
    game: Game,
    infile: impl AsRef<Path>,
    mapfile: impl AsRef<Path>,
    do_with_text: impl FnOnce(&str),
) {
    truth::setup_for_test_harness();

    let temp = tempfile::tempdir().unwrap();
    let temp = temp.path();
    let output = {
        Command::cargo_bin(command).unwrap()
            .arg("decompile")
            .arg("-g").arg(format!("{}", game))
            .arg("-m").arg(mapfile.as_ref())
            .arg(infile.as_ref().canonicalize().unwrap())
            .output().expect("failed to execute process")
    };
    let decompiled = output.stdout;
    if !output.stderr.is_empty() {
        eprintln!("== BINARY STDERR:");
        eprintln!("{}", String::from_utf8_lossy(&output.stderr));
    }
    if !output.status.success() {
        panic!("process failed")
    }

    do_with_text(&String::from_utf8_lossy(&decompiled));

    std::fs::write(temp.join("test.spec"), &decompiled).unwrap();

    assert!({
        Command::cargo_bin(command).unwrap()
            .arg("compile")
            .arg("-g").arg(format!("{}", game))
            .arg("-m").arg(mapfile.as_ref())
            .arg(temp.join("test.spec"))
            .arg("-o").arg(temp.join("test.bin"))
            .status().expect("failed to execute process")
            .success()
    });

    let original = std::fs::read(infile).unwrap();
    let recompiled = std::fs::read(temp.join("test.bin")).unwrap();
    assert_eq!(original, recompiled);
}

#[track_caller]
fn file(fname: &str) -> std::path::PathBuf {
    let mut path = std::path::PathBuf::from("tests/bits-2-bits");
    path.push(fname);
    assert!(path.exists());
    path
}

macro_rules! b2b_test {
    (   $format:expr,
        $game:expr, $map:expr, $test_name:ident, $fname:literal
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
            bits_to_bits($format, $game, file($fname), $map, |s| {
                $( assert!(s.contains($expected)); )*
                insta::assert_snapshot!(s)
            });
        }
    }
}

macro_rules! std_b2b_test {
    ($($args:tt)*) => { b2b_test!{"trustd", $($args)*} };
}

macro_rules! anm_b2b_test {
    ($($args:tt)*) => { b2b_test!{"truanm", $($args)*} };
}

macro_rules! msg_b2b_test {
    ($($args:tt)+) => { b2b_test!{"trumsg", $($args)*} };
}

// a dumb test to make sure that we don't just dump files in the input directory and
// forget to add tests for them.
#[test]
fn all_files_tested() {
    let mut not_mentioned = vec![];
    let this_file_src = std::fs::read_to_string(file!()).unwrap();
    for entry in std::fs::read_dir("tests/bits-2-bits").unwrap() {
        let path = entry.unwrap().path();
        if path.is_file() && ["anm", "std", "msg"].iter().any(|&ext| path.extension().unwrap() == ext)  {
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
std_b2b_test!(Game::Th08, "map/any.stdm", std08_rects, "th08-rects.std");
std_b2b_test!(Game::Th08, "map/any.stdm", std08_strip, "th08-strip.std");
std_b2b_test!(Game::Th08, "map/any.stdm", std08_instance_order, "th08-instance-order.std");
std_b2b_test!(Game::Th08, "map/any.stdm", std08_nonzero_padding, "th08-nonzero-padding.std");
std_b2b_test!(Game::Th08, "map/any.stdm", std08_empty_script, "th08-empty-script.std");
std_b2b_test!(Game::Th06, "map/any.stdm", std06_general, "th06-general.std");
std_b2b_test!(Game::Th12, "map/any.stdm", std12_general, "th12-general.std");

// Test that named regs use are named in the output.
anm_b2b_test!(
    Game::Th12, "map/any.anmm", anm12_registers, "th12-registers.anm",
    expected="I1",
);
// Decompilation of instructions with no signature.
anm_b2b_test!(
    Game::Th12, file("th12-unknown-signature.anmm"), anm12_unknown_signature, "th12-unknown-signature.anm",
    expected="hasNameButNoSignature",  // there's a named instr with no signature in the mapfile...
    expected="ins_1011",  // ...as well as an unnamed one.
);

// Decompilation of word-sized arguments.
anm_b2b_test!(Game::Th12, "map/any.anmm", anm12_anchor_ss_signature, "th12-anchor-ss-signature.anm");

// Decompilation of sprite/script args to use names when appropriate.
anm_b2b_test!(
    Game::Th12, "map/any.anmm", anm12_sprite_script_args, "th12-sprite-script-args.anm",
    expected="scriptNew(script1)",
    expected="sprite(sprite0)",
);
anm_b2b_test!(
    Game::Th12, "map/any.anmm", anm12_sprite_unset, "th12-sprite-unset.anm",
    expected="sprite(-1)",
);
anm_b2b_test!(
    Game::Th12, "map/any.anmm", anm12_sprite_non_sequential, "th12-sprite-non-sequential.anm",
    expected="sprite47",
);
anm_b2b_test!(
    Game::Th12, "map/any.anmm", anm12_sprite_duplicates, "th12-sprite-duplicates.anm",
);

// MSG script table funny business.
msg_b2b_test!(Game::Th06, "map/any.msgm", msg06_multiple_scripts, "th06-multiple-scripts.msg");

// Decoding of string arguments.
msg_b2b_test!(Game::Th06, "map/any.msgm", msg06_z_string, "th06-z-string.msg");
msg_b2b_test!(Game::Th08, "map/any.msgm", msg08_m_string, "th08-m-string.msg");
