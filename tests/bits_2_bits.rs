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
    ($format:expr, $game:expr, $map:literal, $test_name:ident, $fname:literal) => {
        #[test]
        fn $test_name() {
            bits_to_bits($format, $game, file($fname), $map, |s| insta::assert_snapshot!(s));
        }
    }
}

macro_rules! std_b2b_test {
    ($game:expr, $map:literal, $test_name:ident, $fname:literal) => {
        b2b_test!{"trustd", $game, $map, $test_name, $fname}
    }
}

macro_rules! anm_b2b_test {
    ($game:expr, $map:literal, $test_name:ident, $fname:literal) => {
        b2b_test!{"truanm", $game, $map, $test_name, $fname}
    }
}

macro_rules! msg_b2b_test {
    ($game:expr, $map:literal, $test_name:ident, $fname:literal) => {
        b2b_test!{"trumsg", $game, $map, $test_name, $fname}
    }
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

std_b2b_test!(Game::Th08, "map/any.stdm", std08_rects, "th08-rects.std");
std_b2b_test!(Game::Th08, "map/any.stdm", std08_strip, "th08-strip.std");
std_b2b_test!(Game::Th08, "map/any.stdm", std08_instance_order, "th08-instance-order.std");
std_b2b_test!(Game::Th08, "map/any.stdm", std08_nonzero_padding, "th08-nonzero-padding.std");
std_b2b_test!(Game::Th08, "map/any.stdm", std08_empty_script, "th08-empty-script.std");
std_b2b_test!(Game::Th06, "map/any.stdm", std06_general, "th06-general.std");
std_b2b_test!(Game::Th12, "map/any.stdm", std12_general, "th12-general.std");

anm_b2b_test!(Game::Th12, "map/any.anmm", anm12_registers, "th12-registers.anm");
anm_b2b_test!(Game::Th12, "map/any.anmm", anm12_anchor_ss_signature, "th12-anchor-ss-signature.anm");

msg_b2b_test!(Game::Th06, "map/any.msgm", msg06_multiple_scripts, "th06-multiple-scripts.msg");
msg_b2b_test!(Game::Th06, "map/any.msgm", msg06_z_string, "th06-z-string.msg");
msg_b2b_test!(Game::Th08, "map/any.msgm", msg08_m_string, "th08-m-string.msg");
