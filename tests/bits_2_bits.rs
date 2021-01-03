// Tests that decompile and recompile .std to make sure it's bit-for-bit identical.
//
// They also do insta snapshots to give clues on possible causes of trouble.

use std::path::Path;
use std::process::Command;

use ecl_parser::Game;

use assert_cmd::prelude::*;

fn bits_to_bits(
    game: Game,
    infile: impl AsRef<Path>,
    mapfile: impl AsRef<Path>,
    do_with_text: impl FnOnce(&str),
) {
    let temp = tempfile::tempdir().unwrap();
    let temp = temp.path();
    let output = {
        Command::cargo_bin("std-decomp").unwrap()
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

    std::fs::write(temp.join("test.stdspec"), &decompiled).unwrap();

    assert!({
        Command::cargo_bin("std-compile").unwrap()
            .arg("-g").arg(format!("{}", game))
            .arg("-m").arg(mapfile.as_ref())
            .arg(temp.join("test.stdspec"))
            .arg("-o").arg(temp.join("test.std"))
            .status().expect("failed to execute process")
            .success()
    });

    let original = std::fs::read(infile).unwrap();
    let recompiled = std::fs::read(temp.join("test.std")).unwrap();
    assert_eq!(original, recompiled);
}

#[track_caller]
fn file(fname: &str) -> std::path::PathBuf {
    let mut path = std::path::PathBuf::from("tests/bits_2_bits");
    path.push(fname);
    assert!(path.exists());
    path
}

macro_rules! std_b2b_test {
    ($game:expr, $map:literal, $test_name:ident, $fname:literal) => {
        #[test]
        fn $test_name() {
            bits_to_bits($game, file($fname), $map, |s| insta::assert_snapshot!(s));
        }
    }
}

// a dumb test to make sure that we don't just dump files in the input directory and
// forget to add tests for them.
#[test]
fn all_files_tested() {
    let mut not_mentioned = vec![];
    let this_file_src = std::fs::read_to_string(file!()).unwrap();
    for entry in std::fs::read_dir("tests/bits_2_bits").unwrap() {
        let path = entry.unwrap().path();
        if path.is_file() && path.extension().unwrap() == "std" {
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
std_b2b_test!(Game::Th08, "map/any.stdm", std08_loop, "th08-loop.std");
std_b2b_test!(Game::Th08, "map/any.stdm", std08_instance_order, "th08-instance-order.std");
std_b2b_test!(Game::Th08, "map/any.stdm", std08_jump_forward, "th08-jump-forward.std");
std_b2b_test!(Game::Th08, "map/any.stdm", std08_loop_nonzero_time, "th08-loop-nonzero-time.std");
std_b2b_test!(Game::Th08, "map/any.stdm", std08_loop_not_timeof, "th08-loop-not-timeof.std");
std_b2b_test!(Game::Th08, "map/any.stdm", std08_nonzero_padding, "th08-nonzero-padding.std");
std_b2b_test!(Game::Th08, "map/any.stdm", std08_empty_script, "th08-empty-script.std");
std_b2b_test!(Game::Th08, "map/any.stdm", std08_empty_loop, "th08-empty-loop.std");
std_b2b_test!(Game::Th08, "map/any.stdm", std08_2loops_1label, "th08-2loops-1label.std");

// https://github.com/ExpHP/truth/issues/1
//
// This test input is incorrect.  It's supposed to contain a compiled form of `loop { +5: }` but apparently this is
// miscompiling into `+5: loop {}`.
//
// std_b2b_test!(Game::Th08, "map/any.stdm", std08_empty_loop_time, "th08-empty-loop-time.std");

std_b2b_test!(Game::Th06, "map/any.stdm", std06_general, "th06-general.std");
std_b2b_test!(Game::Th12, "map/any.stdm", std12_general, "th12-general.std");
