//! Regression test to make sure that --help always works.

use std::process::Command;

use assert_cmd::prelude::*;
use predicates::function::function as pred;

#[test]
fn help_actually_helps() {
    Command::cargo_bin("truanm").unwrap()
        .arg("compile")
        .arg("--help")
        .assert()
        .success()
        // check that the help text was shown by looking for part of the --game argument help
        .stderr(pred(|s: &str| s.contains("game number, e.g.")))
    ;
}

#[test]
fn show_subcommands_error() {
    Command::cargo_bin("truanm").unwrap()
        .assert()
        .failure()
        // it should do a listing of subcommands.
        .stderr(pred(|s: &str| s.contains("truanm compile [--help] ARGS...")))
        .stderr(pred(|s: &str| s.contains("truanm decompile [--help] ARGS...")))
    ;
}

#[test]
fn show_subcommands_help() {
    Command::cargo_bin("truanm").unwrap()
        .arg("--help")
        .assert()
        .success()  // --help has the same output, but with exit code 0
        .stderr(pred(|s: &str| s.contains("truanm compile [--help] ARGS...")))
        .stderr(pred(|s: &str| s.contains("truanm decompile [--help] ARGS...")))
    ;
}

#[test]
fn fake_subcommand_help() {
    Command::cargo_bin("truanm").unwrap()
        .arg("help")
        .assert()
        // don't really care if this succeeds or fails, but it's something
        // somebody might--and has--tried.  We just want to know it mentions --help.
        .stderr(pred(|s: &str| s.contains("truanm compile [--help] ARGS...")))
        .stderr(pred(|s: &str| s.contains("truanm decompile [--help] ARGS...")))
    ;
}

#[test]
fn subcommand_version() {
    Command::cargo_bin("truanm").unwrap()
        .arg("compile")
        .arg("--version")
        .assert()
        .success()
    ;
}

#[test]
fn main_version() {
    Command::cargo_bin("truanm").unwrap()
        .arg("--version")
        .assert()
        .success()
    ;
}

#[test]
fn core_version() {
    Command::cargo_bin("truth-core").unwrap()
        .arg("--version")
        .assert()
        .success()
    ;
}
