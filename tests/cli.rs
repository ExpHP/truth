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
        .stderr(pred(|s: &str| s.contains("truanm compile")))
        .stderr(pred(|s: &str| s.contains("truanm decompile")))
    ;
}

#[test]
fn show_subcommands_help() {
    Command::cargo_bin("truanm").unwrap()
        .arg("--help")
        .assert()
        .success()  // should succeed as long as --help is given
        .stderr(pred(|s: &str| s.contains("truanm compile")))
        .stderr(pred(|s: &str| s.contains("truanm decompile")))
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

#[test]
fn anm_extract_no_files() {
    Command::cargo_bin("truanm").unwrap()
        .arg("extract")
        .arg("-g")
        .arg("8")
        .assert()
        .failure()
        .stderr(pred(|s: &str| s.contains("Usage: ")))
        .stderr(pred(|s: &str| s.contains("missing required")))
    ;
}
