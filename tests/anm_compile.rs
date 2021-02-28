//! Tests for non-language-related features of anm-compile (notably image sources)

use std::path::Path;
use std::process::Command;

use truth::{Game, AnmFile};

use assert_cmd::prelude::*;

#[track_caller]
fn file(fname: &str) -> std::path::PathBuf {
    let mut path = std::path::PathBuf::from("tests/anm-compile");
    path.push(fname);
    assert!(path.exists(), "{}", path.display());
    path
}

// a dumb test to make sure that we don't just dump files in the input directory and
// forget to add tests for them.
#[test]
fn all_files_tested() {
    let mut not_mentioned = vec![];
    let this_file_src = std::fs::read_to_string(file!()).unwrap();
    for entry in std::fs::read_dir("tests/anm-compile").unwrap() {
        let path = entry.unwrap().path();
        let path_str = &path.to_string_lossy()[..];
        if path.is_file() && path_str.contains(".anm") {  // NOTE: also matches .anm.spec
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

fn compile(game: Game, infile: impl AsRef<Path>) -> AnmFile {
    let (_, anm) = compile_with_args(game, infile, |_| vec![]);
    anm
}

fn compile_for_thecl_defs(game: Game, infile: impl AsRef<Path>) -> String {
    let (tempdir, _) = compile_with_args(
        game, infile, |tempdir| vec![
            "--output-thecl-defs".into(),
            tempdir.join("defs").to_string_lossy().into_owned(),
        ],
    );
    std::fs::read_to_string(tempdir.path().join("defs")).unwrap()
}

fn compile_with_args(
    game: Game,
    infile: impl AsRef<Path>,
    extra_args: impl FnOnce(&Path) -> Vec<String>,  // gets tmpdir as argument
) -> (tempfile::TempDir, AnmFile) {
    truth::setup_for_test_harness();

    let temp_dir = tempfile::tempdir().unwrap();
    let temp = temp_dir.path();
    let output = {
        Command::cargo_bin("truanm").unwrap()
            .arg("compile")
            .arg(infile.as_ref())
            .arg("-g").arg(game.to_string())
            .arg("-o").arg(temp.join("test.anm"))
            .args(extra_args(temp.as_ref()))
            .output().expect("failed to execute process")
    };
    print!("{}", std::str::from_utf8(&output.stdout).unwrap());
    eprint!("{}", std::str::from_utf8(&output.stderr).unwrap());
    assert!(output.status.success());

    let reader = std::io::Cursor::new(std::fs::read(&temp.join("test.anm")).unwrap());
    let anm = AnmFile::read_from_stream(reader, game, false).unwrap();
    (temp_dir, anm)
}

fn compile_fail_stderr(game: Game, infile: impl AsRef<Path>) -> String {
    truth::setup_for_test_harness();

    let temp = tempfile::tempdir().unwrap();
    let temp = temp.path();
    let output = {
        Command::cargo_bin("truanm").unwrap()
            .arg("compile")
            .arg(infile.as_ref())
            .arg("-g").arg(game.to_string())
            .arg("-o").arg(temp.join("test.anm"))
            .output().expect("failed to execute process")
    };
    print!("{}", std::str::from_utf8(&output.stdout).unwrap());
    eprint!("{}", std::str::from_utf8(&output.stderr).unwrap());
    assert!(!output.status.success());
    String::from_utf8_lossy(&output.stderr).into_owned()
}

macro_rules! compile_fail_test {
    ($game:expr, $test_name:ident, $fname:expr) => {
        #[test]
        fn $test_name() {
            insta::assert_snapshot!(compile_fail_stderr($game, $fname));
        }
    }
}

mod embedded_image {
    use super::*;

    // These tests are based on "th12-embedded-image-source.anm",
    //  whose original source can be seen at "th12-embedded-image-source.anm.spec"

    #[test]
    fn full() {
        let anm = compile(Game::Th12, file("th12-embedded-image-full.anm.spec"));
        assert_eq!(anm.entries[0].specs.offset_x, Some(200));
    }

    #[test]
    fn partial() {
        let anm = compile(Game::Th12, file("th12-embedded-image-partial.anm.spec"));
        assert_eq!(anm.entries[0].sprites[0].offset, [12.0, 0.0]);
        assert_eq!(anm.entries[0].scripts.len(), 2);
        assert_eq!(anm.entries[0].scripts[0].instrs[0].opcode, 2);
    }
}

mod no_source {
    use super::*;

    #[test]
    fn okay() {
        compile(Game::Th12, file("th12-no-source-required.anm.spec"));
    }

    compile_fail_test!(Game::Th12, err_missing_metadata, file("th12-err-missing-metadata.anm.spec"));
    compile_fail_test!(Game::Th12, err_missing_image, file("th12-err-missing-image.anm.spec"));
}

compile_fail_test!(Game::Th12, err_sprite_clash, file("th12-err-sprite-clash.anm.spec"));
compile_fail_test!(Game::Th12, err_sprite_clash_implicit, file("th12-err-sprite-clash-implicit.anm.spec"));

#[test]
fn multiple_match() {
    // Note: Output based on "th12-multiple-match-source.anm"/"th12-multiple-match-source.anm.spec"
    let anm = compile(Game::Th12, file("th12-multiple-match.anm.spec"));
    assert_eq!(anm.entries[0].specs.width, Some(2000));  // pulled from file1
    assert_eq!(anm.entries[0].sprites[0].size, [111.0, 111.0]);
    assert_eq!(anm.entries[0].scripts[0].instrs[0].opcode, 1);
    assert_eq!(anm.entries[1].specs.width, Some(1000));  // pulled from file2
    assert_eq!(anm.entries[1].sprites[0].size, [222.0, 220.0]);
    assert_eq!(anm.entries[1].scripts[0].instrs[0].opcode, 2);
}

#[test]
fn multiple_same() {
    // Note: Output based on "th12-multiple-same-source.anm"/"th12-multiple-same-source.anm.spec"
    let anm = compile(Game::Th12, file("th12-multiple-same.anm.spec"));
    assert_eq!(anm.entries[0].specs.width, Some(1000));
    assert_eq!(anm.entries[0].sprites[0].size, [111.0, 111.0]);
    assert_eq!(anm.entries[0].scripts[0].instrs[0].opcode, 1);
    assert_eq!(anm.entries[1].specs.width, Some(2000));
    assert_eq!(anm.entries[1].sprites[0].size, [222.0, 220.0]);
    assert_eq!(anm.entries[1].scripts[0].instrs[0].opcode, 2);
}

#[test]
fn thecl_defs() {
    let defs = compile_for_thecl_defs(Game::Th12, file("th12-thecl-defs-input.anm.spec"));
    let expected = std::fs::read_to_string(file("th12-thecl-defs-expected.ecs")).unwrap();
    assert_eq!(defs, expected);
}


#[test]
fn sprite_ids_gone_wild() {
    let anm = compile(Game::Th12, file("th12-sprite-ids-gone-wild.anm.spec"));
    assert_eq!(anm.entries[0].sprites[0].id, Some(2));
    assert_eq!(anm.entries[0].sprites[1].id, None);  // 3
    assert_eq!(anm.entries[0].sprites[2].id, Some(53));
    assert_eq!(anm.entries[0].sprites[3].id, Some(400));
    assert_eq!(anm.entries[1].sprites[0].id, None);  // 401
    assert_eq!(anm.entries[1].sprites[1].id, Some(404));
}
