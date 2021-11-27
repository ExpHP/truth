//! Utilities used by the tests in `tests/integration/`

use std::path::{Path, PathBuf};
use std::process::Command;
use std::ffi::OsStr;

use truth::Game;

use assert_cmd::prelude::*;

macro_rules! snapshot_path {
    () => { concat!(env!("CARGO_MANIFEST_DIR"), "/tests/compile-fail") }
}

pub mod formats;

pub use test_file::TestFile;
mod test_file;

mod parse_errors;

// =============================================================================

pub struct Format {
    pub cmd: &'static str,
    pub game: Game,
    pub script_head: &'static str,
    /// Embed a series of statements inside some sort of subroutine definition;
    /// whatever is appropriate for the language in question.
    pub make_main: fn(&str) -> String,
}

impl Format {
    /// Implementation of the tests in [`crate::integration::bits_2_bits`].
    #[doc(hidden)]
    pub fn bits_to_bits(
        &self,
        infile: impl AsRef<Path>,
        mapfile: impl AsRef<Path>,
        do_with_text: impl FnOnce(&str),
    ) {
        truth::setup_for_test_harness();

        let original = TestFile::from_path(infile.as_ref());
        let mapfile = TestFile::from_path(mapfile.as_ref());
        let decompile_result = self.decompile(&original, &[], &[mapfile][..]);

        assert!(decompile_result.stderr.is_none(), "unexpected stderr: {}", decompile_result.stderr.unwrap());
        let decompiled = decompile_result.output.unwrap();

        do_with_text(&decompiled.read_to_string());

        let mut args = vec![];
        if self.cmd == "truanm" {
            args.push("--image-source".as_ref());
            args.push(infile.as_ref().as_ref());
        }

        let recompile_mapfiles = &[][..]; // decompiled source already includes mapfile
        let recompile_result = self.compile(&decompiled, &args, recompile_mapfiles);
        let recompiled = recompile_result.output.unwrap();
        assert_eq!(original.read(), recompiled.read());
    }

    pub fn compile<'a>(
        &self,
        src: &TestFile,
        args: &[&OsStr],
        mapfiles: impl IntoIterator<Item=&'a TestFile>,
    ) -> ProgramResult {
        let outfile = TestFile::new_temp("Xx_COMPILATION OUTPUT_xX");
        let output = {
            Command::cargo_bin(self.cmd).unwrap()
                .arg("compile")
                .arg("-g").arg(format!("{}", self.game))
                .arg(src.as_path())
                .arg("-o").arg(outfile.as_path())
                .args(mapfile_args(mapfiles))
                .args(args)
                .output().expect("failed to execute process")
        };
        if !output.stdout.is_empty() {
            eprintln!("== COMPILE STDOUT:");
            eprintln!("{}", String::from_utf8_lossy(&output.stdout));
        }
        if !output.stderr.is_empty() {
            eprintln!("== COMPILE STDERR:");
            eprintln!("{}", String::from_utf8_lossy(&output.stderr));
        }

        ProgramResult {
            output: output.status.success().then(|| outfile),
            stderr: (!output.stderr.is_empty()).then(|| String::from_utf8(output.stderr).unwrap()),
        }
    }

    pub fn decompile<'a>(
        &self,
        infile: &TestFile,
        args: &[&OsStr],
        mapfiles: impl IntoIterator<Item=&'a TestFile>,
    ) -> ProgramResult {
        let outfile = TestFile::new_temp("Xx_DECOMPILATION OUTPUT_xX");
        let output = {
            Command::cargo_bin(self.cmd).unwrap()
                .arg("decompile")
                .arg("-g").arg(format!("{}", self.game))
                .arg(infile.as_path())
                .stdout(outfile.create())
                .args(mapfile_args(mapfiles))
                .args(args)
                .output().expect("failed to execute process")
        };
        if !output.stderr.is_empty() {
            eprintln!("== DECOMPILE STDERR:");
            eprintln!("{}", String::from_utf8_lossy(&output.stderr));
        }

        ProgramResult {
            output: output.status.success().then(move || outfile),
            stderr: (!output.stderr.is_empty()).then(move || String::from_utf8(output.stderr).unwrap()),
        }
    }
}

pub struct ProgramResult {
    /// Only `Some` if the program had an exit code of 0.
    pub output: Option<TestFile>,
    /// Only `Some` if non-empty.
    pub stderr: Option<String>,
}

fn mapfile_args<'a>(mapfiles: impl IntoIterator<Item=&'a TestFile>) -> Vec<String> {
    mapfiles.into_iter().flat_map(|mapfile| {
        vec!["-m".to_string(), mapfile.as_path().to_string_lossy().into()]
    }).collect()
}

// =============================================================================

lazy_static::lazy_static! {
    static ref TEMP_FILE_SUBSTS: Vec<(regex::Regex, &'static str)> = {
        vec![
            (r#"┌─ .+[/\\]original\.spec"#, "┌─ <input>"),
            (r#"┌─ .+[/\\]Xx_MAPFILE INPUT (\d+)_xX"#, "┌─ <mapfile-$1>"),
            (r#"while writing '[^']+': "#, "while writing '<output>':"),
            (r#"^(warning|error): .+[/\\]Xx_COMPILATION OUTPUT_xX:"#, r#"$1: <decompile-input>:"#),
        ].into_iter().map(|(pat, subst)| {
            (regex::Regex::new(pat).unwrap(), subst)
        }).collect()
    };
}

fn make_output_deterministic(stderr: &str) -> String {
    TEMP_FILE_SUBSTS.iter().fold(
        stderr.to_string(),
        |stderr, &(ref re, replacement)| re.replace_all(&stderr[..], replacement).into_owned(),
    )
}

fn erase_panic_line_number_for_accepted_panics(message: &str) -> String {
    lazy_static::lazy_static! {
        static ref PANIC_LINE_NUMBER_RE: regex::Regex = regex::Regex::new(r#"panicked at 'not implemented', ([^:]+):[0-9]+:[0-9]+"#).unwrap();
    }
    PANIC_LINE_NUMBER_RE.replace(message, "panicked at 'not implemented', ${1}:???:??").into_owned()
}

// Implementation of the check_compile_fail_output macro.
#[track_caller]
pub fn _check_compile_fail_output(
    stderr: &str,
    expected: &str,
    // we can't put the snapshot test code in this function because then we wouldn't be able to
    // automatically get the test name and path into the snapshot name.
    //
    // So it's taken via closure, and the macro automates the writing of this closure.
    perform_snapshot_test: impl FnOnce(&str),
) {
    let stderr = make_output_deterministic(&stderr);

    // we don't want internal compiler errors.
    let is_ice = false
        || stderr.contains("panicked at") || stderr.contains("RUST_BACKTRACE=1")
        || stderr.contains("bug!") || stderr.contains("BUG!")
        ;
    let allow_ice = expected == expected::UNIMPLEMENTED && stderr.contains(expected);

    // hitting `unimplemented!` macro is okay if that's the expected error
    let is_bad_ice = is_ice && !allow_ice;
    let is_good_ice = is_ice && allow_ice;
    assert!(!is_bad_ice, "INTERNAL COMPILER ERROR:\n{}", stderr);
    if is_good_ice {
        return; // don't do snapshot test; this test might be changed to succeed later
    }

    let stderr = erase_panic_line_number_for_accepted_panics(&stderr);
    assert!(stderr.contains(expected), "Error did not contain expected! error: {}", stderr);
    perform_snapshot_test(&stderr);
}

/// Performs a snapshot test of stderr while also verifying that it contains a certain substring.
///
/// Certain unreliable parts of the stderr will be made deterministic before performing the snapshot check.
macro_rules! check_compile_fail_output {
    ($stderr:expr, $expected:expr) => {{
        crate::integration_impl::_check_compile_fail_output($stderr, $expected, |normalized_stderr| {
            assert_snapshot!{normalized_stderr};
        });
    }};
}

/// Perform a snapshot test of something.
macro_rules! assert_snapshot {
    ($stderr:expr) => {{
        insta::with_settings!{{snapshot_path => snapshot_path!()}, {
            insta::assert_snapshot!{$stderr};
        }}
    }};
}

// =============================================================================

/// stderr search strings for ubiquitous error messages
pub mod expected {
    pub const TYPE_ERROR: &'static str = "type error";
    pub const PARSE_ERROR: &'static str = "unexpected token";
    pub const UNIMPLEMENTED: &'static str = "not implemented";
    pub const NOT_SUPPORTED_BY_FORMAT: &'static str = "not supported";
    pub const DECOMP_UNKNOWN_SIG: &'static str = "were decompiled to byte blobs";
}

#[macro_use]
pub mod source_test;

// =============================================================================

/// Convert a series of values into a blob, typically for comparison against a raw instruction.
macro_rules! blobify {
    ($($args:expr),* $(,)?) => {{
        #[allow(unused_mut)]
        let mut blob = vec![];
        $( crate::integration_impl::Blobify::append_to(&$args, &mut blob); )*
        blob
    }};
}

pub trait Blobify {
    fn append_to(&self, blob: &mut Vec<u8>);
}

impl Blobify for i32 {
    fn append_to(&self, blob: &mut Vec<u8>) {
        blob.extend_from_slice(&self.to_le_bytes())
    }
}

impl Blobify for f32 {
    fn append_to(&self, blob: &mut Vec<u8>) {
        blob.extend_from_slice(&self.to_bits().to_le_bytes())
    }
}
