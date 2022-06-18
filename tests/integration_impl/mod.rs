//! Utilities used by the tests in `tests/integration/`

use std::path::{Path};
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

pub use parse_errors::strip_diagnostic_comments;
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

        assert!(decompile_result.stderr.is_empty(), "unexpected stderr: {}", String::from_utf8_lossy(&decompile_result.stderr));
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
        let outfile = TestFile::new_temp("Xx_compiled-file_xX");
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
            stderr: output.stderr,
        }
    }

    pub fn decompile<'a>(
        &self,
        infile: &TestFile,
        args: &[&OsStr],
        mapfiles: impl IntoIterator<Item=&'a TestFile>,
    ) -> ProgramResult {
        let outfile = TestFile::new_temp("Xx_decompiled-text_xX");
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
            stderr: output.stderr,
        }
    }
}

pub struct ProgramResult {
    /// Only `Some` if the program had an exit code of 0.
    pub output: Option<TestFile>,
    pub stderr: Vec<u8>,
}

fn mapfile_args<'a>(mapfiles: impl IntoIterator<Item=&'a TestFile>) -> Vec<String> {
    mapfiles.into_iter().flat_map(|mapfile| {
        vec!["-m".to_string(), mapfile.as_path().to_string_lossy().into()]
    }).collect()
}

// =============================================================================

fn make_output_deterministic(stderr: &str) -> String {
    lazy_static::lazy_static! {
        // General substitutions to make
        static ref TEMP_FILE_SUBSTS: Vec<(regex::Regex, &'static str)> = {
            vec![
                // Temporary file names and line numbers
                (r#"┌─ .+[/\\]Xx_([^\r\n]+)_xX"#, "┌─ <$1>"),
                (r#"^(warning|error): .+[/\\]Xx_([^\r\n]+)_xX:"#, r#"$1: <$2>:"#),
                (r#"while writing '[^']+': "#, "while writing '<output>':"),
                // OS error strings
                (r#"^(warning|error): ([^:]+): [^:]+ \(os error \d+\)"#, r#"$1: $2: (os error)"#),
            ].into_iter().map(|(pat, subst)| {
                let re = regex::RegexBuilder::new(pat).multi_line(true).build().unwrap();
                (re, subst)
            }).collect()
        };

        // Regexes for eliminating backslashes on windows.
        static ref PATH_SUBSTS: Vec<regex::Regex> = {
            vec![
                // Each of these should be of the form (text_before_path, text_after_path)
                (r#"^(?:warning|error): "#, r#": .+"#),
            ].into_iter().map(|(before_path, after_path)| {
                // construct a pattern with 3 captures (before, path, after), where path does not
                // contain quotes and contains at least one backslash
                let pat = format!(r#"({before_path})([^ :"\\]+\\[^ :"]+)({after_path})$"#);
                regex::RegexBuilder::new(&pat).multi_line(true).build().unwrap()
            }).collect()
        };
    }

    let stderr = TEMP_FILE_SUBSTS.iter().fold(
        stderr.to_string(),
        |stderr, &(ref re, replacement)| re.replace_all(&stderr[..], replacement).into_owned(),
    );

    let stderr = PATH_SUBSTS.iter().fold(
        stderr.to_string(),
        |stderr, re| re.replace_all(&stderr[..], |captures: &regex::Captures| {
            format!("{}{}{}", &captures[1], captures[2].replace("\\", "/"), &captures[3])
        }).into_owned(),
    );

    stderr
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
#[allow(unused)]  // embedded error comments can't use this so some are unused now
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
