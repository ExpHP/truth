//! Utilities used by the tests in `tests/integration/`

use std::path::{Path, PathBuf};
use std::process::Command;
use std::ffi::OsStr;

use truth::{Game, AnmFile};

use assert_cmd::prelude::*;

pub mod formats;

pub struct Format {
    pub cmd: &'static str,
    pub game: Game,
    pub script_head: &'static str,
    /// Embed a series of statements inside some sort of subroutine definition;
    /// whatever is appropriate for the language in question.
    pub make_main: fn(&str) -> String,
}

pub struct ScriptParts<'a> {
    pub items: &'a str,
    pub main_body: &'a str,
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
        let decompiled = self.decompile_with_args(&original, &["-m".as_ref(), mapfile.as_ref().as_ref()]);

        do_with_text(&decompiled.read_to_string());

        let recompiled = self.compile(&decompiled);
        assert_eq!(original.read(), recompiled.read());
    }

    /// Source-to-binary-to-source-to-binary (sbsb) tests.
    ///
    /// This is similar to [`Self::bits_to_bits`], but with an additional step at the beginning that lets
    /// the inputs be readable text files instead of binary files.
    ///
    /// 1. The input script consists of SIMPLE instructions. (as close as we can
    ///    get to a textual representation of a compiled file)
    /// 2. It is compiled.
    /// 3. That gets decompiled. **This is the step that we're really testing!!**
    /// 4. The decompiled text can be checked to see if it contains something desired.
    /// 5. It then gets compiled again and checked against the first compile.
    ///
    /// The comparison of the two compiled files helps check to make sure that the decompilation
    /// step did not accidentally change the meaning of the code.
    pub fn sbsb_test(&self, original_source: &TestFile, with_decompiled: impl FnOnce(&str)) {
        truth::setup_for_test_harness();

        let compiled = self.compile(&original_source);
        let decompiled = self.decompile(&compiled);
        let decompiled_str = decompiled.read_to_string();

        eprintln!("== DECOMPILED:");
        eprintln!("{}", &decompiled_str);
        with_decompiled(&decompiled_str);

        let recompiled = self.compile(&decompiled);

        assert_eq!(compiled.read(), recompiled.read());
    }

    pub fn make_source(&self, descr: &str, script_parts: ScriptParts<'_>) -> TestFile {
        TestFile::from_content(descr, format!(
            "{}\n{}\n{}",
            self.script_head,
            script_parts.items,
            (self.make_main)(script_parts.main_body),
        ))
    }
}

/// A file possibly backed by a temp directory (which, if so, will be deleted on drop).
///
/// The file need not necessarily even exist yet; e.g. you can use [`Self::new_temp`] to create a
/// temp dir, then use [`Self::as_path`] as an output file argument to a CLI command.
pub struct TestFile {
    descr: String,
    _tempdir: Option<tempfile::TempDir>,
    filepath: PathBuf,
}

impl Format {
    pub fn compile(&self, src: &TestFile) -> TestFile {
        self.compile_with_args(src, &[])
    }

    pub fn compile_and_capture(&self, src: &TestFile) -> (TestFile, std::process::Output) {
        self._compile_with_args(src, &[])
    }

    pub fn compile_with_args(&self, src: &TestFile, args: &[&OsStr]) -> TestFile {
        self._compile_with_args(src, args).0
    }

    fn _compile_with_args(&self, src: &TestFile, args: &[&OsStr]) -> (TestFile, std::process::Output) {
        let outfile = TestFile::new_temp("compilation output");
        let output = {
            Command::cargo_bin(self.cmd).unwrap()
                .arg("compile")
                .arg("-g").arg(format!("{}", self.game))
                .arg(src.as_path())
                .arg("-o").arg(outfile.as_path())
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
        assert!(output.status.success());
        (outfile, output)
    }

    pub fn decompile(&self, src: &TestFile) -> TestFile {
        self.decompile_with_args(src, &[])
    }

    pub fn decompile_with_args(&self, src: &TestFile, args: &[&OsStr]) -> TestFile {
        let outfile = TestFile::new_temp("decompilation output");
        let output = {
            Command::cargo_bin(self.cmd).unwrap()
                .arg("decompile")
                .arg("-g").arg(format!("{}", self.game))
                .arg(src.as_path())
                .stdout(outfile.create())
                .args(args)
                .output().expect("failed to execute process")
        };
        if !output.stderr.is_empty() {
            eprintln!("== DECOMPILE STDERR:");
            eprintln!("{}", String::from_utf8_lossy(&output.stderr));
        }
        assert!(output.status.success());
        outfile
    }
}

impl TestFile {
    /// Construct a [`TestFile`] referring to a (not yet created) filepath inside a newly created
    /// tempdir.  The tempdir will be deleted on drop.
    pub fn new_temp(filename: &str) -> Self {
        let descr = filename.to_string();
        let tempdir = tempfile::tempdir().unwrap_or_else(|e| panic!("while making tempdir for {}: {}", descr, e));
        let filepath = tempdir.path().join(filename);
        TestFile { descr, _tempdir: Some(tempdir), filepath }
    }

    /// Construct a [`TestFile`] from file contents, which will be written to a new file inside
    /// of a new temporary directory.  The tempdir will be deleted on drop.
    pub fn from_content(filename: &str, bytes: impl AsRef<[u8]>) -> Self {
        let out = TestFile::new_temp(filename);
        std::fs::write(out.as_path(), bytes)
            .unwrap_or_else(|e| panic!("while writing to {}: {}", filename, e));
        out
    }

    /// Construct from an existing file without creating a tempdir.
    pub fn from_path(filepath: impl AsRef<Path>) -> Self {
        let filepath = filepath.as_ref().to_owned();
        let descr = filepath.display().to_string();
        TestFile { descr, filepath, _tempdir: None }
    }

    pub fn as_path(&self) -> &Path {
        &self.filepath
    }

    pub fn create(&self) -> std::fs::File {
        std::fs::File::create(&self.filepath)
            .unwrap_or_else(|e| panic!("while creating file for {}: {}", self.descr, e))
    }

    pub fn read(&self) -> Vec<u8> {
        std::fs::read(&self.filepath)
            .unwrap_or_else(|e| panic!("while reading bytes from {}: {}", self.descr, e))
    }

    pub fn read_to_string(&self) -> String {
        std::fs::read_to_string(&self.filepath)
            .unwrap_or_else(|e| panic!("while reading text from {}: {}", self.descr, e))
    }

    pub fn read_anm(&self, format: &Format) -> AnmFile {
        let mut scope = truth::Builder::new().build();
        let mut truth = scope.truth();
        truth.read_anm(format.game, self.as_path(), false).unwrap()
    }
}

// =============================================================================

lazy_static::lazy_static! {
    static ref TEMP_FILE_SUBSTS: Vec<(regex::Regex, &'static str)> = {
        vec![
            (r#"┌─ .+[/\\]original\.spec"#, "┌─ <input>"),
            (r#"while writing '[^']+': "#, "while writing '<output>':"),
        ].into_iter().map(|(pat, subst)| {
            (regex::Regex::new(pat).unwrap(), subst)
        }).collect()
    };
}

impl Format {
    pub fn compile_fail_stderr(&self, source: &TestFile) -> String {
        let output = {
            Command::cargo_bin(self.cmd).unwrap()
                .arg("compile")
                .arg("-g").arg(format!("{}", self.game))
                .arg(source.as_path())
                .arg("-o").arg("/dev/null")
                .output().expect("failed to execute process")
        };
        assert!(!output.status.success());

        String::from_utf8(output.stderr).unwrap()
    }
}

fn make_output_deterministic(stderr: &str) -> String {
    TEMP_FILE_SUBSTS.iter().fold(
        stderr.to_string(),
        |stderr, &(ref re, replacement)| re.replace_all(&stderr[..], replacement).into_owned(),
    )
}

macro_rules! snapshot_path {
    () => { concat!(env!("CARGO_MANIFEST_DIR"), "/tests/compile-fail") }
}

// used to implement defaults for some optional macro parts by writing `first_token!( $($thing)?  "" )`
macro_rules! first_token {
    ($tok:tt $($rest:tt)*) => { $tok };
}

/// Generates a test that does *something* to a source script.
///
/// The purpose of this is to reduce the friction to writing tests as much as possible.
/// It reduces noise by allowing things not relevant to a given test to be left out.  It also
/// reduces the amount of busywork in converting a test back and forth between a compile-succeed
/// test and a compile-fail test. (you just replace a `check:` closure with an `expect_fail:` string)
macro_rules! source_test {
    (
        $format:expr, $test_name:ident

        // -------------------------
        // args to make_source!
        $(, items: $items:expr)?
        $(, main_body: $main_body:expr)?
        $(, full_source: $full_source:expr)?

        // -------------------------
        // Test details
        //
        // You must supply one of the following things:

        // Compile the code and run the given closure on the compiled TestFile.
        $(, check_compiled:$check_fn:expr)?

        // Does an "SBSB" test to test decompilation of a file compiled from simple source.
        //
        // IMPORTANT: Please see the documentation of Format::sbsb_test for more information.
        $(, sbsb: $sbsb_check_fn:expr)?

        // Do a compile-fail snapshot test.
        //
        // Requires a string to search for in the STDERR output.
        // (This helps ensure that compilation is failing for a legitimate reason.)
        //
        // It's okay if a change to the compiler breaks a test by causing it to produce a different error!
        // (e.g. because the order of passes changed, or something formerly unparseable is now parseable).
        // Whenever this occurs, just review the new outputs and make sure that the new errors are still
        // related to what they were originally testing.
        // This is intended to be a slightly larger speed-bump than other cases of insta-snapshot test breakage.
        $(, expect_fail: $expect_fail_msg:expr)?

        // Compile the code and expect success, but snapshot stderr and check for a substring.
        $(, expect_warning: $expect_warning_msg:expr)?

        $(,)?
    ) => {
        #[test]
        fn $test_name() {
            // make it error if there's no `check:` or `expect_fail:`
            #![deny(unused)]

            truth::setup_for_test_harness();

            let source = make_source!(
                $format
                $(, items: $items)?
                $(, main_body: $main_body)?
                $(, full_source: $full_source)?
            );

            $(
                let outfile = $format.compile(&source);
                // annotate closure so that method lookup works
                let check_fn: fn(&crate::integration_impl::TestFile, &crate::integration_impl::Format) = $check_fn;
                check_fn(&outfile, &$format);
                return;
            )?

            $(
                let (_, output) = $format.compile_and_capture(&source);
                // annotate closure so that method lookup works
                _check_compile_fail_output!(String::from_utf8_lossy(&output.stderr), expected: $expect_warning_msg);
                return;
            )?

            $(
                $format.sbsb_test(&source, $sbsb_check_fn);
                return;
            )?

            $(
                let stderr = $format.compile_fail_stderr(&source);
                _check_compile_fail_output!(stderr, expected: $expect_fail_msg);
                return;
            )?
        }
    };
}

macro_rules! make_source {
    (
        $format:expr

        // (optional) other items you want in the script
        $(, items: $items:expr)?

        // the statements to compile into a function body
        $(, main_body: $main_body:expr)?

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
        $format.make_source("original.spec", crate::integration_impl::ScriptParts {
            items: first_token!( $($items)? "" ),
            main_body: first_token!( $($main_body)? "" ),
        })
    };

    (
        // Alternative that takes full source.  It is recommended to only use this when necessary
        // (namely when testing things in meta), as there's a greater likelihood that the tests
        // will be broken by innocent changes.
        $format:expr

        , full_source: $main_body:expr

        $(, expected: $expected:expr)?
        $(,)?
    ) => {
        crate::integration_impl::TestFile::from_content("original.spec", $main_body)
    };
}

#[track_caller]
pub fn _check_compile_fail_output(stderr: &str, expected: &str, snapshot: impl FnOnce(&str)) {
    let stderr = make_output_deterministic(&stderr);

    // we don't want internal compiler errors.
    let is_ice = false
        || stderr.contains("panicked at") || stderr.contains("RUST_BACKTRACE=1")
        || stderr.contains("bug!") || stderr.contains("BUG!")
        ;
    let allow_ice = expected == expected::UNIMPLEMENTED && stderr.contains(expected);

    // hitting `unimplemented!` macro is okay if that's the expected error
    let is_bad_ice = is_ice && !allow_ice;
    assert!(!is_bad_ice, "INTERNAL COMPILER ERROR:\n{}", stderr);

    assert!(stderr.contains(expected), "Error did not contain expected! error: {}", stderr);
    snapshot(&stderr);
}

macro_rules! _check_compile_fail_output {
    ($stderr:expr, expected: $expected:expr) => {{
        crate::integration_impl::_check_compile_fail_output(&$stderr, $expected, |stderr| {
            insta::with_settings!{{snapshot_path => snapshot_path!()}, {
                insta::assert_snapshot!{stderr};
            }}
        });
    }}
}

/// stderr search strings for ubiquitous error messages
pub mod expected {
    pub const TYPE_ERROR: &'static str = "type error";
    pub const PARSE_ERROR: &'static str = "unexpected token";
    pub const UNIMPLEMENTED: &'static str = "not implemented";
    pub const NOT_SUPPORTED_BY_FORMAT: &'static str = "not supported";
}
