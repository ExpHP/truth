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
    pub fn sbsb_test(&self, script_text: &str, with_decompiled: impl FnOnce(&str)) {
        truth::setup_for_test_harness();

        let full_source = format!("{}\n{}", self.script_head, (self.make_main)(script_text));

        let original_source = TestFile::from_content("original source", full_source);
        let compiled = self.compile(&original_source);
        let decompiled = self.decompile(&compiled);
        let decompiled_str = decompiled.read_to_string();

        eprintln!("== DECOMPILED:");
        eprintln!("{}", &decompiled_str);
        with_decompiled(&decompiled_str);

        let recompiled = self.compile(&decompiled);

        assert_eq!(compiled.read(), recompiled.read());
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

    pub fn compile_with_args(&self, src: &TestFile, args: &[&OsStr]) -> TestFile {
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
        outfile
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
    pub fn new_temp(descr: &str) -> Self {
        let descr = descr.to_string();
        let tempdir = tempfile::tempdir().unwrap_or_else(|e| panic!("while making tempdir for {}: {}", descr, e));
        let filepath = tempdir.path().join("file");
        TestFile { descr, _tempdir: Some(tempdir), filepath }
    }

    /// Construct a [`TestFile`] from file contents, which will be written to a new file inside
    /// of a new temporary directory.  The tempdir will be deleted on drop.
    pub fn from_content(descr: &str, bytes: impl AsRef<[u8]>) -> Self {
        let out = TestFile::new_temp(descr);
        std::fs::write(out.as_path(), bytes)
            .unwrap_or_else(|e| panic!("while writing to {}: {}", descr, e));
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
        let reader = std::io::Cursor::new(self.read());
        AnmFile::read_from_stream(reader, format.game, false).unwrap()
    }
}

// =============================================================================

lazy_static::lazy_static! {
    static ref TEMP_FILE_REGEX: regex::Regex = regex::Regex::new(r#"┌─ .+[/\\]original\.spec"#).unwrap();
}
const TEMP_FILE_REPLACEMENT: &'static str = "┌─ <input>";

impl Format {
    pub fn compile_fail_stderr(&self, other_items: &str, main_body: &str) -> String {
        truth::setup_for_test_harness();

        self.compile_fail_stderr_no_transform(format!(
            "{}\n{}\n{}",
            self.script_head,
            other_items,
            (self.make_main)(main_body),
        ))
    }

    pub fn compile_fail_stderr_no_transform<S: AsRef<[u8]>>(&self, full_source: S) -> String {
        use std::fs::{write};

        truth::setup_for_test_harness();

        let temp = tempfile::tempdir().unwrap();
        let temp = temp.path();

        write(temp.join("original.spec"), full_source).unwrap();
        self._compile_fail_stderr(temp.join("original.spec"))
    }

    fn _compile_fail_stderr(&self, src: impl AsRef<OsStr>) -> String {
        let output = {
            Command::cargo_bin(self.cmd).unwrap()
                .arg("compile")
                .arg("-g").arg(format!("{}", self.game))
                .arg(src)
                .arg("-o").arg("/dev/null")
                .output().expect("failed to execute process")
        };
        assert!(!output.status.success());

        self.make_output_deterministic(std::str::from_utf8(&output.stderr).unwrap())
    }

    fn make_output_deterministic(&self, stderr: &str) -> String {
        TEMP_FILE_REGEX.replace_all(stderr, TEMP_FILE_REPLACEMENT).into_owned()
    }
}

macro_rules! snapshot_path {
    () => { concat!(env!("CARGO_MANIFEST_DIR"), "/tests/compile-fail") }
}

// used to implement defaults for some optional macro parts by writing `first_token!( $($thing)?  "" )`
macro_rules! first_token {
    ($tok:tt $($rest:tt)*) => { $tok };
}

macro_rules! compile_fail_test {
    (
        $format:expr, $test_name:ident

        // (optional) other items you want in the script
        $(, items_before: $items_before:expr)?

        // the statements to compile into a function body
        , main_body: $main_body:expr

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
        #[test]
        fn $test_name() {
            let stderr = $format.compile_fail_stderr(
                first_token!( $($items_before)? "" ),
                $main_body,
            );
            _check_compile_fail_output!(stderr $(, expected: $expected)?);
        }
    };

    (
        // Alternative that takes full source.  It is recommended to only use this when necessary
        // (namely when testing things in meta), as there's a greater likelihood that the tests
        // will be broken by innocent changes.
        $format:expr, $test_name:ident

        , full_source: $main_body:expr

        $(, expected: $expected:expr)?
        $(,)?
    ) => {
        #[test]
        fn $test_name() {
            let stderr = $format.compile_fail_stderr_no_transform($main_body);
            _check_compile_fail_output!(stderr $(, expected: $expected)?);
        }
    };
}

macro_rules! _check_compile_fail_output {
    ($stderr:expr $(, expected: $expected:expr)?) => {{
        #![allow(unused_mut)]

        let stderr = $stderr;

        // we don't want internal compiler errors.
        let is_ice = (
            stderr.contains("panicked at") || stderr.contains("RUST_BACKTRACE=1")
            || stderr.contains("bug!") || stderr.contains("BUG!")
        );
        // hitting `unimplemented!` macro is okay if that's the expected error
        let is_accepted_ice = false $(
            || ($expected == crate::integration_impl::expected::UNIMPLEMENTED && stderr.contains($expected))
        )?;
        let is_bad_ice = is_ice && !is_accepted_ice;
        assert!(!is_bad_ice, "INTERNAL COMPILER ERROR:\n{}", stderr);

        $( assert!(stderr.contains($expected), "Error did not contain expected! error: {}", stderr); )?
        insta::with_settings!{{snapshot_path => snapshot_path!()}, {
            insta::assert_snapshot!{stderr};
        }}
    }}
}

/// stderr search strings for ubiquitous error messages
pub mod expected {
    pub const TYPE_ERROR: &'static str = "type error";
    pub const PARSE_ERROR: &'static str = "unexpected token";
    pub const UNIMPLEMENTED: &'static str = "not implemented";
    pub const NOT_SUPPORTED_BY_FORMAT: &'static str = "not supported";
}
