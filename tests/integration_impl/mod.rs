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
        let mapfile = TestFile::from_path(mapfile.as_ref());
        let decompiled = self.decompile_with_args(&original, &[], Some(&mapfile));

        do_with_text(&decompiled.read_to_string());

        let mut args = vec![];
        if self.cmd == "truanm" {
            args.push("--image-source".as_ref());
            args.push(infile.as_ref().as_ref());
        }

        let recompile_mapfile = None; // decompiled source already includes mapfile
        let recompiled = self.compile_with_args(&decompiled, &args, recompile_mapfile);
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
    pub fn sbsb_test(&self, original_source: &TestFile, decompile_args: &[impl AsRef<OsStr>], mapfile: Option<&TestFile>, with_decompiled: impl FnOnce(&str)) {
        truth::setup_for_test_harness();

        let decompile_args = decompile_args.iter().map(AsRef::as_ref).collect::<Vec<_>>();

        let compiled = self.compile(&original_source, mapfile);
        let decompiled = self.decompile_with_args(&compiled, &decompile_args, mapfile);
        let decompiled_str = decompiled.read_to_string();

        eprintln!("== DECOMPILED:");
        eprintln!("{}", &decompiled_str);
        with_decompiled(&decompiled_str);

        let recompile_mapfile = None; // decompiled file already links mapfile
        let recompiled = self.compile(&decompiled, recompile_mapfile);

        assert_eq!(compiled.read(), recompiled.read());
    }

    /// In essence, a "decompile-fail" test.
    ///
    /// This is like `sbsb` but rather than compiling to binary one last time,
    /// it instead expects to find a message in stderr from decompilation.
    ///
    /// stderr will be snapshotted.
    pub fn sbsb_fail_test(
        &self,
        original_source: &TestFile,
        decompile_args: &[impl AsRef<OsStr>],
        mapfile: Option<&TestFile>,
        should_error: bool,
        check_compile_fail_output: impl FnOnce(&str),
    ) {
        truth::setup_for_test_harness();

        let decompile_args = decompile_args.iter().map(AsRef::as_ref).collect::<Vec<_>>();

        let compiled = self.compile(&original_source, mapfile);
        let (_decompiled, decompiled_output) = self._decompile_with_args(&compiled, &decompile_args, mapfile);

        check_compile_fail_output(&String::from_utf8(decompiled_output.stderr).unwrap());
        assert_eq!(decompiled_output.status.success(), !should_error);
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
    pub fn compile(&self, src: &TestFile, mapfile: Option<&TestFile>) -> TestFile {
        self.compile_with_args(src, &[], mapfile)
    }

    pub fn compile_and_capture(&self, src: &TestFile, args: &[impl AsRef<OsStr>], mapfile: Option<&TestFile>) -> (TestFile, std::process::Output) {
        let args = args.into_iter().map(|arg| arg.as_ref()).collect::<Vec<_>>();
        self._compile_with_args(src, &args, mapfile)
    }

    pub fn compile_with_args(&self, src: &TestFile, args: &[&OsStr], mapfile: Option<&TestFile>) -> TestFile {
        self._compile_with_args(src, args, mapfile).0
    }

    fn _compile_with_args(&self, src: &TestFile, args: &[&OsStr], mapfile: Option<&TestFile>) -> (TestFile, std::process::Output) {
        let outfile = TestFile::new_temp("Xx_COMPILATION OUTPUT_xX");
        let output = {
            Command::cargo_bin(self.cmd).unwrap()
                .arg("compile")
                .arg("-g").arg(format!("{}", self.game))
                .arg(src.as_path())
                .arg("-o").arg(outfile.as_path())
                .args(optional_mapfile_args(mapfile))
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

    fn _decompile_with_args(&self, src: &TestFile, args: &[&OsStr], mapfile: Option<&TestFile>) -> (TestFile, std::process::Output) {
        let outfile = TestFile::new_temp("Xx_DECOMPILATION OUTPUT_xX");
        let output = {
            Command::cargo_bin(self.cmd).unwrap()
                .arg("decompile")
                .arg("-g").arg(format!("{}", self.game))
                .arg(src.as_path())
                .stdout(outfile.create())
                .args(optional_mapfile_args(mapfile))
                .args(args)
                .output().expect("failed to execute process")
        };
        (outfile, output)
    }

    pub fn decompile_with_args(&self, src: &TestFile, args: &[&OsStr], mapfile: Option<&TestFile>) -> TestFile {
        let (outfile, output) = self._decompile_with_args(src, args, mapfile);
        if !output.stderr.is_empty() {
            eprintln!("== DECOMPILE STDERR:");
            eprintln!("{}", String::from_utf8_lossy(&output.stderr));
        }
        assert!(output.status.success());
        outfile
    }
}

fn optional_mapfile_args(mapfile: Option<&TestFile>) -> Vec<String> {
    match mapfile {
        Some(mapfile) => vec!["-m".to_string(), mapfile.filepath.to_string_lossy().into()],
        None => vec![],
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

    pub fn read_anm(&self, format: &Format) -> truth::AnmFile {
        let mut scope = truth::Builder::new().build();
        let mut truth = scope.truth();
        truth.read_anm(format.game, self.as_path(), true).unwrap()
    }

    pub fn read_msg(&self, format: &Format) -> truth::MsgFile {
        let mut scope = truth::Builder::new().build();
        let mut truth = scope.truth();
        truth.read_msg(format.game, truth::InstrLanguage::Msg, self.as_path()).unwrap()
    }

    pub fn read_ecl(&self, format: &Format) -> truth::EclFile {
        let mut scope = truth::Builder::new().build();
        let mut truth = scope.truth();
        truth.read_ecl(format.game, self.as_path()).unwrap()
    }
}

// =============================================================================

lazy_static::lazy_static! {
    static ref TEMP_FILE_SUBSTS: Vec<(regex::Regex, &'static str)> = {
        vec![
            (r#"┌─ .+[/\\]original\.spec"#, "┌─ <input>"),
            (r#"┌─ .+[/\\]Xx_MAPFILE INPUT_xX"#, "┌─ <mapfile>"),
            (r#"while writing '[^']+': "#, "while writing '<output>':"),
            (r#"^(warning|error): .+[/\\]Xx_COMPILATION OUTPUT_xX:"#, r#"$1: <decompile-input>:"#),
        ].into_iter().map(|(pat, subst)| {
            (regex::Regex::new(pat).unwrap(), subst)
        }).collect()
    };
}

impl Format {
    /// Attempt to compile but expect failure and extract stderr.
    pub fn compile_fail_stderr(&self, source: &TestFile, mapfile: Option<&TestFile>) -> String {
        let output = {
            Command::cargo_bin(self.cmd).unwrap()
                .arg("compile")
                .arg("-g").arg(format!("{}", self.game))
                .arg(source.as_path())
                .arg("-o").arg("/dev/null")
                .args(optional_mapfile_args(mapfile))
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
        crate::integration_impl::_check_compile_fail_output(&$stderr, $expected, |stderr| {
            assert_snapshot!{stderr};
        });
    }}
}

/// Perform a snapshot test of something.
macro_rules! assert_snapshot {
    ($stderr:expr) => {{
        insta::with_settings!{{snapshot_path => snapshot_path!()}, {
            insta::assert_snapshot!{$stderr};
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

#[macro_use]
pub mod source_test;
