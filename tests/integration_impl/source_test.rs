use super::{Format, TestFile, ProgramResult};
use super::parse_errors::{self, ExpectedDiagnostic};
use std::ffi::{OsStr, OsString};

/// Generates a test that compiles a source script and maybe also decompiles it.
///
/// The purpose of this is to reduce the friction to writing tests as much as possible.
/// It reduces noise by allowing things not relevant to a given test to be left out.  It also
/// reduces the amount of busywork in converting a test back and forth between a compile-succeed
/// test and a compile-fail test (a thing you frequently have to do when making a group of tests
/// that share a lot of source).
///
/// The available test attributes currently come directly from the methods on [`SourceTest`].
/// (one might ask, why use this macro when one could use that builder API directly?
///  The answer is partly historical, but also partly because a macro of some form is necessary
///  to get the correct test names in `insta` snapshots.)
macro_rules! source_test {
    (
        $(# $attr:tt)*
        $format:ident, $test_name:ident
        $(, $method:ident : $value:expr )*
        $(,)?
    ) => {
        #[test]
        $(# $attr)*
        fn $test_name() {
            use crate::integration_impl::source_test;

            let format = &$format;
            let mut test = source_test::SourceTest::new(format);
            $( __source_test_attr!( test, $method, $value ); )*
            test.run(|stderr| assert_snapshot!(stderr));
        }
    };
}

macro_rules! __source_test_attr {
    // ($test:expr, $method:ident, [$($item:expr),*$(,)?]) => {
    //     $test.$method(vec![ $(From::from($item)),* ]);
    // };
    ($test:expr, $method:ident, $value:expr) => {
        $test.$method($value);
    };
}

/// Internal representation of the input to the source_test macro.
pub struct SourceTest {
    format: &'static Format,
    source: SourceBuilder,
    options: SourceTestOptions,
}

#[derive(Default)]
struct SourceTestOptions {
    next_mapfile_index: usize,
    shared_mapfiles: Vec<TestFile>,
    compile: TestCommandProps,
    decompile: TestCommandProps,
    check_compiled: Option<Box<dyn FnOnce(&TestFile, &Format)>>,
    check_decompiled: Option<Box<dyn FnOnce(&str)>>,
    skip_recompile: bool,
    skip_roundtrip: bool,
}

#[derive(Debug, Clone, Default)]
struct TestCommandProps {
    mapfiles: Vec<TestFile>,
    extra_args: Vec<OsString>,
    expected: ExpectedResult,
}

use result::ExpectedResult;
mod result {
    use super::*;

    #[derive(Debug, Clone, Default)]
    pub(super) struct ExpectedResult {
        is_success: Option<bool>,
        diagnostics: Vec<ExpectedDiagnostic>,
    }

    impl ExpectedResult {
        /// Returns true if any of the `expect_` methods have been called.  If this hasn't been called,
        /// the test step doesn't need to run.
        pub(super) fn should_run(&self) -> bool {
            // the diagnostics check is to ensure warnings get tested
            !(self.is_success.is_none() && self.diagnostics.is_empty())
        }

        pub(super) fn should_succeed(&self) -> bool {
            self.is_success.unwrap_or(true)
        }

        /// Expect the program invocation to succeed (`true`) or (`fail`).  This can be called multiple times
        /// but will panic if called with conflicting values.
        pub(super) fn expect_success(&mut self, success: bool) {
            assert_ne!(self.is_success, Some(!success), "conflicting expectations on command (must succeed and fail)");
            self.is_success = Some(success);
        }

        pub(super) fn expect_diagnostics(&mut self, diagnostics: impl IntoIterator<Item=ExpectedDiagnostic>) {
            for diagnostic in diagnostics {
                if diagnostic.implies_failure() {
                    self.expect_success(false);
                }
                self.diagnostics.push(diagnostic);
            }
        }

        pub(super) fn expect_error(&mut self, pattern: String) {
            self.expect_diagnostics(vec![ExpectedDiagnostic::new_error_without_location(pattern)])
        }

        pub(super) fn expect_warning(&mut self, pattern: String) {
            self.expect_diagnostics(vec![ExpectedDiagnostic::new_warning_without_location(pattern)])
        }

        pub(super) fn expected_diagnostics(&self) -> &[ExpectedDiagnostic] {
            &self.diagnostics
        }
    }
}

impl SourceTest {
    pub fn new(format: &'static Format) -> Self {
        let source = SourceBuilder::new(format);
        SourceTest { format, source, options: Default::default() }
    }
}

impl SourceTest {
    // whenever a builder method is about to do something
    fn expect_compilation_to_succeed(&mut self) {
        self.options.compile.expected.expect_success(true);
    }

    fn expect_decompilation_to_succeed(&mut self) {
        self.expect_decompilation_can_run();
        self.options.decompile.expected.expect_success(true);
    }

    fn expect_decompilation_can_run(&mut self) {
        self.expect_compilation_to_succeed();
    }

    fn expect_recompilation_can_run(&mut self) {
        self.expect_decompilation_to_succeed();
    }
}

impl SourceTest {
    fn make_mapfile(&mut self, text: impl Into<String>) -> (TestFile, Vec<ExpectedDiagnostic>) {
        self.options.next_mapfile_index += 1;
        let actual_filename = format!("Xx_mapfile-{}_xX", self.options.next_mapfile_index);
        let normalized_filename = format!("<mapfile-{}>", self.options.next_mapfile_index);

        let (text, diagnostics) = parse_errors::parse_expected_diagnostics(&normalized_filename, text.into().as_bytes());
        let file = TestFile::from_content(&actual_filename, &text);
        (file, diagnostics)
    }

    // source
    pub fn main_body(&mut self, text: impl Into<String>) {
        self.source.main_body = Some(text.into());
    }
    pub fn items(&mut self, text: impl Into<String>) {
        self.source.items = Some(text.into());
    }
    pub fn full_source(&mut self, text: impl Into<Vec<u8>>) {
        self.source.full_source = Some(text.into());
    }

    // shared (compile/decompile)
    pub fn mapfile(&mut self, text: impl Into<String>) {
        let (mapfile, diagnostics) = self.make_mapfile(text);
        self.options.shared_mapfiles.push(mapfile);
        self.options.compile.expected.expect_diagnostics(diagnostics);
    }

    // compile input
    pub fn compile_args(&mut self, args: &[impl AsRef<OsStr>]) {
        self.options.compile.extra_args.extend(args.iter().map(|x| x.as_ref().to_owned()));
    }
    pub fn compile_mapfile(&mut self, text: impl Into<String>) {
        let (mapfile, diagnostics) = self.make_mapfile(text);
        self.options.compile.mapfiles.push(mapfile);
        self.options.compile.expected.expect_diagnostics(diagnostics);
    }
    // compile result
    pub fn expect_error(&mut self, text: impl Into<String>) {
        self.options.compile.expected.expect_error(text.into());
    }
    pub fn expect_warning(&mut self, text: impl Into<String>) {
        self.options.compile.expected.expect_warning(text.into());
    }
    pub fn check_compiled(&mut self, func: impl FnMut(&TestFile, &Format) + 'static) {
        self.expect_compilation_to_succeed();
        self.options.check_compiled = Some(Box::new(func));
    }

    // decompile input
    pub fn decompile_args(&mut self, args: &[impl AsRef<OsStr>]) {
        self.expect_decompilation_can_run();
        self.options.decompile.extra_args.extend(args.iter().map(|x| x.as_ref().to_owned()));
    }
    #[allow(dead_code)]
    pub fn decompile_mapfile(&mut self, text: impl Into<String>) {
        self.expect_decompilation_can_run();
        let (mapfile, diagnostics) = self.make_mapfile(text);
        self.options.decompile.mapfiles.push(mapfile);
        self.options.decompile.expected.expect_diagnostics(diagnostics);
    }
    // decompile result
    pub fn check_decompiled(&mut self, func: impl FnMut(&str) + 'static) {
        self.expect_decompilation_to_succeed();
        self.options.check_decompiled = Some(Box::new(func));
    }
    pub fn expect_decompile_warning(&mut self, text: impl Into<String>) {
        self.expect_decompilation_can_run();
        self.options.decompile.expected.expect_warning(text.into());
    }
    pub fn expect_decompile_error(&mut self, text: impl Into<String>) {
        self.expect_decompilation_can_run();
        self.options.decompile.expected.expect_error(text.into());
    }

    /// If true (default), recompilation is attempted after any decompilation.
    ///
    /// (mind: decompilation is normally only attempted if [`Self::check_decompiled`],
    ///  [`Self::expect_decompile_warning`], or [`Self::expect_decompile_error`] is used)
    pub fn recompile(&mut self, value: bool) {
        self.expect_recompilation_can_run();
        self.options.skip_recompile = !value;
    }
    /// If true (default) and recompilation occurs, it must match the first compilation.
    ///
    /// (mind: recompilation normally occurs only if decompilation occurs AND succeeds)
    pub fn require_roundtrip(&mut self, value: bool) {
        self.expect_recompilation_can_run();
        self.options.skip_roundtrip = !value;
    }
}

impl ProgramResult {
    #[track_caller]
    fn check_with_expected(
        &self,
        expected_result: &ExpectedResult,
        mut do_snapshot: impl FnMut(&str),
    ) {
        assert_eq!(self.output.is_some(), expected_result.should_succeed(), "exit code mismatch");
        let stderr_str = String::from_utf8_lossy(&self.stderr);
        let normalized_stderr = super::make_output_deterministic(&stderr_str);
        let actual_diagnostics = parse_errors::parse_diagnostics(normalized_stderr.as_bytes());

        let allow_extra = false;
        parse_errors::compare_actual_and_expected_diagnostics(
            &actual_diagnostics,
            expected_result.expected_diagnostics(),
            allow_extra,
        );
        if !self.stderr.is_empty() {
            do_snapshot(&normalized_stderr)
        }
    }
}

impl SourceTest {
    #[track_caller]
    pub fn run(
        mut self,
        // A closure that does an insta snapshot test.
        // This is a kludge to get the correct snapshot file name.
        do_snapshot: fn(&str),
    ) {
        // do some last minute preparation/modifications that couldn't be done until the
        // user was finished with the builder
        let (source, source_diagnostics) = self.source.build("Xx_input_xX");
        self.options.compile.expected.expect_diagnostics(source_diagnostics);

        // defer to pure impl
        Self::run_impl(self.format, &source, self.options, do_snapshot)
    }

    // #[track_caller]
    fn run_impl(
        format: &Format,
        source: &TestFile,
        options: SourceTestOptions,
        do_snapshot: fn(&str),
    ) {
        truth::setup_for_test_harness();

        let compile_mapfiles = options.shared_mapfiles.iter().chain(&options.compile.mapfiles);
        let decompile_mapfiles = options.shared_mapfiles.iter().chain(&options.decompile.mapfiles);
        let recompile_mapfiles = options.shared_mapfiles.iter().chain(&options.decompile.mapfiles);

        assert!(options.compile.expected.should_run(), "nothing to do!");

        let args = options.compile.extra_args.iter().map(AsRef::as_ref).collect::<Vec<_>>();
        let result = format.compile(&source, &args, compile_mapfiles);
        result.check_with_expected(&options.compile.expected, do_snapshot);
        let compiled = result.output;

        if options.compile.expected.should_succeed() {
            if let Some(func) = options.check_compiled {
                func(compiled.as_ref().unwrap(), format);
            };
        }

        if options.decompile.expected.should_run() {
            let compiled = compiled.as_ref().unwrap();
            let args = options.decompile.extra_args.iter().map(AsRef::as_ref).collect::<Vec<_>>();
            let result = format.decompile(compiled, &args, decompile_mapfiles);

            if let Some(output) = &result.output {
                eprintln!("=== DECOMPILE OUTPUT ===");
                eprintln!("{}", output.read_to_string());
            }

            result.check_with_expected(&options.decompile.expected, do_snapshot);

            if options.decompile.expected.should_succeed() {
                let decompiled = result.output.unwrap();
                if let Some(func) = options.check_decompiled {
                    func(&decompiled.read_to_string());
                };
                if !options.skip_recompile {
                    let result = format.compile(&decompiled, &[][..], recompile_mapfiles);
                    let recompiled = result.output.expect("recompile failed?!");
                    if !options.skip_roundtrip {
                        assert_eq!(compiled.read(), recompiled.read());
                    }
                }
            }
        }
    }
}

struct SourceBuilder {
    format: &'static Format,
    items: Option<String>,
    main_body: Option<String>,
    full_source: Option<Vec<u8>>,
}

impl SourceBuilder {
    fn new(format: &'static Format) -> Self {
        SourceBuilder {
            format, items: None, main_body: None, full_source: None,
        }
    }

    fn build(&self, filename: &'static str) -> (TestFile, Vec<ExpectedDiagnostic>) {
        let content = self.build_utf8();
        let normalized_filename = "<input>";
        let (content, diagnostics) = parse_errors::parse_expected_diagnostics(normalized_filename, &content);
        (TestFile::from_content(filename, content), diagnostics)
    }

    fn build_utf8(&self) -> Vec<u8> {
        let do_parts = self.main_body.is_some() || self.items.is_some();
        let do_full = self.full_source.is_some();
        assert!(do_full || do_parts, "missing 'main_body', 'items', or 'full_source'");
        assert!(!(do_full && do_parts), "'full_source' cannot be used with 'main_body' or 'items'");

        if do_parts {
            format!(
                "{}\n{}\n{}",
                self.format.script_head,
                self.items.clone().unwrap_or_else(String::new),
                (self.format.make_main)(&self.main_body.clone().unwrap_or_else(String::new)),
            ).into()
        } else {
            self.full_source.clone().unwrap()
        }
    }
}
