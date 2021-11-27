use super::{Format, TestFile, ProgramResult};
use super::parse_errors::{self, ExpectedDiagnostic};
use std::ffi::{OsStr, OsString};

// used to implement defaults for some optional macro parts by writing `first_token!( $($thing)?  "" )`
macro_rules! first_token {
    ($tok:tt $($rest:tt)*) => { $tok };
}

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
            test.run(
                |stderr, expected| check_compile_fail_output!(stderr, expected),
            );
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
    recompile: Option<bool>,
    require_roundtrip: Option<bool>,
}

#[derive(Debug, Clone, Default)]
struct TestCommandProps {
    should_run: bool,
    mapfiles: Vec<TestFile>,
    extra_args: Vec<OsString>,
    expected: ExpectedResult,
}

#[derive(Debug, Clone, Default)]
struct ExpectedResult {
    is_error: Option<bool>,
    diagnostics: Vec<ExpectedDiagnostic>,
}

impl Default for SourceTestOptions {
    fn default() -> Self {
        SourceTestOptions {
            compile: TestCommandProps {
                should_run: true,
                ..Default::default()
            },
            ..Default::default()
        }
    }
}

impl SourceTest {
    pub fn new(format: &'static Format) -> Self {
        let source = SourceBuilder::new(format);
        SourceTest { format, source, options: Default::default() }
    }
}

/// These methods attempt to help identify malformed test inputs.
///
/// E.g. if a test has both an expected compile error and a flag related to decompilation,
/// then something must be wrong because decompilation will not be possible.
impl SourceTest {
    fn sanity_check_for_no_decompile(&self) {
        assert!(!self.options.decompile.should_run);
        assert!(self.options.decompile.expected.is_error.is_none());
        self.sanity_check_for_no_recompile();
    }

    fn sanity_check_for_no_recompile(&self) {
        assert!(self.options.recompile.is_none());
        self.sanity_check_for_no_roundtrip();
    }

    fn sanity_check_for_no_roundtrip(&self) {
        assert!(self.options.require_roundtrip.is_none());
    }
}

impl SourceTest {
    fn make_mapfile(&mut self, text: impl Into<String>) -> (TestFile, Vec<ExpectedDiagnostic>) {
        self.next_mapfile_index += 1;
        let filename = format!("Xx_MAPFILE INPUT {}_xX", self.next_mapfile_index);

        let (text, diagnostics) = parse_errors::parse_expected_diagnostics(&filename, &text.into());
        let file = TestFile::from_content(&filename, &text);
        (file, diagnostics)
    }

    pub fn main_body(&mut self, text: impl Into<String>) {
        self.source.main_body = Some(text.into());
    }
    pub fn items(&mut self, text: impl Into<String>) {
        self.source.items = Some(text.into());
    }
    pub fn full_source(&mut self, text: impl Into<Vec<u8>>) {
        self.source.full_source = Some(text.into());
    }

    pub fn compile_args(&mut self, args: &[impl AsRef<OsStr>]) { self.options.compile.extra_args.extend(args.iter().map(|x| x.as_ref().to_owned())); }
    pub fn mapfile(&mut self, text: impl Into<String>) {
        let (mapfile, diagnostics) = self.make_mapfile(text);
        self.options.shared_mapfiles.push(mapfile);
        self.options.compile.expected.extend(diagnostics);
    }
    pub fn expect_error(&mut self, text: impl Into<String>) { self.options.compile.expected.expect_error(text.into()); }
    pub fn expect_warning(&mut self, text: impl Into<String>) { self.options.compile.expected.expect_warning(text.into()); }

    pub fn compile_mapfile(&mut self, text: impl Into<String>) {
        let (mapfile, diagnostics) = self.make_mapfile(text);
        self.options.compile.mapfiles.push(mapfile);
        self.options.compile.expected.extend(diagnostics);
    }

    pub fn decompile_args(&mut self, args: &[impl AsRef<OsStr>]) {
        self.options.decompile.extra_args.extend(args.iter().map(|x| x.as_ref().to_owned()));
    }
    pub fn decompile_mapfile(&mut self, text: impl Into<String>) {
        let (mapfile, diagnostics) = self.make_mapfile(text);
        self.options.decompile.mapfiles.push(mapfile);
        self.options.decompile.expected.extend(diagnostics);
    }
    pub fn expect_decompile_warning(&mut self, text: impl Into<String>) {
        self.options.compile.expected.expect_success();
        self.options.decompile.expected.expect_warning(text.into());
    }
    pub fn expect_decompile_error(&mut self, text: impl Into<String>) {
        self.options.compile.expected.expect_success();
        self.options.decompile.expected.expect_error(text.into());
    }

    pub fn check_compiled(&mut self, func: impl FnMut(&TestFile, &Format) + 'static) {
        self.options.compile.expected.expect_success();
        self.options.check_compiled = Some(Box::new(func));
    }
    pub fn check_decompiled(&mut self, func: impl FnMut(&str) + 'static) {
        self.options.compile.expected.expect_success();
        self.options.decompile.expected.expect_success();
        self.options.check_decompiled = Some(Box::new(func));
    }
    /// If true (default), recompilation is attempted after any decompilation.
    ///
    /// (mind: decompilation is normally only attempted if [`Self::check_decompiled`],
    ///  [`Self::expect_decompile_warning`], or [`Self::expect_decompile_error`] is used)
    pub fn recompile(&mut self, value: bool) {
        self.options.recompile = Some(value);
    }
    /// If true (default) and recompilation occurs, it must match the first compilation.
    ///
    /// (mind: recompilation normally occurs only if decompilation occurs AND succeeds)
    pub fn require_roundtrip(&mut self, value: bool) {
        self.options.require_roundtrip = Some(value);
    }
}

impl ExpectedResult {
    fn expect_success(&mut self, success: bool) {
        assert_ne!(self.is_error, Some(!success), "conflicting expectations on command (must succeed and fail)");
        self.is_error = Some(success);
    }

    fn expect_diagnostics(&mut self, diagnostics: impl IntoIterator<Item=ExpectedDiagnostic>) {
        for diagnostic in diagnostics {
            if diagnostic.implies_failure() {
                self.expect_success(false);
            }
            self.diagnostics.push(diagnostic);
        }
    }

    fn expect_error(&mut self, pattern: String) {
        self.expect_diagnostics(vec![ExpectedDiagnostic::new_error_without_location(pattern)])
    }

    fn expect_warning(&mut self, pattern: String) {
        self.expect_diagnostics(vec![ExpectedDiagnostic::new_warning_without_location(pattern)])
    }
}

impl ProgramResult {
    #[track_caller]
    pub fn check_with_expected(
        &self,
        expected_result: &ExpectedResult,
        mut check_compile_fail_output: impl FnMut(&str, &str),
    ) {
        assert_eq!(self.output.is_none(), expected_result.is_error.unwrap_or(false), "exit code mismatch");
        match (self.output.is_some(), expected_result.is_error) {
            (_, None) => panic!("check_with_expected called when no action was expected (bug in test utils)"),
            (true, Some(false)) => {},
            (false, Some(true)) => {},
            (true, Some(true)) => panic!("expected success but got error"),
            (false, Some(false)) => panic!("expected error but program succeeded"),
        }
        match (&self.stderr, &expected_result.message) {
            (None, None) => {},
            (None, Some(_pattern)) => panic!("no warning or error when one was expected"),
            (Some(_stderr), None) => panic!("unexpected warning or error"),
            (Some(stderr), Some(pattern)) => check_compile_fail_output(stderr, pattern),
        }
    }
}

impl SourceTest {
    #[track_caller]
    pub fn run(
        mut self,
        // A closure that calls the check_compile_fail_output! macro.
        // This is a kludge to get the correct snapshot file name.
        check_compile_fail_output: fn(&str, &str),
    ) {
        // do some last minute preparation/modifications that couldn't be done until the
        // user was finished with the builder
        let (source, source_diagnostics) = self.source.build("original.spec");
        self.options.compile.expected.expect_diagnostics(source_diagnostics);

        // defer to pure impl
        Self::run_impl(self.format, &source, self.options, check_compile_fail_output)
    }

    #[track_caller]
    fn run_impl(
        format: &Format,
        source: &TestFile,
        options: SourceTestOptions,
        check_compile_fail_output: fn(&str, &str),
    ) {
        truth::setup_for_test_harness();

        let compile_mapfiles = options.shared_mapfiles.iter().chain(&options.compile.mapfiles);
        let decompile_mapfiles = options.shared_mapfiles.iter().chain(&options.decompile.mapfiles);
        let recompile_mapfiles = options.shared_mapfiles.iter().chain(&options.decompile.mapfiles);

        assert!(options.compile.should_run, "nothing to do!");

        let args = options.compile.extra_args.iter().map(AsRef::as_ref).collect::<Vec<_>>();
        let result = format.compile(&source, &args, compile_mapfiles());
        result.check_with_expected(&options.compile.expected, |stderr, expected| {
            check_compile_fail_output(stderr, expected)
        });
        let compiled = result.output;

        if !options.compile.expected.is_error.unwrap() {
            if let Some(func) = &mut options.check_compiled {
                func(compiled.as_ref().unwrap(), format);
            };
        }

        if options.decompile.has_action() {
            let compiled = compiled.as_ref().unwrap();
            let args = options.decompile.extra_args.iter().map(AsRef::as_ref).collect::<Vec<_>>();
            let result = format.decompile(compiled, &args, decompile_mapfiles());
            result.check_with_expected(&options.decompile.expected, |stderr, expected| {
                check_compile_fail_output(stderr, expected);
            });

            if !options.decompile.expected.is_error.unwrap() {
                let decompiled = result.output.unwrap();
                if let Some(func) = options.check_decompiled {
                    func(&decompiled.read_to_string());
                };
                if options.recompile.unwrap_or(true) {
                    let result = format.compile(&decompiled, &[][..], decompile_mapfiles());
                    let recompiled = result.output.expect("recompile failed?!");
                    if options.require_roundtrip {
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

macro_rules! question_kleene_to_option {
    ( $thing:expr ) => { Some($thing) };
    ( ) => { None };
}
