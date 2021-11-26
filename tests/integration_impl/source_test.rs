use super::{Format, TestFile, ProgramResult};
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

struct SourceTestOptions {
    shared_mapfiles: Vec<String>,
    compile_props: TestCommandProps,
    decompile_props: TestCommandProps,
    check_compiled: Option<Box<dyn FnMut(&TestFile, &Format)>>,
    check_decompiled: Option<Box<dyn FnMut(&str)>>,
    recompile: bool,
    require_roundtrip: bool,
}

impl Default for SourceTestOptions {
    fn default() -> Self {
        SourceTestOptions {
            shared_mapfiles: Default::default(),
            compile_props: Default::default(),
            decompile_props: Default::default(),
            check_compiled: Default::default(),
            check_decompiled: Default::default(),
            recompile: true,
            require_roundtrip: true,
        }
    }
}

impl SourceTest {
    pub fn new(format: &'static Format) -> Self {
        let source = SourceBuilder::new(format);
        SourceTest { format, source, options: Default::default() }
    }

    pub fn main_body(&mut self, text: impl Into<String>) { self.source.main_body = Some(text.into()); }
    pub fn items(&mut self, text: impl Into<String>) { self.source.items = Some(text.into()); }
    pub fn full_source(&mut self, text: impl Into<Vec<u8>>) { self.source.full_source = Some(text.into()); }

    pub fn compile_args(&mut self, args: &[impl AsRef<OsStr>]) { self.options.compile_props.extra_args.extend(args.iter().map(|x| x.as_ref().to_owned())); }
    pub fn mapfile(&mut self, text: impl Into<String>) { self.options.shared_mapfiles.push(text.into()); }
    pub fn expect_error(&mut self, text: impl Into<String>) { self.options.compile_props.expected.expect_error(text.into()); }
    pub fn expect_warning(&mut self, text: impl Into<String>) { self.options.compile_props.expected.expect_warning(text.into()); }

    pub fn compile_mapfile(&mut self, text: impl Into<String>) { self.options.compile_props.mapfiles.push(text.into()); }

    pub fn decompile_args(&mut self, args: &[impl AsRef<OsStr>]) {
        self.options.decompile_props.extra_args.extend(args.iter().map(|x| x.as_ref().to_owned()));
    }
    pub fn decompile_mapfile(&mut self, text: impl Into<String>) {
        self.options.decompile_props.mapfiles.push(text.into());
    }
    pub fn expect_decompile_warning(&mut self, text: impl Into<String>) {
        self.options.compile_props.expected.expect_success();
        self.options.decompile_props.expected.expect_warning(text.into());
    }
    pub fn expect_decompile_error(&mut self, text: impl Into<String>) {
        self.options.compile_props.expected.expect_success();
        self.options.decompile_props.expected.expect_error(text.into());
    }

    pub fn check_compiled(&mut self, func: impl FnMut(&TestFile, &Format) + 'static) {
        self.options.compile_props.expected.expect_success();
        self.options.check_compiled = Some(Box::new(func));
    }
    pub fn check_decompiled(&mut self, func: impl FnMut(&str) + 'static) {
        self.options.compile_props.expected.expect_success();
        self.options.decompile_props.expected.expect_success();
        self.options.check_decompiled = Some(Box::new(func));
    }
    /// If true (default), recompilation is attempted after any decompilation.
    ///
    /// (mind: decompilation is normally only attempted if [`Self::check_decompiled`],
    ///  [`Self::expect_decompile_warning`], or [`Self::expect_decompile_error`] is used)
    pub fn require_roundtrip(&mut self, value: bool) {
        self.options.require_roundtrip = value;
    }
    /// If true (default) and recompilation occurs, it must match the first compilation.
    ///
    /// (mind: recompilation normally occurs only if decompilation occurs AND succeeds)
    pub fn recompile(&mut self, value: bool) {
        self.options.recompile = value;
    }
}

#[derive(Debug, Default)]
struct TestCommandProps {
    mapfiles: Vec<String>,
    extra_args: Vec<OsString>,
    expected: ExpectedResult,
}

#[derive(Debug, Default)]
pub struct ExpectedResult {
    is_error: Option<bool>,
    message: Option<String>,
}

impl ExpectedResult {
    fn expect_success(&mut self) {
        self.is_error.get_or_insert(false);
    }

    fn expect_warning(&mut self, message: String) {
        assert!(self.message.is_none(), "multiple expect_warning/expect_error not yet supported");
        self.is_error.get_or_insert(false);
        self.message = Some(message);
    }

    fn expect_error(&mut self, message: String) {
        assert!(self.message.is_none(), "multiple expect_warning/expect_error not yet supported");
        self.is_error = Some(true);
        self.message = Some(message);
    }
}

impl TestCommandProps {
    /// Should this test command run?
    fn has_action(&self) -> bool { self.expected.is_error.is_some() }
}

impl ProgramResult {
    #[track_caller]
    pub fn check_with_expected(
        &self,
        expected_result: &ExpectedResult,
        mut check_compile_fail_output: impl FnMut(&str, &str),
    ) {
        assert_eq!(self.output.is_none(), expected_result.is_error.unwrap(), "exit code mismatch");
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
        &mut self,  // &mut to call FnMut closures
        // A closure that calls the check_compile_fail_output! macro.
        // This is a kludge to get the correct snapshot file name.
        check_compile_fail_output: fn(&str, &str),
    ) {
        truth::setup_for_test_harness();

        let shared_mapfiles = {
            self.options.shared_mapfiles.iter()
                .map(|s| TestFile::from_content("Xx_MAPFILE INPUT_xX", s))
                .collect::<Vec<_>>()
        };
        let compile_only_mapfiles = {
            self.options.compile_props.mapfiles.iter()
                .map(|s| TestFile::from_content("Xx_MAPFILE INPUT_xX", s))
                .collect::<Vec<_>>()
        };
        // FIXME dumb way
        let decompile_only_mapfiles = {
            self.options.decompile_props.mapfiles.iter()
                .map(|s| TestFile::from_content("Xx_MAPFILE INPUT_xX", s))
                .collect::<Vec<_>>()
        };
        let compile_mapfiles = || shared_mapfiles.iter().chain(&compile_only_mapfiles);
        let decompile_mapfiles = || shared_mapfiles.iter().chain(&decompile_only_mapfiles);

        assert!(self.options.compile_props.has_action(), "nothing to do!");

        let source = self.source.build("original.spec");
        let args = self.options.compile_props.extra_args.iter().map(AsRef::as_ref).collect::<Vec<_>>();
        let result = self.format.compile(&source, &args, compile_mapfiles());
        result.check_with_expected(&self.options.compile_props.expected, |stderr, expected| {
            check_compile_fail_output(stderr, expected)
        });
        let compiled = result.output;

        if !self.options.compile_props.expected.is_error.unwrap() {
            if let Some(func) = &mut self.options.check_compiled {
                func(compiled.as_ref().unwrap(), self.format);
            };
        }

        if self.options.decompile_props.has_action() {
            let compiled = compiled.as_ref().unwrap();
            let args = self.options.decompile_props.extra_args.iter().map(AsRef::as_ref).collect::<Vec<_>>();
            let result = self.format.decompile(compiled, &args, decompile_mapfiles());
            result.check_with_expected(&self.options.decompile_props.expected, |stderr, expected| {
                check_compile_fail_output(stderr, expected);
            });

            if !self.options.decompile_props.expected.is_error.unwrap() {
                let decompiled = result.output.unwrap();
                if let Some(func) = &mut self.options.check_decompiled {
                    func(&decompiled.read_to_string());
                };
                if self.options.recompile {
                    let result = self.format.compile(&decompiled, &[][..], decompile_mapfiles());
                    let recompiled = result.output.expect("recompile failed?!");
                    if self.options.require_roundtrip {
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

    fn build(&self, filename: &'static str) -> TestFile {
        let do_parts = self.main_body.is_some() || self.items.is_some();
        let do_full = self.full_source.is_some();
        assert!(do_full || do_parts, "missing 'main_body', 'items', or 'full_source'");
        assert!(!(do_full && do_parts), "'full_source' cannot be used with 'main_body' or 'items'");

        if do_parts {
            TestFile::from_content(filename, format!(
                "{}\n{}\n{}",
                self.format.script_head,
                self.items.clone().unwrap_or_else(String::new),
                (self.format.make_main)(&self.main_body.clone().unwrap_or_else(String::new)),
            ))
        } else {
            TestFile::from_content(filename, self.full_source.clone().unwrap())
        }
    }
}

macro_rules! question_kleene_to_option {
    ( $thing:expr ) => { Some($thing) };
    ( ) => { None };
}
