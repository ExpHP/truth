use super::{Format, TestFile};

// used to implement defaults for some optional macro parts by writing `first_token!( $($thing)?  "" )`
macro_rules! first_token {
    ($tok:tt $($rest:tt)*) => { $tok };
}

/// Generates a test that does *something* to a source script.
///
/// The purpose of this is to reduce the friction to writing tests as much as possible.
/// It reduces noise by allowing things not relevant to a given test to be left out.  It also
/// reduces the amount of busywork in converting a test back and forth between a compile-succeed
/// test and a compile-fail test (a thing you frequently have to do when making a group of tests
/// that share a lot of source).
///
/// This is largely a wrapper around the TestFile API.  You can use that directly if you need
/// to do something not supported by the macro.
macro_rules! source_test {
    (
        $(# $attr:tt)*
        $format:ident, $test_name:ident

        $(, mapfile: $mapfile:expr)?
        $(, compile_args: $compile_args:expr)?
        // -------------------------
        // args to make_source!
        $(, items: $items:expr)?
        $(, main_body: $main_body:expr)?
        $(, full_source: $full_source:expr)?

        // -------------------------
        // Test details
        //
        // You must supply one of the following things:

        // Snapshot stderr and check for a substring.
        // This is incompatible with anything other than check_compiled.
        $(, expect_warning: $expect_warning_msg:expr)?
        // Compile the code and run the given closure on the compiled TestFile.
        $(, check_compiled: $check_fn:expr)?


        // Does an "SBSB" test to test decompilation of a file compiled from simple source.
        //
        // IMPORTANT: Please see the documentation of Format::sbsb_test for more information.
        $(, decompile_args: $sbsb_decompile_args:expr)?
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
        $(, expect_error: $expect_error_msg:expr)?

        // These are like a "failing" version of SBSB.  They compile and then check for stderr during decompilation.
        $(, expect_decompile_warning: $expect_decompile_warning_msg:expr)?
        $(, expect_decompile_error: $expect_decompile_error_msg:expr)?

        $(,)?
    ) => {
        #[test]
        $(# $attr)*
        fn $test_name() {
            let format = &$format;
            crate::integration_impl::source_test::SourceTest {
                format,
                source: make_source!(
                    $format
                    $(, items: $items)?
                    $(, main_body: $main_body)?
                    $(, full_source: $full_source)?
                ),
                mapfile: question_kleene_to_option!( $($mapfile.to_string())? ),
                compile_args: question_kleene_to_option!( $(&$compile_args)? ),
                expect_error: question_kleene_to_option!( $($expect_error_msg.to_string())? ),
                expect_warning: question_kleene_to_option!( $($expect_warning_msg.to_string())? ),
                expect_decompile_error: question_kleene_to_option!( $($expect_decompile_error_msg.to_string())? ),
                expect_decompile_warning: question_kleene_to_option!( $($expect_decompile_warning_msg.to_string())? ),
                sbsb: question_kleene_to_option!( $($sbsb_check_fn)? ),
                check_compiled: question_kleene_to_option!( $($check_fn)? ),
                sbsb_decompile_args: question_kleene_to_option!( $(&$sbsb_decompile_args)? ),
            }.run(|stderr, expected| check_compile_fail_output!(stderr, expected))
        }
    };
}

/// Internal representation of the input to the source_test macro.
pub struct SourceTest {
    pub format: &'static Format,
    pub source: TestFile,
    pub mapfile: Option<String>,
    pub compile_args: Option<&'static [&'static str]>,
    pub check_compiled: Option<fn(&TestFile, &Format)>,
    pub expect_warning: Option<String>,
    pub expect_error: Option<String>,
    pub expect_decompile_warning: Option<String>,
    pub expect_decompile_error: Option<String>,
    pub sbsb_decompile_args: Option<&'static [&'static str]>,
    pub sbsb: Option<fn(&str)>,
}

impl SourceTest {
    #[track_caller]
    pub fn run(
        &self,
        // A closure that calls the check_compile_fail_output! macro.
        // This is a kludge to get the correct snapshot file name.
        check_compile_fail_output: fn(&str, &str),
    ) {
        truth::setup_for_test_harness();

        let mut did_something = false;

        let mapfile = self.mapfile.as_ref().map(|s| TestFile::from_content("Xx_MAPFILE INPUT_xX", s));
        let compile_args = self.compile_args.unwrap_or(&[]);

        if self.check_compiled.is_some() || self.expect_warning.is_some() {
            let (outfile, output) = self.format.compile_and_capture(&self.source, compile_args, mapfile.as_ref());
            let stderr = String::from_utf8_lossy(&output.stderr);
            match &self.expect_warning {
                Some(expected) => {
                    check_compile_fail_output(&stderr, expected);
                    did_something = true;
                },
                None => assert_eq!(stderr, ""),
            }
            if let Some(check_fn) = self.check_compiled {
                check_fn(&outfile, &self.format);
                did_something = true;
            }
        }

        if let Some(sbsb_check_fn) = self.sbsb {
            // decompile test
            assert!(self.compile_args.is_none(), "sbsb + compile_args not implemented");
            assert!(self.expect_decompile_warning.is_none(), "combining sbsb + expect_decompile_warning is not yet implemented");
            self.format.sbsb_test(&self.source, self.sbsb_decompile_args.unwrap_or(&[]), mapfile.as_ref(), sbsb_check_fn);
            did_something = true;

        } else if self.expect_decompile_error.is_some() || self.expect_decompile_warning.is_some() {
            // decompile-fail test
            assert!(self.compile_args.is_none(), "decompile-fail + compile_args not implemented");
            assert!(!(self.expect_decompile_error.is_some() && self.expect_decompile_warning.is_some()));
            let should_error = self.expect_decompile_error.is_some();
            let expect_msg = self.expect_decompile_error.as_deref().or(self.expect_decompile_warning.as_deref()).unwrap();
            self.format.sbsb_fail_test(
                &self.source, self.sbsb_decompile_args.unwrap_or(&[]), mapfile.as_ref(),
                should_error, |stderr| check_compile_fail_output(stderr, expect_msg),
            );
            did_something = true;

        } else {
            if self.sbsb_decompile_args.is_some() {
                panic!("Test was provided with decompile_args but was not an sbsb or decompile_fail test!")
            }
        }

        if let Some(expect_error_msg) = &&self.expect_error {
            assert!(self.compile_args.is_none(), "compile-fail + compile_args not implemented");
            let stderr = self.format.compile_fail_stderr(&self.source, mapfile.as_ref());
            check_compile_fail_output(&stderr, expect_error_msg);
            did_something = true;
        }

        if !did_something {
            panic!("Test had nothing to do!");
        }
    }
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

macro_rules! question_kleene_to_option {
    ( $thing:expr ) => { Some($thing) };
    ( ) => { None };
}
