use crate::pos::{FileId};

use codespan_reporting as cs;
pub type Diagnostic = cs::diagnostic::Diagnostic<FileId>;
pub type Label = cs::diagnostic::Label<FileId>;

/// An error type that is intended to be pretty-printed through [`codespan_reporting`].
///
/// A `CompileError` may contain multiple errors.  It may even contain no errors!  This should
/// not happen when calling a function that returns a ``Result<T, CompileError>`, and is mainly
/// for use in code that attempts to gather errors from many sources (typically ending with a
/// call to [`CompileError::into_result`]).
#[derive(thiserror::Error, Debug)]
#[must_use = "A CompileError must be emitted or it will not be seen!"]
#[error("a diagnostic wasn't formatted. This is a bug! The diagnostic was: {:?}", .diagnostics)]
pub struct CompileError {
    #[doc(hidden)]
    pub diagnostics: Vec<Diagnostic>
}

impl CompileError {
    pub fn new_empty() -> CompileError { CompileError { diagnostics: vec![] } }
    pub fn append(&mut self, mut other: CompileError) {
        self.diagnostics.append(&mut other.diagnostics);
    }
    /// Become an `Ok` if empty, and an `Err` otherwise.
    pub fn into_result<T>(self, value: T) -> Result<T, CompileError> {
        match self.diagnostics.len() {
            0 => Ok(value),
            _ => Err(self),
        }
    }
    pub fn error_count(&self) -> usize { self.diagnostics.len() }

    /// Drain all errors from this object and write them to the standard error stream.
    ///
    /// In order to render spans correctly, the [`Files`] instance used to parse AST
    /// nodes is required.
    pub fn emit<'a>(&mut self, files: &'a impl cs::files::Files<'a, FileId=FileId>) -> Result<(), codespan_reporting::files::Error> {
        use codespan_reporting::term::{self, termcolor as tc};

        let writer = tc::StandardStream::stderr(tc::ColorChoice::Always);
        for e in self.diagnostics.drain(..) {
            term::emit(&mut writer.lock(), &*TERM_CONFIG, files, &e).unwrap();
        }
        Ok(())
    }

    /// Emit errors that contain no labels.
    ///
    /// It is a bug to call this when there is any possibility that the errors have labels.
    /// It should only be used when reading e.g. binary files, which have no position info.
    pub fn emit_nospans<'a>(&mut self) {
        // because there are no labels, we know the methods of the Files will never be used,
        // so we can use a dummy implementation.
        let result = self.emit(&crate::error::PanicFiles);

        // The only possible error here is an IO Error.  This would suggest STDERR is not writable,
        // which is hardly any reason to stop what we're doing, so just ignore all errors.
        drop(result);
    }
}

lazy_static::lazy_static! {
    static ref TERM_CONFIG: codespan_reporting::term::Config = {
        let mut config = codespan_reporting::term::Config::default();
        // Make output closer to rustc. Fewer colors overall, looks better.
        config.styles.primary_label_error.set_intense(true);
        config.styles.secondary_label.set_intense(true);
        config.styles.line_number.set_intense(true);
        config.styles.source_border.set_intense(true);
        config
    };
}

#[macro_export]
macro_rules! _diagnostic {
    (
        @ $severity:ident,
        $(code=$code:literal,)? message($($message:tt)+)
        $(, primary( $primary_span:expr, $($primary_msg:tt)+ ) )*
        $(, secondary( $secondary_span:expr, $($secondary_msg:tt)+ ) )*
        $(, note( $($note_msg:tt)+ ) )*
        $(,)?
    ) => {{
        #[allow(unused)]
        use $crate::error::{CompileError, Diagnostic, Label};
        #[allow(unused)]
        use $crate::pos::HasSpan;

        CompileError { diagnostics: vec![
            Diagnostic::$severity()
                $( .with_code($code) )?
                .with_message(format!( $($message)+ ))
                .with_labels(vec![
                    $( match HasSpan::span(&$primary_span) {
                        span => Label::primary(span.file_id, span).with_message(format!( $($primary_msg)+ ))
                    } ,)*
                    $( match HasSpan::span(&$secondary_span) {
                        span => Label::secondary(span.file_id, span).with_message(format!( $($secondary_msg)+ ))
                    } ,)*
                ])
                .with_notes(vec![ $(format!( $($note_msg)+ ))* ]),
        ]}
    }};
    ( // shorthand for message only
        @ $severity:ident,
        $message_fmt:literal $(, $message_arg:expr)* $(,)?
    ) => { $crate::_diagnostic!{
        @ $severity,
        message($message_fmt $(, $message_arg)*),
    }};
}

/// Generates a `CompileError` of severity `error`.
#[macro_export]
macro_rules! error {
    ($($arg:tt)+) => { $crate::_diagnostic!(@error, $($arg)+) };
}

/// Generates a `CompileError` of severity `warning`.
#[macro_export]
macro_rules! warning {
    ($($arg:tt)+) => { $crate::_diagnostic!(@warning, $($arg)+) };
}

/// Generates and immediately emits a `CompileError` of severity `warning` that has no labels.
#[macro_export]
macro_rules! fast_warning {
    ($($fmt_arg:tt)+) => {{
        $crate::warning!(message($($fmt_arg)+)).emit_nospans()
    }};
}

impl<'a> From<crate::parse::Error<'a>> for CompileError {
    fn from(e: crate::parse::Error<'a>) -> CompileError {
        // FIXME We could certainly do better here by matching on the error, but we need FileId to
        //       make spans from the positions on the error type.
        //       This feature will be easier to add when we add error recovery to the parser,
        //       as we can get the FileId from the parser state then.
        error!(message("{}", e))
    }
}

impl From<anyhow::Error> for CompileError {
    fn from(e: anyhow::Error) -> CompileError {
        error!(message("{:#}", e))
    }
}

impl From<std::io::Error> for CompileError {
    #[track_caller]
    fn from(e: std::io::Error) -> CompileError {
        // obviously not ideal but it's better than sitting there with a vague "file not found"
        // and no backtrace
        panic!("{}", e)
    }
}

/// Trait for running an iterator and continuing after an `Err` to collect more errors.
pub trait GatherErrorIteratorExt {
    type OkItem;

    /// Collect an iterator, continuing after failure in order to gather more errors.
    ///
    /// If at least one of the items is `Err(_)`, it returns an `Err(_)` that concatenates all
    /// of the errors in the stream.  Otherwise, it returns `Ok(_)`.
    fn collect_with_recovery<B: std::iter::FromIterator<Self::OkItem>>(self) -> Result<B, CompileError>;
}

impl<Ts, T> GatherErrorIteratorExt for Ts
where
    Ts: Iterator<Item=Result<T, CompileError>>
{
    type OkItem = T;

    fn collect_with_recovery<B: std::iter::FromIterator<T>>(self) -> Result<B, CompileError> {
        let mut errors = CompileError::new_empty();
        let out = self.filter_map(|r| match r {
            Ok(x) => Some(x),
            Err(e) => { errors.append(e); None }
        }).collect();

        errors.into_result(out)
    }
}

#[test]
fn test_collect_with_recovery() {
    // straightforward usage
    let result = (0..10).map(|x| match x % 2 {
        0 => Ok(x),
        1 => Err(error!(message("odd number: {}", x))),
        _ => unreachable!(),
    }).collect_with_recovery::<Vec<_>>();
    assert_eq!(result.unwrap_err().error_count(), 5);

    // collecting into () for side-effects
    let mut vec = vec![];
    let result = (0..10).map(|x| match x % 2 {
        0 => {
            vec.push(x);
            Ok(())
        },
        1 => Err(error!(message("odd number: {}", x))),
        _ => unreachable!(),
    }).collect_with_recovery::<()>();
    assert_eq!(vec, vec![0, 2, 4, 6, 8]);
    assert_eq!(result.unwrap_err().error_count(), 5);
}

/// Implementation of [`codespan_reporting::files::Files`] where all methods panic.
#[doc(hidden)]
pub struct PanicFiles;

#[doc(hidden)]
pub type CsResult<T> = Result<T, codespan_reporting::files::Error>;

impl<'a> codespan_reporting::files::Files<'a> for PanicFiles {
    type FileId = FileId;
    type Name = &'static str;
    type Source = &'static str;

    fn name(&'a self, _: FileId) -> CsResult<Self::Name> { unreachable!("span in emit_nospans!") }
    fn source(&'a self, _: FileId) -> CsResult<Self::Source> { unreachable!("span in emit_nospans!") }
    fn line_index(&'a self, _: FileId, _: usize) -> CsResult<usize> { unreachable!("span in emit_nospans!") }
    fn line_range(&'a self, _: FileId, _: usize) -> CsResult<std::ops::Range<usize>> { unreachable!("span in emit_nospans!") }
}
