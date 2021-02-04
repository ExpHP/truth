use crate::pos::{FileId, Span, HasSpan};

use codespan_reporting as cs;
type CsDiagnostic = cs::diagnostic::Diagnostic<FileId>;
type CsLabel = cs::diagnostic::Label<FileId>;

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
    diagnostics: Vec<Diagnostic>
}

impl CompileError {
    /// Zips two CompileError results, combining the errors if the both fail.
    pub fn join<A, B>(a: Result<A, CompileError>, b: Result<B, CompileError>) -> Result<(A, B), CompileError> {
        match (a, b) {
            (Ok(a), Ok(b)) => Ok((a, b)),
            (Err(e), Ok(_)) => Err(e),
            (Ok(_), Err(e)) => Err(e),
            (Err(mut a), Err(b)) => {
                a.append(b);
                Err(a)
            },
        }
    }
}

/// A single error in a [`CompileError`].  You can still add more labels to it.
///
/// It converts into [`CompileError`] using [`From`], so a `?` should suffice.
#[derive(Debug)]
pub struct Diagnostic {
    imp: CsDiagnostic,
}

impl Diagnostic {
    pub fn error() -> Self { Diagnostic { imp: CsDiagnostic::error() } }
    pub fn warning() -> Self { Diagnostic { imp: CsDiagnostic::warning() } }

    pub fn code(&mut self, code: String) -> &mut Self {
        self.imp.code = Some(code);
        self
    }

    pub fn message(&mut self, message: String) -> &mut Self {
        self.imp.message = message;
        self
    }

    /// Add a label of type 'primary'.
    pub fn primary(&mut self, span: impl HasSpan, message: String) -> &mut Self {
        let span = span.span();
        self.imp.labels.push(CsLabel::primary(span.file_id, span).with_message(message));
        self
    }

    /// Add a label of type 'secondary'.
    pub fn secondary(&mut self, span: impl HasSpan, message: String) -> &mut Self {
        let span = span.span();
        self.imp.labels.push(CsLabel::secondary(span.file_id, span).with_message(message));
        self
    }

    pub fn note(&mut self, message: String) -> &mut Self {
        self.imp.notes.push(message);
        self
    }
}

impl From<Diagnostic> for CompileError {
    fn from(d: Diagnostic) -> Self { CompileError { diagnostics: vec![d] } }
}

/// Error type used by parts of the codebase that don't have access to spans.
///
/// These parts of the codebase use `anyhow` to produce a single, fatal error message that may
/// include a chain of context.  This is always ultimately converted into a [`CompileError`]
/// shortly before being displayed to the user.
pub type SimpleError = anyhow::Error;

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
    pub fn into_result_with<T>(self, value: impl FnOnce() -> T) -> Result<T, CompileError> {
        match self.diagnostics.len() {
            0 => Ok(value()),
            _ => Err(self),
        }
    }
    pub fn error_count(&self) -> usize { self.diagnostics.len() }

    /// Drain all errors from this object and write them to the standard error stream.
    ///
    /// In order to render spans correctly, the [`crate::Files`] instance used to parse AST
    /// nodes is required.
    pub fn emit<'a>(&mut self, files: &'a impl cs::files::Files<'a, FileId=FileId>) -> Result<(), codespan_reporting::files::Error> {
        use cs::term::termcolor as tc;

        if std::env::var("_TRUTH_DEBUG__TEST").ok().as_deref() == Some("1") {
            let mut writer = tc::NoColor::new(vec![]);
            self.emit_to_writer(&mut writer, files)?;
            eprint!("{}", std::str::from_utf8(&writer.into_inner()).unwrap());
        } else {
            // typical
            let writer = tc::StandardStream::stderr(tc::ColorChoice::Auto);
            self.emit_to_writer(&mut writer.lock(), files)?;
        }
        Ok(())
    }

    fn emit_to_writer<'a>(
        &mut self,
        writer: &mut impl cs::term::termcolor::WriteColor,
        files: &'a impl cs::files::Files<'a, FileId=FileId>,
    ) -> Result<(), codespan_reporting::files::Error> {
        for e in self.diagnostics.drain(..) {
            cs::term::emit(writer, &*TERM_CONFIG, files, &e.imp).unwrap();
        }
        Ok(())
    }

    /// Render the errors to a text string with no color escapes.  Intended mainly for unit tests.
    pub fn to_string<'a>(&self, files: &'a impl cs::files::Files<'a, FileId=FileId>) -> Result<String, codespan_reporting::files::Error> {
        use codespan_reporting::term::{self, termcolor as tc};

        let mut writer = tc::NoColor::new(vec![]);
        for e in &self.diagnostics {
            term::emit(&mut writer, &*TERM_CONFIG, files, &e.imp).unwrap();
        }
        Ok(String::from_utf8(writer.into_inner()).expect("codespan crate wrote non-UTF8?!"))
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

// -------------------------

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
        let mut d = $crate::error::Diagnostic::$severity();
        d.message(format!( $($message)+ ));
        $( d.code($code); )?
        $( d.primary(&$primary_span, format!( $($primary_msg)+ )); )*
        $( d.secondary(&$secondary_span, format!( $($secondary_msg)+ )); )*
        $( d.note(format!( $($note_msg)+ )); )*
        $crate::error::CompileError::from(d)
    }};
    ( // shorthand for message only
        @ $severity:ident,
        $message_fmt:literal $(, $message_arg:expr)* $(,)?
    ) => { $crate::_diagnostic!{
        @ $severity,
        message($message_fmt $(, $message_arg)*),
    }};
}

/// Generates a [`CompileError`] of severity `error`.
///
/// If you want to modify the error after the macro call (by dynamically adding labels/notes),
/// try the [`Diagnostic`] builder API instead.
#[macro_export]
macro_rules! error {
    ($($arg:tt)+) => { $crate::_diagnostic!(@error, $($arg)+) };
}

/// Generates a [`CompileError`] of severity `warning`.
///
/// If you want to modify the error after the macro call (by dynamically adding labels/notes),
/// try the [`Diagnostic`] builder API instead.
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
        use lalrpop_util::ParseError::*;

        match e {
            User { error } => error.into(),
            UnrecognizedEOF { location, ref expected } => error!(
                message("unexpected EOF"),
                primary(Span::from_locs(location, location), "unexpected EOF"),
                note("{}", DisplayExpected(expected)),
            ),
            UnrecognizedToken { token: (start, token, end), ref expected } => error!(
                message("unexpected token `{}`", token),
                primary(Span::from_locs(start, end), "unexpected token"),
                note("{}", DisplayExpected(expected)),
            ),
            ExtraToken { token: (start, token, end) } => error!(
                message("unexpected extra token `{}`", token),
                primary(Span::from_locs(start, end), "extra token"),
            ),
            InvalidToken { .. } => unreachable!("we don't use lalrpop's lexer"),
        }
    }
}

struct DisplayExpected<'a>(&'a [String]);
impl std::fmt::Display for DisplayExpected<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // copied from lalrpop_util
        if !self.0.is_empty() {
            writeln!(f)?;
            for (i, e) in self.0.iter().enumerate() {
                let sep = match i {
                    0 => "Expected one of",
                    _ if i < self.0.len() - 1 => ",",
                    // Last expected message to be written
                    _ => " or",
                };
                write!(f, "{} {}", sep, e)?;
            }
        }
        Ok(())
    }
}

impl From<anyhow::Error> for CompileError {
    fn from(e: anyhow::Error) -> CompileError {
        error!(message("{:#}", e)).into()
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

impl From<crate::fmt::Error> for CompileError {
    fn from(e: crate::fmt::Error) -> CompileError {
        SimpleError::from(e).into()
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

impl<Ts, T, E> GatherErrorIteratorExt for Ts
where
    Ts: Iterator<Item=Result<T, E>>,
    E: Into<CompileError>,
{
    type OkItem = T;

    fn collect_with_recovery<B: std::iter::FromIterator<T>>(self) -> Result<B, CompileError> {
        let mut errors = CompileError::new_empty();
        let out = self.filter_map(|r| match r {
            Ok(x) => Some(x),
            Err(e) => { errors.append(e.into()); None }
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

// -------------------------

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

// -------------------------

/// Utility that makes it easier to apply `anyhow::Context` to all errors in a region of code.
///
/// Basically, the most straightforward way to have many error paths apply the same context is to
/// put them in an IIFE.  However, (a) IIFEs can be confusing to read, and (b) you'd typically be
/// forced to explicitly annotate the return type due to the nested usage of `?`.
///
/// Basically,
/// ```text
/// group_anyhow(|| {
///     ...
/// }).with_context(|| { ... })
/// ```
/// is nicer than
/// ```text
/// (|| -> Result<_, anyhow::Error> {
///     ...
/// })().with_context(|| { ... })
/// ```
pub(crate) fn group_anyhow<T>(
    func: impl FnOnce() -> Result<T, anyhow::Error>,
) -> Result<T, anyhow::Error> {
    func()
}
