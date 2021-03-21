use crate::pos::{FileId, Span};
use crate::diagnostic::Diagnostic;

use codespan_reporting as cs;

/// An error type that is intended to be pretty-printed through [`codespan_reporting`].
///
/// A [`CompileError`] may contain multiple errors.  It may even contain no errors!  This can
/// happen if errors were already emitted.  Even a [`CompileError`] with no errors should be
/// treated as a "failure".  (if you want to create an accumulator of errors where having no
/// errors is considered to be a success, see [`ErrorStore`]).
///
/// **Do not use this type to hold non-fatal diagnostics.**
/// Use [`Vec<Diagnostic>`][`Diagnostic`] instead.
///
/// There is no general recommendation regarding whether errors should be emitted immediately
/// using [`DiagnosticEmitter`], or if they should be accumulated using [`Self::join`] and
/// [`Self::append`] and returned en masse to the caller.  Usage of [`DiagnosticEmitter`] is a
/// *requirement* for non-fatal diagnostics (i.e. warnings) with spans; however, many pieces of code
/// in the compiler that don't need to generate warnings may prefer to return their errors, simply
/// because this allows for somewhat looser coupling.
///
/// [`DiagnosticEmitter`]: [`crate::context::diagnostic::DiagnosticEmitter`]
#[derive(thiserror::Error, Debug, Clone)]
#[must_use = "A CompileError must be emitted or it will not be seen!"]
// FIXME: We have to get rid of derive(Error) because now we use `impl Display` in places where it could be easy
//        to accidentally supply CompileError
#[error("a diagnostic wasn't formatted. This is a bug! The diagnostic was: {:?}", .diagnostics)]
pub struct CompileError {
    diagnostics: Vec<Diagnostic>,
}

/// A dummy error type with no payload.
///
/// This type is returned by [`DiagnosticEmitter::emit`] for potential use as an error type.
/// More generally, this could be used by any function that "emits" its errors through some form of side effect.
/// E.g. a function could call a callback, or a private method may push an item onto a `Vec` field.
///
/// This type very deliberately does not implement [`std::error::Error`] or [`std::fmt::Display`].
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[must_use = "When reporting an error, you usually also want to return Err.  Call `.ignore()` to explicitly ignore."]
// FIXME: temporary because something in formats/ was relying on this
#[derive(thiserror::Error)]
#[error("ErrorReported converted to a type-with-payload. This is a bug!")]
pub struct ErrorReported;

impl ErrorReported {
    /// Explicitly drop this [`ErrorReported`] value.
    ///
    /// This is like `let _ = ...` or `drop(...)`, but as a named method that helps clarify intent (and that would
    /// stop compiling by design if a refactoring changed the error to a different type that actually contained
    /// a payload).
    pub fn ignore(self) {}
}

impl CompileError {
    /// Zips two CompileError results, combining the errors if they both fail.
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

impl CompileError {
    /// Create an empty [`CompileError`].  Even an empty [`CompileError`] is still an error!
    pub fn new() -> CompileError {
        CompileError { diagnostics: vec![] }
    }

    pub fn append(&mut self, mut other: CompileError) {
        self.diagnostics.append(&mut other.diagnostics);
    }

    /// Drain all errors from this object and write them to the standard error stream.
    ///
    /// In order to render spans correctly, the [`crate::Files`] instance used to parse AST
    /// nodes is required.
    #[deprecated] // generate warnings to help us move things to DiagnosticEmitter
    pub fn emit<'a>(&mut self, _files: &'a impl cs::files::Files<'a, FileId=FileId>) {
        // use cs::term::termcolor as tc;
        //
        // if std::env::var("_TRUTH_DEBUG__TEST").ok().as_deref() == Some("1") {
        //     // use eprint! so that the test harness can capture it
        //     let mut writer = tc::NoColor::new(vec![]);
        //     self.emit_to_writer(&mut writer, files, &*TERM_CONFIG);
        //     eprint!("{}", std::str::from_utf8(&writer.into_inner()).unwrap());
        // } else {
        //     // typical
        //     let writer = tc::StandardStream::stderr(tc::ColorChoice::Auto);
        //     self.emit_to_writer(&mut writer.lock(), files, &*TERM_CONFIG);
        // }
        panic!()
    }

    /// Drain all errors from this object and write them to some output terminal.
    ///
    /// In order to render spans correctly, the [`crate::Files`] instance used to parse AST
    /// nodes is required.
    #[deprecated] // generate warnings to help us move things to DiagnosticEmitter
    pub fn emit_to_writer<'a>(
        self,
        _writer: &mut dyn cs::term::termcolor::WriteColor,
        _files: &'a impl cs::files::Files<'a, FileId=FileId>,
        _config: &cs::term::Config,
    ) {
        // for e in self.diagnostics.drain(..) {
        //     cs::term::emit(writer, config, files, &e.imp)
        //         .unwrap_or_else(|fmt_err| {
        //             panic!("Internal compiler error while formatting error:\n{:#?}\ncould not format error because: {}", e.imp, fmt_err)
        //         });
        // }
        panic!();
    }

    /// Emit errors that contain no labels.
    ///
    /// It is a bug to call this when there is any possibility that the errors have labels.
    /// It should only be used when reading e.g. binary files, which have no position info.
    #[deprecated] // generate warnings to help us move things to DiagnosticEmitter
    pub fn emit_nospans<'a>(&mut self) {
        // // because there are no labels, we know the methods of the Files will never be used,
        // // so we can use a dummy implementation.
        // let result = self.emit(&crate::error::PanicFiles);
        //
        // // The only possible error here is an IO Error.  This would suggest STDERR is not writable,
        // // which is hardly any reason to stop what we're doing, so just ignore all errors.
        // drop(result);
        panic!()
    }
}

/// Error type used by parts of the codebase that don't have access to spans.
///
/// These parts of the codebase use `anyhow` to produce a single, fatal error message that may
/// include a chain of context.  This is always ultimately converted into a [`CompileError`]
/// shortly before being displayed to the user.
pub type SimpleError = anyhow::Error;

// -------------------------

/// An accumulator for errors that provides a straightforward way of converting to
/// a `Result<T, CompileError>` based on whether any errors have occurred.
#[derive(Debug, Clone)]
pub struct ErrorStore<E = CompileError> {
    errors: Option<E>,
}

// FIXME temporary trait while we get rid of CompileError
pub trait ErrorMerge {
    fn err_merge_append(&mut self, new_error: Self);
}

impl ErrorMerge for CompileError { fn err_merge_append(&mut self, new: CompileError) { self.append(new) } }
impl ErrorMerge for ErrorReported { fn err_merge_append(&mut self, _: ErrorReported) {} }

impl<E: ErrorMerge> ErrorStore<E> {
    /// Create an [`ErrorStore`] in the default, 'success' state.
    pub fn new() -> Self { ErrorStore { errors: None } }

    /// Force this [`ErrorStore`] into the error state and add data from a new error.
    pub fn append(&mut self, new_error: E) {
        self.errors = match self.errors.take() {
            Some(mut errors) => {
                errors.err_merge_append(new_error);
                Some(errors)
            },
            None => Some(new_error),
        };
    }

    /// Become an `Ok` if empty, and an `Err` otherwise.
    pub fn into_result<T>(self, value: T) -> Result<T, E> {
        match self.errors {
            None => Ok(value),
            Some(error) => Err(error),
        }
    }
    pub fn into_result_with<T>(self, value: impl FnOnce() -> T) -> Result<T, E> {
        match self.errors {
            None => Ok(value()),
            Some(error) => Err(error),
        }
    }
}

// -------------------------

// needed by DiagnosticEmitter::emit
impl crate::diagnostic::IntoDiagnostics for crate::error::CompileError {
    fn into_diagnostics(self) -> Vec<Diagnostic> { self.diagnostics }
}

// -------------------------

impl From<Diagnostic> for CompileError {
    fn from(d: Diagnostic) -> Self { CompileError { diagnostics: vec![d] } }
}

impl From<Vec<Diagnostic>> for CompileError {
    fn from(diagnostics: Vec<Diagnostic>) -> Self { CompileError { diagnostics } }
}

impl From<ErrorReported> for CompileError {
    fn from(_: ErrorReported) -> Self { CompileError { diagnostics: vec![] } }
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
    type Err;

    /// Collect an iterator, continuing after failure in order to gather more errors.
    ///
    /// If at least one of the items is `Err(_)`, it returns an `Err(_)` that concatenates all
    /// of the errors in the stream.  Otherwise, it returns `Ok(_)`.
    fn collect_with_recovery<B: std::iter::FromIterator<Self::OkItem>>(self) -> Result<B, Self::Err>;
}

impl<Ts, T, E> GatherErrorIteratorExt for Ts
where
    Ts: Iterator<Item=Result<T, E>>,
    E: ErrorMerge,
{
    type OkItem = T;
    type Err = E;

    fn collect_with_recovery<B: std::iter::FromIterator<T>>(self) -> Result<B, E> {
        let mut errors = ErrorStore::new();
        let out = self.filter_map(|r| match r {
            Ok(x) => Some(x),
            Err(e) => {
                errors.append(e);
                None
            },
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
    assert_eq!(result.unwrap_err().diagnostics.len(), 5);

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
    assert_eq!(result.unwrap_err().diagnostics.len(), 5);
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
