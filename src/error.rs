use crate::pos::{FileId};

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

// =============================================================================

/// An accumulator for errors that provides a straightforward way of converting to
/// a `Result<T, CompileError>` based on whether any errors have occurred.
#[derive(Debug, Clone)]
pub struct ErrorStore<E = ErrorReported> {
    errors: Option<E>,
}

// FIXME temporary trait while we get rid of CompileError
pub trait ErrorMerge {
    fn err_merge_append(&mut self, new_error: Self);
}

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
#[cfg(nope)]
fn test_collect_with_recovery() {
    let scope = crate::Scope::new();
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

// =============================================================================

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

// =============================================================================

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
