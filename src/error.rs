use crate::pos::{FileId};

/// A dummy error type with no payload.
///
/// This type is returned by [`RootEmitter::emit`] for potential use as an error type.
/// More generally, this could be used by any function that "emits" its errors through some form of side effect.
/// E.g. a function could call a callback, or a private method may push an item onto a `Vec` field.
///
/// This type very deliberately does not implement [`std::error::Error`] or [`std::fmt::Display`].
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[must_use = "When reporting an error, you usually also want to return Err.  Call `.ignore()` to explicitly ignore."]
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

// FIXME: If this looks overengineered, it's because it is.
//        It is naught but a ghastly remnant of some ErrorStore type that used to exist.
/// An accumulator for errors that provides a straightforward way of converting to
/// a `Result<T, ErrorReported>` based on whether any errors have occurred.
#[derive(Debug, Clone, Default)]
pub struct ErrorFlag {
    errors: Option<ErrorReported>,
}

impl ErrorFlag {
    /// Create an [`ErrorFlag`] in the default, 'success' state.
    pub fn new() -> Self { Default::default() }

    /// Force this [`ErrorFlag`] into the error state.
    pub fn set(&mut self, e: ErrorReported) {
        self.errors = Some(e);
    }

    /// If the given flag is in an error state, make this one also an error.
    pub fn update(&mut self, other: ErrorFlag) {
        self.errors = self.errors.or(other.errors);
    }

    /// Become an `Ok` if empty, and an `Err` otherwise.
    pub fn into_result<T>(self, value: T) -> Result<T, ErrorReported> {
        match self.errors {
            None => Ok(value),
            Some(error) => Err(error),
        }
    }
    pub fn into_result_with<T>(self, value: impl FnOnce() -> T) -> Result<T, ErrorReported> {
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

    /// Collect an iterator, continuing after failure in order to gather more errors.
    ///
    /// If at least one of the items is `Err(_)`, it returns an `Err(_)`.
    /// Otherwise, it returns `Ok(_)`.
    fn collect_with_recovery<B: FromIterator<Self::OkItem>>(self) -> Result<B, ErrorReported>;
}

impl<Ts, T> GatherErrorIteratorExt for Ts
where
    Ts: Iterator<Item=Result<T, ErrorReported>>,
{
    type OkItem = T;

    fn collect_with_recovery<B: FromIterator<T>>(self) -> Result<B, ErrorReported> {
        let mut errors = ErrorFlag::new();
        let out = self.filter_map(|r| match r {
            Ok(x) => Some(x),
            Err(e) => {
                errors.set(e);
                None
            },
        }).collect();

        errors.into_result(out)
    }
}

#[test]
fn test_collect_with_recovery() {
    let mut scope = crate::Builder::new().capture_diagnostics(true).build();
    let truth = scope.truth();

    // straightforward usage
    let result = (0..10).map(|x| match x % 2 {
        0 => Ok(x),
        1 => Err(truth.emit(error!(message("odd number: {}", x)))),
        _ => unreachable!(),
    }).collect_with_recovery::<Vec<_>>();
    assert!(result.is_err());
    assert_eq!(truth.get_captured_diagnostics().unwrap().matches("odd number").count(), 5);

    // -------------------------------------

    let mut scope = crate::Builder::new().capture_diagnostics(true).build();
    let truth = scope.truth();

    // collecting into () for side-effects
    let mut vec = vec![];
    let result = (0..10).map(|x| match x % 2 {
        0 => {
            vec.push(x);
            Ok(())
        },
        1 => Err(truth.emit(error!(message("odd number: {}", x)))),
        _ => unreachable!(),
    }).collect_with_recovery::<()>();
    assert!(result.is_err());
    assert_eq!(vec, vec![0, 2, 4, 6, 8]);
    assert_eq!(truth.get_captured_diagnostics().unwrap().matches("odd number").count(), 5);
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
