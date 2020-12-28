use crate::pos::{FileId, Files};

pub type Diagnostic = ::codespan_reporting::diagnostic::Diagnostic<FileId>;
pub type Label = ::codespan_reporting::diagnostic::Label<FileId>;

/// An error type that is intended to be pretty-printed through [`codespan_reporting`].
///
/// A `CompileError` may contain multiple errors.  It may even contain no errors!  This should
/// not happen when calling a function that returns a ``Result<T, CompileError>`, and is mainly
/// for use in code that attempts to gather errors from many sources (typically ending with a
/// call to [`CompileError::into_result`]).
#[derive(thiserror::Error, Debug)]
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

    /// Drain all errors from this object and write them to the standard error stream.
    ///
    /// In order to render spans correctly, the [`Files`] instance used to parse AST
    /// nodes is required.
    pub fn emit(&mut self, files: &Files) -> Result<(), codespan_reporting::files::Error> {
        use codespan_reporting::term::{self, termcolor as tc};

        let writer = tc::StandardStream::stderr(tc::ColorChoice::Always);
        let config = {
            let mut config = term::Config::default();
            // Make output closer to rustc. Fewer colors overall, looks better.
            config.styles.primary_label_error.set_intense(true);
            config.styles.secondary_label.set_intense(true);
            config.styles.line_number.set_intense(true);
            config.styles.source_border.set_intense(true);
            config
        };
        for e in self.diagnostics.drain(..) {
            term::emit(&mut writer.lock(), &config, files, &e).unwrap();
        }
        Ok(())
    }
}

macro_rules! error {
    (
        $(code=$code:literal,)? message($($message:tt)+)
        $(, primary( $primary_span:expr, $($primary_msg:tt)+ ) )*
        $(, secondary( $secondary_span:expr, $($secondary_msg:tt)+ ) )*
        $(, note( $($note_msg:tt)+ ) )*
        $(,)?
    ) => {{
        #[allow(unused)]
        use crate::error::{CompileError, Diagnostic, Label};
        #[allow(unused)]
        use crate::pos::HasSpan;

        CompileError { diagnostics: vec![
            Diagnostic::error()
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
