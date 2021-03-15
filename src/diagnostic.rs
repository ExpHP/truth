
use std::fmt;
use std::cell::RefCell;
use std::rc::Rc;
use std::any::Any;

use codespan_reporting as cs;
use cs::term::termcolor as tc;

use crate::pos::{Files, FileId, HasSpan};

type CsDiagnostic = cs::diagnostic::Diagnostic<FileId>;
type CsLabel = cs::diagnostic::Label<FileId>;

/// Builder pattern for a single diagnostic message (warning or error).
///
/// It converts into [`CompileError`] using [`From`], so a `?` should suffice.
#[derive(Debug, Clone)]
#[must_use = "A Diagnostic must be emitted or it will not be seen!"]
pub struct Diagnostic {
    imp: CsDiagnostic,
}

// FIXME: Should be #[must_use] but then we'd need to create our own newtype.
/// Type alias indicating diagnostics that are non-fatal.
///
/// Sometimes a function might return this if it doesn't have access to a [`DiagnosticEmitter`].
/// Please be sure to emit them!
pub type Warnings = Vec<Diagnostic>;

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

// =============================================================================

/// Type responsible for emitting diagnostics and storing the metadata necessary to render them.
pub struct DiagnosticEmitter {
    files: Files,
    config: cs::term::Config,
    writer: Box<RefCell<dyn WriteError>>,
}

impl fmt::Debug for DiagnosticEmitter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("DiagnosticEmitter")
            .field("files", &self.files)
            .field("config", &self.config)
            .field("writer", &(..))
            .finish()
    }
}

impl DiagnosticEmitter {
    fn from_writer<W: WriteError>(writer: W) -> Self {
        DiagnosticEmitter {
            files: Files::new(),
            config: default_term_config(),
            writer: Box::new(RefCell::new(writer)),
        }
    }

    /// Create a [`DiagnosticEmitter`] that writes diagnostics to the standard error stream.
    pub fn new_stderr() -> Rc<Self> {
        Rc::new(Self::from_writer(tc::StandardStream::stderr(tc::ColorChoice::Auto)))
    }

    /// Create a [`DiagnosticEmitter`] that captures diagnostic output which can be recovered
    /// by calling [`Self::get_captured_diagnostics`].
    pub fn new_captured() -> Rc<Self> {
        let writer: CapturedWriter = tc::NoColor::new(vec![]);
        Rc::new(Self::from_writer(writer))
    }

    pub fn emit(&self, errors: impl Into<Vec<Diagnostic>>) {
        // NOTE: we don't take an iterator because the iterator could call `.emit()` and lead to a runtime borrow conflict.
        for diag in errors.into() {
            let mut writer = self.writer.borrow_mut();
            cs::term::emit(writer.as_write_color(), &self.config, &self.files, &diag.imp)
                .unwrap_or_else(|fmt_err| {
                    panic!("Internal compiler error while formatting error:\n{:#?}\ncould not format error because: {}", diag.imp, fmt_err)
                });
        }
    }

    /// Obtain captured diagnostics written to stderr, provided that this [`CompilerContext`]
    /// was constructed using [`Self::new_captured`]. (otherwise, returns `None`)
    pub fn get_captured_diagnostics(&self) -> Option<String> {
        let writer = self.writer.borrow();
        let writer = writer.as_any().downcast_ref::<CapturedWriter>()?;

        Some(String::from_utf8_lossy(&writer.get_ref()).into_owned())
    }
}

pub trait WriteError: tc::WriteColor + Any {
    fn as_any(&self) -> &dyn Any;
    fn as_write_color(&mut self) -> &mut dyn tc::WriteColor;
}

impl<T: tc::WriteColor + Any> WriteError for T {
    fn as_any(&self) -> &dyn Any { self }
    fn as_write_color(&mut self) -> &mut dyn tc::WriteColor { self }
}

fn default_term_config() -> cs::term::Config {
    let mut config = cs::term::Config::default();
    // Make output closer to rustc. Fewer colors overall, looks better.
    config.styles.primary_label_error.set_intense(true);
    config.styles.secondary_label.set_intense(true);
    config.styles.line_number.set_intense(true);
    config.styles.source_border.set_intense(true);
    config
}

type CapturedWriter = tc::NoColor<Vec<u8>>;

impl From<Diagnostic> for Vec<Diagnostic> {
    fn from(d: Diagnostic) -> Vec<Diagnostic> { vec![d] }
}
