
use std::fmt;
use std::cell::RefCell;
use std::path::Path;

use codespan_reporting as cs;
use cs::term::termcolor as tc;

use crate::error::ErrorReported;
use crate::io::nice_display_path;
use crate::pos::{Files, FileId, HasSpan};

type CsDiagnostic = cs::diagnostic::Diagnostic<FileId>;
type CsLabel = cs::diagnostic::Label<FileId>;

/// Builder pattern for a single diagnostic message (warning or error).
#[derive(Debug, Clone)]
#[must_use = "A Diagnostic must be emitted or it will not be seen!"]
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

    /// Prepend a string to the message.  This is used to provide location info on diagnostic messages
    /// that do not have spans.  (e.g. they come from decompiled binary data)
    fn prefix_existing_message(&mut self, prefix: impl fmt::Display) -> &mut Self {
        let message = std::mem::replace(&mut self.imp.message, String::new());
        self.imp.message = format!("{}{}", prefix, message);
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
    pub files: Files,
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
    fn from_writer<W: WriteError + 'static>(writer: W) -> Self {
        DiagnosticEmitter {
            files: Files::new(),
            config: default_term_config(),
            writer: Box::new(RefCell::new(writer)),
        }
    }

    /// Create a [`DiagnosticEmitter`] that writes diagnostics to the standard error stream.
    pub fn new_stderr() -> Self {
        if std::env::var("_TRUTH_DEBUG__TEST").ok().as_deref() == Some("1") {
            Self::from_writer(EprintErrorWriter)
        } else {
            // contrary to what you might expect, ColorChoice::Auto does not check isatty
            let color = match atty::is(atty::Stream::Stderr) {
                true => tc::ColorChoice::Auto,
                false => tc::ColorChoice::Never,
            };
            Self::from_writer(tc::StandardStream::stderr(color))
        }
    }

    /// Create a [`DiagnosticEmitter`] that captures diagnostic output which can be recovered
    /// by calling [`Self::get_captured_diagnostics`].
    pub fn new_captured() -> Self {
        Self::from_writer(CapturingErrorWriter::new())
    }

    pub fn emit(&self, errors: impl IntoDiagnostics) -> ErrorReported {
        // NOTE: we don't take an iterator because the iterator could call `.emit()` and lead to a runtime borrow conflict.
        for diag in errors.into_diagnostics() {
            self.writer.borrow_mut().write_error(&diag, &self.config, &self.files);
        }
        ErrorReported
    }

    /// Obtain captured diagnostics written to stderr, provided that this [`CompilerContext`]
    /// was constructed using [`Self::new_captured`]. (otherwise, returns `None`)
    pub fn get_captured_diagnostics(&self) -> Option<String> {
        self.writer.borrow().get_captured_output()
    }
}

pub trait WriteError {
    fn write_error(&mut self, diagnostic: &Diagnostic, config: &cs::term::Config, files: &Files);
    /// If this is a capturing writer, gives a string of all diagnostics written thus far.
    fn get_captured_output(&self) -> Option<String> { None }
}

impl<T: tc::WriteColor> WriteError for T {
    fn write_error(&mut self, diagnostic: &Diagnostic, config: &cs::term::Config, files: &Files) {
        cs::term::emit(self, config, files, &diagnostic.imp)
            .unwrap_or_else(|fmt_err| {
                panic!("Internal compiler error while formatting error:\n{:#?}\ncould not format error because: {}", diagnostic.imp, fmt_err)
            });
    }
}

/// [`WriteError`] impl used when diagnostic capturing is enabled during the construction of [`crate::Truth`].
///
/// This is used by unit tests when they want to inspect the diagnostic output.
struct CapturingErrorWriter { writer: tc::NoColor<Vec<u8>> }
impl CapturingErrorWriter {
    fn new() -> Self { CapturingErrorWriter { writer: tc::NoColor::new(vec![]) } }
}
impl WriteError for CapturingErrorWriter {
    fn write_error(&mut self, diagnostic: &Diagnostic, config: &cs::term::Config, files: &Files) {
        self.writer.write_error(diagnostic, config, files);
    }
    fn get_captured_output(&self) -> Option<String> { Some(String::from_utf8_lossy(&self.writer.get_ref()).into_owned()) }
}

/// [`WriteError`] impl that uses `eprint!` in order to behave as a test-harness-aware form of STDERR.
///
/// This serves a different purpose from [`CapturingErrorWriter`], and neither makes the other obsolete.
/// This one mostly helps with tests where `truth` is expected to succeed; these typically do NOT enable
/// diagnostic capturing, as it would be impossible to print these diagnostics at every possible place
/// where the test could panic.
struct EprintErrorWriter;
impl WriteError for EprintErrorWriter {
    fn write_error(&mut self, diagnostic: &Diagnostic, config: &cs::term::Config, files: &Files) {
        let mut writer = CapturingErrorWriter::new();
        writer.write_error(diagnostic, config, files);
        // the rust test harness only captures eprint!, not general writes to std::io::stderr
        eprint!("{}", writer.get_captured_output().expect("is CapturingErrorWriter"));
    }
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

pub trait IntoDiagnostics {
    fn into_diagnostics(self) -> Vec<Diagnostic>;
}

impl IntoDiagnostics for Diagnostic {
    fn into_diagnostics(self) -> Vec<Diagnostic> { vec![self] }
}

impl IntoDiagnostics for Vec<Diagnostic> {
    fn into_diagnostics(self) -> Vec<Diagnostic> { self }
}

// =============================================================================

pub use unspanned::UnspannedEmitter;
pub mod unspanned {
    use super::*;
    use std::fmt;

    pub trait UnspannedEmitter: fmt::Display {
        fn _emitter(&self) -> &DiagnosticEmitter;

        fn chain_with<'a, T, Label, Callback>(&'a self, label: Label, cb: Callback) -> T
        where
            Self: Sized,
            Label: Fn(&mut fmt::Formatter) -> fmt::Result + 'a,
            Callback: FnOnce(&'_ NodeWith<&'a Self, Label>) -> T,
        { cb(&NodeWith { parent: self, label }) }

        fn chain<'a, T, Label, Callback>(&'a self, label: Label, cb: Callback) -> T
        where
            Self: Sized,
            Label: fmt::Display + 'a,
            Callback: FnOnce(&'_ Node<&'a Self, Label>) -> T,
        { cb(&Node { parent: self, label }) }

        fn emit(&self, diagnostics: impl IntoDiagnostics) -> ErrorReported
        where
            Self: Sized,
        {
            diagnostics.into_diagnostics().into_iter().for_each(|d| self.emit_one(d).ignore());
            ErrorReported
        }

        fn emit_one(&self, mut diagnostic: Diagnostic) -> ErrorReported {
            diagnostic.prefix_existing_message(self);
            self._emitter().emit(diagnostic)
        }
    }

    impl UnspannedEmitter for Root<'_> {
        fn _emitter(&self) -> &DiagnosticEmitter { &self.0 }
    }

    impl fmt::Display for Root<'_> {
        fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result { Ok(()) }
    }

    impl<Parent, Label> UnspannedEmitter for Node<Parent, Label>
    where
        Parent: UnspannedEmitter,
        Label: fmt::Display,
    {
        fn _emitter(&self) -> &DiagnosticEmitter { self.parent._emitter() }
    }

    impl<Parent, LabelFn> UnspannedEmitter for NodeWith<Parent, LabelFn>
    where
        Parent: UnspannedEmitter,
        LabelFn: Fn(&mut fmt::Formatter) -> fmt::Result,
    {
        fn _emitter(&self) -> &DiagnosticEmitter { self.parent._emitter() }
    }

    pub type WhileReading<'a> = Rooted<'a, String>;
    pub fn while_reading(filename: impl AsRef<Path>, diagnostics: &DiagnosticEmitter) -> WhileReading<'_> {
        make_root(format!("{}", nice_display_path(filename)), diagnostics)
    }

    pub type WhileWriting<'a> = Rooted<'a, String>;
    pub fn while_writing(filename: impl AsRef<Path>, diagnostics: &DiagnosticEmitter) -> WhileWriting<'_> {
        make_root(format!("while writing {}", nice_display_path(filename)), diagnostics)
    }

    pub type WhileDecompiling<'a> = Rooted<'a, String>;
    pub fn while_decompiling<'a>(filename: Option<&str>, diagnostics: &'a DiagnosticEmitter) -> WhileDecompiling<'a> {
        make_root(match filename {
            Some(filename) => format!("{}", nice_display_path(filename)),
            None => format!("while decompiling"),
        }, diagnostics)
    }

    pub type Rooted<'a, T> = Node<Root<'a>, T>;
    pub fn make_root<T: fmt::Display>(label: T, diagnostics: &DiagnosticEmitter) -> Rooted<'_, T> {
        Node { parent: Root(diagnostics), label }
    }

    impl<T: UnspannedEmitter + ?Sized> UnspannedEmitter for &'_ T {
        fn _emitter(&self) -> &DiagnosticEmitter { (**self)._emitter() }
    }

    #[derive(Clone)] pub struct Root<'a>(pub &'a DiagnosticEmitter);
    #[derive(Clone)] pub struct Node<Parent, Label> {
        parent: Parent,
        label: Label,
    }
    #[derive(Clone)] pub struct NodeWith<Parent, LabelFn> {
        parent: Parent,
        label: LabelFn,
    }

    impl<Parent, Label> fmt::Display for Node<Parent, Label>
    where
        Parent: fmt::Display,
        Label: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            fmt::Display::fmt(&self.parent, f)?;
            fmt::Display::fmt(&self.label, f)?;
            fmt::Display::fmt(": ", f)?;
            Ok(())
        }
    }

    impl<Parent, Label> fmt::Display for NodeWith<Parent, Label>
    where
        Parent: fmt::Display,
        Label: Fn(&mut fmt::Formatter) -> fmt::Result,
    {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            fmt::Display::fmt(&self.parent, f)?;
            (self.label)(f)?;
            fmt::Display::fmt(": ", f)?;
            Ok(())
        }
    }

    #[test]
    fn test() {
        let diagnostics = DiagnosticEmitter::new_captured();

        // here's how we'd typically write a function signature
        fn func(emitter: &impl UnspannedEmitter) {
            let x = 3;
            emitter.chain_with(|f| write!(f, "thing {}", x), |emitter| {
                emitter.chain("while eating a sub", |emitter| {
                    emitter.emit(warning!("blah {}", 20)).ignore();
                })
            })
        }

        let emitter = unspanned::while_reading("a.txt", &diagnostics);
        func(&emitter);

        let stderr = diagnostics.get_captured_diagnostics().unwrap();
        assert!(stderr.contains("a.txt: thing 3: while eating a sub: blah 20"));
        assert_snapshot!(stderr);
    }
}
