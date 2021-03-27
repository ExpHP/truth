
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

/// A single diagnostic message (warning or error).
#[derive(Debug, Clone)]
#[must_use = "A Diagnostic must be emitted or it will not be seen!"]
pub struct Diagnostic {
    imp: CsDiagnostic,
    unspanned_prefix: String,
}

impl Diagnostic {
    /// Construct with error severity.  Generally you use the [`error!`] macro instead.
    pub fn error() -> Self { Diagnostic { imp: CsDiagnostic::error(), unspanned_prefix: String::new() } }
    /// Construct with warning severity.  Generally you use the [`warning!`] macro instead.
    pub fn warning() -> Self { Diagnostic { imp: CsDiagnostic::warning(), unspanned_prefix: String::new() } }

    pub fn code(&mut self, code: &'static str) -> &mut Self {
        self.imp.code = Some(code.into());
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

/// Type that decides where diagnostic messages get written, and that stores the metadata necessary to render them.
pub struct RootEmitter {
    pub files: Files,
    config: cs::term::Config,
    writer: Box<RefCell<dyn WriteError>>,
}

impl fmt::Debug for RootEmitter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("RootEmitter")
            .field("files", &self.files)
            .field("config", &self.config)
            .field("writer", &(..))
            .finish()
    }
}

impl RootEmitter {
    fn from_writer<W: WriteError + 'static>(writer: W) -> Self {
        RootEmitter {
            files: Files::new(),
            config: default_term_config(),
            writer: Box::new(RefCell::new(writer)),
        }
    }

    /// Create a [`RootEmitter`] that writes diagnostics to the standard error stream.
    pub fn new_stderr() -> Self {
        if crate::env::is_test_mode() {
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

    /// Create a [`RootEmitter`] that captures diagnostic output which can be recovered
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

    /// Obtain captured diagnostics written to stderr, provided that this [`RootEmitter`]
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
        let mut imp = diagnostic.imp.clone();

        let spans_visible = match config.display_style {
            cs::term::DisplayStyle::Rich => true,
            cs::term::DisplayStyle::Medium | cs::term::DisplayStyle::Short => false,
        };
        if imp.labels.is_empty() || !spans_visible {
            imp.message = format!("{}{}", diagnostic.unspanned_prefix, imp.message);
        }

        cs::term::emit(self, config, files, &imp)
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

/// Trait for emitting diagnostics.
///
/// The primary implementor of this is [`RootEmitter`], and in many cases (especially during compilation
/// of data parsed from text), using that type will suffice.
///
/// This trait largely exists to accommodate errors that may not include spans (e.g. during the reading
/// or decompilation of a binary file).  By calling a method like [`Self::chain`], you can allow these
/// span-less diagnostics to have a series of prefixes added to them, like `"'files/abc.ecl': in script 3: "`.
///
/// If you have a `&dyn Emitter`, `Sized` bounds will prevent you from calling most methods,
/// but you can resolve this by calling [`<dyn Emitter>::as_sized`].
pub trait Emitter {
    fn _root_emitter(&self) -> &RootEmitter;

    /// A prefix added by this emitter to the `message` field of any diagnostics that do not contain spans.
    fn _unspanned_prefix(&self) -> String;

    /// Append an additional prefix for diagnostics that lack spans.
    ///
    /// Rather than returning the new emitter, it is passed into a callback.  This lets you shadow the original
    /// emitter, and then easily return back to using the old one once you leave the callback.
    fn chain<'a, T, Label, Callback>(&'a self, label: Label, cb: Callback) -> T
    where
        Self: Sized,
        Label: fmt::Display + 'a,
        Callback: FnOnce(&'_ Node<&'a Self, Label>) -> T,
    { cb(&self.get_chained(label)) }

    /// Like [`Emitter::chain`], but takes a format function.
    ///
    /// This should be far closer to zero cost than using [`Emitter::chain`] with `format!` or `format_args!`
    /// (and thus more suitable for tight loops), but these haven't been benchmarked.
    fn chain_with<'a, T, Label, Callback>(&'a self, label: Label, cb: Callback) -> T
    where
        Self: Sized,
        Label: Fn(&mut fmt::Formatter) -> fmt::Result + 'a,
        Callback: FnOnce(&'_ Node<&'a Self, DisplayFn<Label>>) -> T,
    { cb(&Node { parent: self, label: DisplayFn { func: label } }) }

    /// Form of [`Self::chain`] that returns the new emitter instead of taking a callback.
    /// Less idiomatic, but sometimes necessary.
    fn get_chained<'a, Label>(&'a self, label: Label) -> Node<&'a Self, Label>
    where
        Self: Sized,
        Label: fmt::Display + 'a,
    { Node { parent: self, label } }

    /// Emit any number of diagnostic messages.
    fn emit(&self, diagnostics: impl IntoDiagnostics) -> ErrorReported
    where
        Self: Sized,
    {
        diagnostics.into_diagnostics().into_iter().for_each(|mut d| {
            d.unspanned_prefix = self._unspanned_prefix();
            self._root_emitter().emit(d).ignore();
        });
        ErrorReported
    }
}

impl<'b> dyn Emitter + 'b {
    /// Allows one to call methods on `&dyn Emitter` that require `Self: Sized`.
    /// (e.g. `emitter.as_sized().emit(...)`)
    ///
    /// (all this does is just borrow the sucker through auto-ref, but it beats writing
    /// `(&emitter).emit(...)`)
    pub fn as_sized<'a>(self: &'a &'b Self) -> &'a &'b Self { self }
}

impl Emitter for RootEmitter {
    fn _root_emitter(&self) -> &RootEmitter { self }
    fn _unspanned_prefix(&self) -> String { String::new() }
}

impl<Parent, Label> Emitter for Node<Parent, Label>
where
    Parent: Emitter,
    Label: fmt::Display,
{
    fn _root_emitter(&self) -> &RootEmitter { self.parent._root_emitter() }

    fn _unspanned_prefix(&self) -> String {
        use std::fmt::Write;

        let mut prefix = self.parent._unspanned_prefix();
        write!(prefix, "{}: ", self.label).unwrap();
        prefix
    }
}

/// Adapts a [`fmt::Formatter`] function into an implementation of [`fmt::Display`].
pub struct DisplayFn<F> where F: Fn(&mut fmt::Formatter) -> fmt::Result { func: F }
impl<F> fmt::Display for DisplayFn<F> where F: Fn(&mut fmt::Formatter) -> fmt::Result {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { (self.func)(f) }
}

pub type WhileReading<'a> = Rooted<'a, String>;
pub type WhileWriting<'a> = Rooted<'a, String>;
pub type WhileDecompiling<'a> = Rooted<'a, String>;
impl RootEmitter {
    /// Get an [`Emitter`] with a standardized label for errors that come from files being read.
    pub fn while_reading(&self, filename: impl AsRef<Path>) -> WhileReading<'_> {
        self.get_chained(format!("{}", nice_display_path(filename)))
    }

    /// Get an [`Emitter`] with a standardized label for errors that occur during write operations.
    pub fn while_writing(&self, filename: impl AsRef<Path>) -> WhileWriting<'_> {
        self.get_chained(format!("while writing '{}'", nice_display_path(filename)))
    }

    /// Get an [`Emitter`] with a standardized label for errors that come from something being decompiled
    /// (which may or may not originate from a binary file).
    pub fn while_decompiling(&self, binary_filename: Option<&str>) -> WhileDecompiling<'_> {
        self.get_chained(match binary_filename {
            Some(binary_filename) => format!("{}", nice_display_path(binary_filename)),
            None => format!("while decompiling"),
        })
    }
}

pub type Rooted<'a, T> = Node<&'a RootEmitter, T>;

impl<T: Emitter + ?Sized> Emitter for &'_ T {
    fn _root_emitter(&self) -> &RootEmitter { (**self)._root_emitter() }
    fn _unspanned_prefix(&self) -> String { (**self)._unspanned_prefix() }
}

#[derive(Clone)] pub struct Node<Parent, Label> {
    parent: Parent,
    label: Label,
}

#[test]
fn test_unspanned() {
    let root_emitter = RootEmitter::new_captured();

    // here's how we'd typically write a function signature
    fn func(emitter: &impl Emitter) {
        let x = 3;
        emitter.chain_with(|f| write!(f, "thing {}", x), |emitter| {
            emitter.chain("while eating a sub", |emitter| {
                emitter.emit(warning!("blah {}", 20)).ignore();
            })
        })
    }

    let emitter = root_emitter.while_reading("a.txt");
    func(&emitter);

    let stderr = root_emitter.get_captured_diagnostics().unwrap();
    assert!(stderr.contains("a.txt: thing 3: while eating a sub: blah 20"), "{}", stderr);
    assert_snapshot!(stderr);
}
