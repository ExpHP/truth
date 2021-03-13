use codespan_reporting as cs;

use crate::pos::Files;
use crate::error::{CompileError, ErrorOccurred};

pub struct DiagnosticEmitter<'a> {
    files: &'a Files,
    config: &'a cs::term::Config,
    writer: &'a mut (dyn cs::term::termcolor::WriteColor + 'a),
}

impl<'a> DiagnosticEmitter<'a> {
    pub fn new(config: &'a cs::term::Config, files: &'a Files, writer: &'a mut impl cs::term::termcolor::WriteColor) -> Self {
        DiagnosticEmitter { config, files, writer }
    }

    /// Emit a diagnostic.
    ///
    /// Returns [`ErrorOccurred`] in order to allow it to be used like `result.map_err(|e| emitter.emit(e))?`
    /// for converting Results of [`CompileError`] into [`ErrorOccurred`].
    pub fn emit(&mut self, diag: CompileError) -> ErrorOccurred {
        diag.emit_to_writer(self.writer, self.files, self.config);
        ErrorOccurred
    }

    /// Emit a diagnostic and return [`Err(ErrorOccurred)`][`ErrorOccurred`].
    ///
    /// This is for the common case where the current function cannot continue due to an error;
    /// simply write `return emitter.fail_with(d);`  (and when converting code that formerly used
    /// `CompileError`, you simply replace `Err` with `emitter.fail_with`)
    pub fn fail_with<T>(&mut self, diag: CompileError) -> Result<T, ErrorOccurred> {
        Err(self.emit(diag))
    }
}

pub type Never = std::convert::Infallible;
