use codespan_reporting as cs;

use crate::pos::Files;
use crate::error::CompileError;

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
    pub fn emit(&mut self, diag: CompileError) {
        diag.emit_to_writer(self.writer, self.files, self.config);
        ErrorOccurred
    }

    /// Emit a diagnostic and return an `Err` with an empty [`CompileError`].
    ///
    /// Use this as `return emitter.fail_with(d);` or `emitter.fail_with(d)?`.
    /// Its purpose is to help reduce defects where one forgets to return an `Err` variant
    /// after emitting a fatal error.  (for this to happen, one would now have to
    /// specifically call the less popular [`Self::emit`] method instead)
    pub fn fail_with<T>(&mut self, diag: CompileError) -> Result<T, CompileError> {
        self.emit(diag);
        Err(CompileError::new())
    }
}
