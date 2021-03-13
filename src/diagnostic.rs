use std::sync::Mutex;
use std::fmt;

use codespan_reporting as cs;

use crate::pos::Files;
use crate::error::CompileError;

pub struct DiagnosticEmitter<'a> {
    files: &'a Files,
    config: &'a cs::term::Config,
    writer: Mutex<&'a mut (dyn cs::term::termcolor::WriteColor + 'a)>,
}

impl fmt::Debug for DiagnosticEmitter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "DiagnosticEmitter")
    }
}

impl<'a> DiagnosticEmitter<'a> {
    pub fn new(config: &'a cs::term::Config, files: &'a Files, writer: &'a mut impl cs::term::termcolor::WriteColor) -> Self {
        DiagnosticEmitter { config, files, writer: Mutex::new(writer) }
    }

    /// Emit a diagnostic.
    pub fn emit(&self, diag: CompileError) {
        // *technically speaking* this could deadlock if there was a really bad `Files` or `WriteColor` impl.
        match self.writer.lock() {
            Ok(writer) => diag.emit_to_writer(&mut *writer, self.files, self.config),
            Err(_poison) => { /* I think it's had enough. */ },
        }
    }

    /// Emit a diagnostic and return an `Err` with an empty [`CompileError`].
    ///
    /// Use this as `return emitter.fail_with(d);` or `emitter.fail_with(d)?`.
    /// Its purpose is to help reduce defects where one forgets to return an `Err` variant
    /// after emitting a fatal error.  (for this to happen, one would now have to
    /// specifically call the less popular [`Self::emit`] method instead)
    pub fn fail_with<T>(&self, diag: CompileError) -> Result<T, CompileError> {
        self.emit(diag);
        Err(CompileError::new())
    }
}
