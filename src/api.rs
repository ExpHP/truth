use std::path::Path;

use crate::ast;
use crate::game::Game;
use crate::diagnostic::{RootEmitter, IntoDiagnostics};
use crate::error::ErrorReported;
use crate::context::{CompilerContext, Scope};
use crate::passes::DecompileKind;

/// Front-end API of `truth`, for direct use by `truth`'s various entry point functions, as well
/// as by unit tests.
///
/// To construct one, see [`Builder`].
///
/// The main purpose is to reduce the number of types that code outside of the crate needs to know about
/// or import.  To this end, its methods cover a wide variety of uses.
pub struct Truth<'ctx> {
    ctx: CompilerContext<'ctx>,
}

/// Builder for constructing [`Truth`].
pub struct Builder {
    capture_diagnostics: bool,
}

impl Default for Builder {
    fn default() -> Self { Self::new() }
}

impl Builder {
    pub fn new() -> Self {
        Builder {
            capture_diagnostics: false,
        }
    }

    /// Begin constructing the compiler using the settings stored on this [`Builder`].
    ///
    /// To finish constructing it, store the result in a local variable and call [`Scope::truth`].
    pub fn build(&self) -> Scope {
        let emitter = match self.capture_diagnostics {
            true => RootEmitter::new_captured(),
            false => RootEmitter::new_stderr(),
        };
        Scope::new(emitter)
    }

    pub fn capture_diagnostics(&mut self, capture: bool) -> &mut Self {
        self.capture_diagnostics = capture; self
    }
}

impl Scope {
    /// Create an instance of the compiler backed by this [`Scope`].
    pub fn truth(&mut self) -> Truth<'_> {
        Truth { ctx: CompilerContext::new(self) }
    }
}

// =============================================================================

/// # Special
impl Truth<'_> {
    /// **Note:** Requires having called [`Builder::capture_diagnostics`].
    pub fn get_captured_diagnostics(&self) -> Option<String> {
        self.ctx.emitter.get_captured_diagnostics()
    }
}

/// # Reading text files
impl Truth<'_> {
    pub fn apply_mapfile_str(&mut self, text: &str) -> Result<(), ErrorReported> {
        self.apply_mapfile(&crate::Eclmap::parse(text, &self.ctx.emitter)?)
    }

    pub fn apply_mapfile(&mut self, mapfile: &crate::Eclmap) -> Result<(), ErrorReported> {
        self.ctx.extend_from_eclmap(None, &mapfile)
    }

    pub fn read_mapfile_and_record(&mut self, filepath: &Path, game: Option<Game>) -> Result<(), ErrorReported> {
        let eclmap = crate::Eclmap::load(filepath, game, &self.ctx.emitter)?;
        self.ctx.extend_from_eclmap(Some(filepath), &eclmap)
    }

    pub fn read_script(&mut self, path: &Path) -> Result<ast::Script, ErrorReported> {
        let bytes = self.fs().read(path)?;
        self.parse(&path.to_string_lossy(), &bytes).map(|x| x.value)
    }

    /// Parse a piece of text into any parse-able AST node.
    ///
    /// The name does not need to be a valid path or even unique; for instance, it is common to use
    /// the name `"<input>"` for source text not associated with any file.
    pub fn parse<A: crate::parse::Parse>(&mut self, display_name: &str, text: &[u8]) -> Result<crate::pos::Sp<A>, ErrorReported> {
        let (file_id, source_str) = self.ctx.emitter.files.add(display_name, text).map_err(|e| self.emit(e))?;
        let mut state = crate::parse::State::new();

        A::parse_stream(&mut state, crate::parse::lexer::Lexer::new(file_id, &source_str[..]))
            .map_err(|e| self.emit(e))
    }
}

/// # Common behavior of pragmas
impl Truth<'_> {
    /// Loads mapfiles from a parsed script.
    pub fn load_mapfiles_from_pragmas(&mut self, game: Game, script: &ast::Script) -> Result<(), ErrorReported> {
        for path_literal in &script.mapfiles {
            let path: &Path = path_literal.string.as_ref();

            let eclmap = crate::Eclmap::load(&path, Some(game), &self.ctx.emitter)?;
            self.ctx.extend_from_eclmap(Some(path), &eclmap)?;
        }
        Ok(())
    }

    pub fn expect_no_image_sources(&self, ast: &ast::Script) -> Result<(), ErrorReported> {
        if let Some(path) = ast.image_sources.get(0) {
            Err(self.emit(error!(
                message("unexpected image_source"),
                primary(path.span, "image_source not valid in this format"),
            )))
        } else { Ok(()) }
    }
}

/// # Compilation and decompilation
impl Truth<'_> {
    pub fn compile_anm(&mut self, game: Game, ast: &ast::Script) -> Result<crate::AnmFile, ErrorReported> {
        crate::AnmFile::compile_from_ast(game, ast, &mut self.ctx)
    }
    pub fn compile_msg(&mut self, game: Game, ast: &ast::Script) -> Result<crate::MsgFile, ErrorReported> {
        crate::MsgFile::compile_from_ast(game, ast, &mut self.ctx)
    }
    pub fn compile_std(&mut self, game: Game, ast: &ast::Script) -> Result<crate::StdFile, ErrorReported> {
        crate::StdFile::compile_from_ast(game, ast, &mut self.ctx)
    }

    pub fn decompile_anm(&mut self, game: Game, middle: &crate::AnmFile, decompile_kind: DecompileKind) -> Result<ast::Script, ErrorReported> {
        crate::AnmFile::decompile_to_ast(middle, game, &mut self.ctx, decompile_kind)
    }
    pub fn decompile_msg(&mut self, game: Game, middle: &crate::MsgFile, decompile_kind: DecompileKind) -> Result<ast::Script, ErrorReported> {
        crate::MsgFile::decompile_to_ast(middle, game, &mut self.ctx, decompile_kind)
    }
    pub fn decompile_std(&mut self, game: Game, middle: &crate::StdFile, decompile_kind: DecompileKind) -> Result<ast::Script, ErrorReported> {
        crate::StdFile::decompile_to_ast(middle, game, &mut self.ctx, decompile_kind)
    }
}

/// # Binary file IO
impl<'ctx> Truth<'ctx> {
    pub fn read_anm(&mut self, game: Game, path: &Path, with_images: bool) -> Result<crate::AnmFile, ErrorReported> {
        match with_images {
            true => {
                let mut reader = self.fs().open_read(path)?;
                crate::AnmFile::read_from_stream(&mut reader, game, with_images)
            },
            false => {
                // Here we don't read the whole thing because seeking can skip costly reads of megabytes of image data.
                //
                // Seeking drops the buffer though, so use a tiny buffer.
                let buffer_size = 64;
                let mut reader = self.fs().open(path)?
                    .map_reader(|r| std::io::BufReader::with_capacity(buffer_size, r));
                crate::AnmFile::read_from_stream(&mut reader, game, with_images)
            },
        }
    }
    pub fn read_msg(&mut self, game: Game, path: &Path) -> Result<crate::MsgFile, ErrorReported> {
        crate::MsgFile::read_from_stream(&mut self.fs().open_read(path)?, game)
    }
    pub fn read_std(&mut self, game: Game, path: &Path) -> Result<crate::StdFile, ErrorReported> {
        crate::StdFile::read_from_stream(&mut self.fs().open_read(path)?, game)
    }

    pub fn write_anm(&mut self, game: Game, outpath: &Path, middle: &crate::AnmFile) -> Result<(), ErrorReported> {
        crate::AnmFile::write_to_stream(middle, &mut self.fs().create_buffered(outpath)?, game)
    }
    pub fn write_msg(&mut self, game: Game, outpath: &Path, middle: &crate::MsgFile) -> Result<(), ErrorReported> {
        crate::MsgFile::write_to_stream(middle, &mut self.fs().create_buffered(outpath)?, game)
    }
    pub fn write_std(&mut self, game: Game, outpath: &Path, middle: &crate::StdFile) -> Result<(), ErrorReported> {
        crate::StdFile::write_to_stream(middle, &mut self.fs().create_buffered(outpath)?, game)
    }

    /// Returns an object with filesystem-related helper methods.
    pub fn fs(&self) -> crate::Fs<'ctx> { crate::Fs::new(self.ctx.emitter) }
}

/// # Diagnostics
impl Truth<'_> {
    pub fn emit(&self, e: impl IntoDiagnostics) -> ErrorReported {
        self.ctx.emitter.emit(e)
    }
}

/// # Functions for use by tests
///
/// Sometimes tests want finer control over what's happening than any API we're willing to commit to yet.
impl<'ctx> Truth<'ctx> {
    #[doc(hidden)]
    pub fn ctx(&mut self) -> &mut CompilerContext<'ctx> { &mut self.ctx }

    #[doc(hidden)]
    pub fn emitter(&self) -> impl crate::diagnostic::Emitter + 'ctx { self.ctx.emitter }
}
