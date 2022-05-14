use std::path::Path;

use crate::ast;
use crate::pos::{Sp};
use crate::game::{Game, LanguageKey};
use crate::diagnostic::{RootEmitter, IntoDiagnostics};
use crate::error::ErrorReported;
use crate::context::{CompilerContext, Scope};
use crate::llir::DecompileOptions;

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
    // FIXME: These mapfile functions shouldn't have to take a game,
    //        but they do so that they can verify timeline arg0 presence...
    /// For unit tests.
    pub fn apply_mapfile_str(&mut self, text: &str, game: Game) -> Result<(), ErrorReported> {
        let (file_id, text_rc) = self.ctx.emitter.files.add("<input mapfile>", text.as_ref()).map_err(|e| self.emit(e))?;
        let source_str = crate::pos::SourceStr::from_full_source(file_id, &text_rc[..]);
        let seqmap = crate::parse::seqmap::SeqmapRaw::parse(source_str, &self.ctx.emitter)?;
        self.apply_mapfile(&crate::Mapfile::from_seqmap(seqmap, &self.ctx.emitter)?, game)
    }

    pub fn apply_mapfile(&mut self, mapfile: &crate::Mapfile, game: Game) -> Result<(), ErrorReported> {
        self.ctx.extend_from_mapfile(None, &mapfile, game)
    }

    pub fn load_mapfile(&mut self, filepath: &Path, game: Game) -> Result<(), ErrorReported> {
        let eclmap = crate::Mapfile::load(filepath, Some(game), &self.ctx.emitter, |path| {
            let bytes = self.fs().read(path)?;
            self.ctx.emitter.files.add(&path.to_string_lossy(), &bytes)
                .map_err(|e| self.ctx.emitter.emit(e))
                .map(|(file_id, str)| (file_id, str.to_string()))
        })?;
        self.ctx.extend_from_mapfile(Some(filepath), &eclmap, game)
    }

    pub fn read_script(&mut self, path: &Path) -> Result<ast::ScriptFile, ErrorReported> {
        let bytes = self.fs().read(path)?;
        self.parse(&path.to_string_lossy(), &bytes).map(|x| x.value)
    }

    /// Parse a piece of text into any parse-able AST node.
    ///
    /// This will automatically fill [`NodeId`]s, [`ResId`]s, and [`LoopId`]s.
    ///
    /// The name does not need to be a valid path or even unique; for instance, it is common to use
    /// the name `"<input>"` for source text not associated with any file.
    pub fn parse<A>(&mut self, display_name: &str, text: &[u8]) -> Result<Sp<A>, ErrorReported>
    where
        A: crate::parse::Parse,
        Sp<A>: crate::ast::Visitable,
    {
        let (file_id, source_str) = self.ctx.emitter.files.add(display_name, text).map_err(|e| self.emit(e))?;
        let source_str = crate::pos::SourceStr::from_full_source(file_id, &source_str[..]);
        let mut state = crate::parse::State::new();
        let mut lexer = crate::parse::lexer::GenericLexer::<>::new(source_str);
        A::parse_stream(&mut state, &mut lexer)
            .map_err(|e| self.emit(e))
            .and_then(|mut ast| {
                crate::passes::resolution::fill_missing_node_ids(&mut ast, &self.ctx.unused_node_ids)?;
                crate::passes::resolution::assign_res_ids(&mut ast, &mut self.ctx)?;
                crate::passes::resolution::assign_loop_ids(&mut ast, &mut self.ctx)?;
                Ok(ast)
            })
    }

    /// Register a source text for the purpose of display in diagnostics, without parsing it.
    ///
    /// This is primarily for unit tests for parsers of things besides the full AST. (otherwise you
    /// would use [`Self::parse`]...)
    #[cfg(test)]
    pub(crate) fn register_source<'b>(&mut self, display_name: &str, text: &'b str) -> Result<crate::pos::SourceStr<'b>, ErrorReported> {
        let (file_id, _) = self.ctx.emitter.files.add(display_name, text.as_ref()).map_err(|e| self.emit(e))?;
        Ok(crate::pos::SourceStr::from_full_source(file_id, text))
    }
}

/// # Common behavior of pragmas
impl Truth<'_> {
    /// Loads mapfiles from a parsed script.
    pub fn load_mapfiles_from_pragmas(&mut self, game: Game, script: &ast::ScriptFile) -> Result<(), ErrorReported> {
        for path_literal in &script.mapfiles {
            let path: &Path = path_literal.string.as_ref();
            self.load_mapfile(&path, game)?;
        }
        Ok(())
    }

    pub fn expect_no_image_sources(&self, ast: &ast::ScriptFile) -> Result<(), ErrorReported> {
        if let Some(path) = ast.image_sources.get(0) {
            Err(self.emit(error!(
                message("unexpected image_source"),
                primary(path.span, "image_source not valid in this format"),
            )))
        } else { Ok(()) }
    }
}

/// # Compilation and decompilation
impl<'ctx> Truth<'ctx> {
    /// Perform the "mapfile validation" pass.
    ///
    /// This does additional validation on mapfile stuff that didn't seem to fit anywhere else.
    ///
    /// This must be called before any compilation/decompilation can be done.  Ideally, it should be
    /// called **after** all mapfiles have been read, including those listed inside any source files we
    /// are compiling.
    ///
    /// FIXME: This should *eventually* be superceded by however we implement truth-syntax-style
    ///        definition files, and will likely occur at the same time we do name resolution
    ///        and const eval and other language-independent things.
    pub fn validate_defs(&mut self) -> Result<TruthWithValidatedDefs<'_, 'ctx>, ErrorReported> {
        self.ctx.validate_defs()?;
        Ok(TruthWithValidatedDefs { truth: self })
    }
}

/// Typestate-helper wrapper to ensure we don't forget to call [`Truth::validate_defs`],
/// which is otherwise easy to forget and could go unnoticed.
///
/// This is where all of big compilation/decompilation/reading/writing functions are defined.
pub struct TruthWithValidatedDefs<'a, 'ctx> {
    truth: &'a mut Truth<'ctx>,
}

impl<'a, 'ctx> core::ops::Deref for TruthWithValidatedDefs<'a, 'ctx> {
    type Target = &'a mut Truth<'ctx>;

    fn deref(&self) -> &Self::Target { &self.truth }
}

impl<'a, 'ctx> core::ops::DerefMut for TruthWithValidatedDefs<'a, 'ctx> {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.truth }
}

/// # Compilation and decompilation
impl TruthWithValidatedDefs<'_, '_> {
    pub fn compile_anm(&mut self, game: Game, ast: &ast::ScriptFile) -> Result<crate::WorkingAnmFile, ErrorReported> {
        crate::WorkingAnmFile::compile_from_ast(game, ast, &mut self.ctx)
    }
    pub fn compile_msg(&mut self, game: Game, language: LanguageKey, ast: &ast::ScriptFile) -> Result<crate::MsgFile, ErrorReported> {
        crate::MsgFile::compile_from_ast(game, language, ast, &mut self.ctx)
    }
    pub fn compile_mission(&mut self, game: Game, ast: &ast::ScriptFile) -> Result<crate::MissionMsgFile, ErrorReported> {
        crate::MissionMsgFile::compile_from_ast(game, ast, &mut self.ctx)
    }
    pub fn compile_std(&mut self, game: Game, ast: &ast::ScriptFile) -> Result<crate::StdFile, ErrorReported> {
        crate::StdFile::compile_from_ast(game, ast, &mut self.ctx)
    }
    pub fn compile_ecl(&mut self, game: Game, ast: &ast::ScriptFile) -> Result<crate::EclFile, ErrorReported> {
        crate::EclFile::compile_from_ast(game, ast, &mut self.ctx)
    }

    pub fn decompile_anm(&mut self, game: Game, middle: &crate::AnmFile, decompile_options: &DecompileOptions) -> Result<ast::ScriptFile, ErrorReported> {
        crate::AnmFile::decompile_to_ast(middle, game, &mut self.ctx, decompile_options)
    }
    pub fn decompile_msg(&mut self, game: Game, language: LanguageKey, middle: &crate::MsgFile, decompile_options: &DecompileOptions) -> Result<ast::ScriptFile, ErrorReported> {
        crate::MsgFile::decompile_to_ast(middle, game, language, &mut self.ctx, decompile_options)
    }
    pub fn decompile_mission(&mut self, game: Game, middle: &crate::MissionMsgFile) -> Result<ast::ScriptFile, ErrorReported> {
        crate::MissionMsgFile::decompile_to_ast(middle, game, &mut self.ctx)
    }
    pub fn decompile_std(&mut self, game: Game, middle: &crate::StdFile, decompile_options: &DecompileOptions) -> Result<ast::ScriptFile, ErrorReported> {
        crate::StdFile::decompile_to_ast(middle, game, &mut self.ctx, decompile_options)
    }
    pub fn decompile_ecl(&mut self, game: Game, middle: &crate::EclFile, decompile_options: &DecompileOptions) -> Result<ast::ScriptFile, ErrorReported> {
        crate::EclFile::decompile_to_ast(middle, game, &mut self.ctx, decompile_options)
    }
}

/// # Binary file IO
impl TruthWithValidatedDefs<'_, '_> {
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
    pub fn read_image_source(&mut self, game: Game, path: &Path) -> Result<crate::anm::ImageSource, ErrorReported> {
        let metadata = self.fs().metadata(path).map_err(|e| self.emit(e))?;

        if metadata.is_file() {
            let with_images = true;
            self.read_anm(game, path, with_images).map(crate::anm::ImageSource::Anm)
        } else if metadata.is_dir() {
            Ok(crate::anm::ImageSource::Directory(path.to_owned()))
        } else {
            Err(self.emit(error!("{}: unable to determine type of path", path.display())))
        }
    }
    pub fn read_msg(&mut self, game: Game, language: LanguageKey, path: &Path) -> Result<crate::MsgFile, ErrorReported> {
        crate::MsgFile::read_from_stream(&mut self.fs().open_read(path)?, game, language)
    }
    pub fn read_mission(&mut self, game: Game, path: &Path) -> Result<crate::MissionMsgFile, ErrorReported> {
        crate::MissionMsgFile::read_from_stream(&mut self.fs().open_read(path)?, game)
    }
    pub fn read_std(&mut self, game: Game, path: &Path) -> Result<crate::StdFile, ErrorReported> {
        crate::StdFile::read_from_stream(&mut self.fs().open_read(path)?, game)
    }
    pub fn read_ecl(&mut self, game: Game, path: &Path) -> Result<crate::EclFile, ErrorReported> {
        crate::EclFile::read_from_stream(&mut self.fs().open_read(path)?, game)
    }

    /// This can be called after loading all image sources.
    pub fn finalize_anm(&mut self, game: Game, middle: crate::WorkingAnmFile) -> Result<crate::AnmFile, ErrorReported> {
        middle.finalize(&mut self.fs(), game, self.ctx.emitter)
    }

    pub fn write_anm(&mut self, game: Game, outpath: &Path, middle: &crate::AnmFile) -> Result<(), ErrorReported> {
        crate::AnmFile::write_to_stream(middle, &mut self.fs().create_buffered(outpath)?, game)
    }
    pub fn write_msg(&mut self, game: Game, language: LanguageKey, outpath: &Path, middle: &crate::MsgFile) -> Result<(), ErrorReported> {
        crate::MsgFile::write_to_stream(middle, &mut self.fs().create_buffered(outpath)?, game, language)
    }
    pub fn write_mission(&mut self, game: Game, outpath: &Path, middle: &crate::MissionMsgFile) -> Result<(), ErrorReported> {
        crate::MissionMsgFile::write_to_stream(middle, &mut self.fs().create_buffered(outpath)?, game)
    }
    pub fn write_std(&mut self, game: Game, outpath: &Path, middle: &crate::StdFile) -> Result<(), ErrorReported> {
        crate::StdFile::write_to_stream(middle, &mut self.fs().create_buffered(outpath)?, game)
    }
    pub fn write_ecl(&mut self, game: Game, outpath: &Path, middle: &crate::EclFile) -> Result<(), ErrorReported> {
        crate::EclFile::write_to_stream(middle, &mut self.fs().create_buffered(outpath)?, game)
    }
}

// =============================================================================
// Helpers

impl<'ctx> Truth<'ctx> {
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
