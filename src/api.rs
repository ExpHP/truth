use std::path::Path;

use crate::ast;
use crate::game::Game;
use crate::error::ErrorReported;
use crate::context::CompilerContext;
use crate::io::{BinReader, BinWriter};
use crate::passes::DecompileKind;

/// Front-end API of `truth`, for direct use by `truth`'s various entry point functions, as well
/// as by unit tests.
pub struct Truth<'ctx> {
    ctx: CompilerContext<'ctx>,
}

/// # Construction
impl Truth<'_> {
    /// Construct a new instance that prints diagnostics to STDERR.
    ///
    /// Due to the borrowed data inside the type, it cannot be directly returned, and is instead "returned"
    /// by passing it into a continuation function.
    pub fn new_stderr<T>(cont: impl for<'a> FnOnce(&mut Truth<'a>) -> T) -> T {
        CompilerContext::new_stderr(|ctx| cont(&mut Truth { ctx }))
    }
}

/// # Reading text files
impl Truth<'_> {
    pub fn load_mapfile(&mut self, text: &str) -> Result<(), ErrorReported> {
        crate::Eclmap::parse(text, &self.ctx.diagnostics)
            .and_then(|eclmap| self.ctx.extend_from_eclmap(None, &eclmap))
            .map_err(|e| self.emit(error!("{:#}", e)))
    }

    pub fn read_mapfile_and_record(&mut self, filepath: &Path, game: Option<Game>) -> Result<(), ErrorReported> {
        use anyhow::Context; // FIXME remove

        crate::Eclmap::load(filepath, game, &self.ctx.diagnostics)
            .and_then(|eclmap| {
                self.ctx.extend_from_eclmap(Some(filepath), &eclmap)
                    .with_context(|| format!("while applying '{}'", filepath.display()))
            })
            .map_err(|e| self.emit(error!("{:#}", e)))
    }

    pub fn read_script(&mut self, path: &Path) -> Result<ast::Script, ErrorReported> {
        self.ctx.diagnostics.files.read_file(&path).map_err(|e| self.ctx.diagnostics.emit(e)).map(|sp| sp.value)
    }
}

/// # Common behavior of pragmas
impl Truth<'_> {
    /// Loads mapfiles from a parsed script.
    pub fn load_mapfiles_from_pragmas(&mut self, game: Game, script: &ast::Script) -> Result<(), ErrorReported> {
        for path_literal in &script.mapfiles {
            let path: &Path = path_literal.string.as_ref();

            crate::error::group_anyhow(|| {
                let eclmap = crate::Eclmap::load(&path, Some(game), &self.ctx.diagnostics)?;
                self.ctx.extend_from_eclmap(Some(path), &eclmap)?;
                Ok(())
            }).map_err(|e| self.ctx.diagnostics.emit(error!(
                message("{:#}", e),
                primary(path_literal, "error loading mapfile"),
            )))?
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
        crate::AnmFile::decompile_to_ast(middle, game, &self.ctx, decompile_kind)
    }
    pub fn decompile_msg(&mut self, game: Game, middle: &crate::MsgFile, decompile_kind: DecompileKind) -> Result<ast::Script, ErrorReported> {
        crate::MsgFile::decompile_to_ast(middle, game, &self.ctx, decompile_kind)
    }
    pub fn decompile_std(&mut self, game: Game, middle: &crate::StdFile, decompile_kind: DecompileKind) -> Result<ast::Script, ErrorReported> {
        crate::StdFile::decompile_to_ast(middle, game, &self.ctx, decompile_kind)
    }
}

/// # Binary file IO
impl Truth<'_> {
    pub fn read_anm(&mut self, game: Game, path: &Path, with_images: bool) -> Result<crate::AnmFile, ErrorReported> {
        match with_images {
            true => {
                let mut reader = BinReader::read(&self.ctx.diagnostics, path)?;
                crate::AnmFile::read_from_stream(&mut reader, game, with_images)
            },
            false => {
                // Here we don't read the whole thing because seeking can skip costly reads of megabytes of image data.
                //
                // Seeking drops the buffer though, so use a tiny buffer.
                let buffer_size = 64;
                let mut reader = BinReader::open(&self.ctx.diagnostics, path)?.map_reader(|r| std::io::BufReader::with_capacity(buffer_size, r));
                crate::AnmFile::read_from_stream(&mut reader, game, with_images)
            },
        }
    }
    pub fn read_msg(&mut self, game: Game, path: &Path) -> Result<crate::MsgFile, ErrorReported> {
        crate::MsgFile::read_from_stream(&mut BinReader::read(&self.ctx.diagnostics, path)?, game)
    }
    pub fn read_std(&mut self, game: Game, path: &Path) -> Result<crate::StdFile, ErrorReported> {
        crate::StdFile::read_from_stream(&mut BinReader::read(&self.ctx.diagnostics, path)?, game)
    }

    pub fn write_anm(&mut self, game: Game, outpath: &Path, middle: &crate::AnmFile) -> Result<(), ErrorReported> {
        crate::AnmFile::write_to_stream(middle, &mut BinWriter::create_buffered(&self.ctx.diagnostics, outpath)?, game)
    }
    pub fn write_msg(&mut self, game: Game, outpath: &Path, middle: &crate::MsgFile) -> Result<(), ErrorReported> {
        crate::MsgFile::write_to_stream(middle, &mut BinWriter::create_buffered(&self.ctx.diagnostics, outpath)?, game)
    }
    pub fn write_std(&mut self, game: Game, outpath: &Path, middle: &crate::StdFile) -> Result<(), ErrorReported> {
        crate::StdFile::write_to_stream(middle, &mut BinWriter::create_buffered(&self.ctx.diagnostics, outpath)?, game)
    }

    /// Like [`std::fs::write`] with error handling.
    pub fn write_file(&mut self, path: &Path, data: impl AsRef<[u8]>) -> Result<(), ErrorReported> {
        unimplemented!()
    }
}

/// # Diagnostics
impl Truth<'_> {
    pub fn emit(&self, e: impl Into<Vec<crate::diagnostic::Diagnostic>>) -> ErrorReported {
        self.ctx.diagnostics.emit(e)
    }
}

