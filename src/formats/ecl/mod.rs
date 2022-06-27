use crate::ast;
use crate::io::{BinReader, BinWriter, ReadResult, WriteResult};
use crate::error::{ErrorReported};
use crate::game::{Game};
use crate::llir::{DecompileOptions};
use crate::context::CompilerContext;

use ecl_06::OldeEclFile;
pub mod ecl_06;

use ecl_10::StackEclFile;
pub mod ecl_10;

#[derive(Debug, Clone)]
#[derive(strum::EnumDiscriminants)]
#[strum_discriminants(name(EclFileKind))]
pub enum EclFile {
    Olde(ecl_06::OldeEclFile),
    Stack(ecl_10::StackEclFile),
}

impl EclFile {
    pub fn decompile_to_ast(&self, game: Game, ctx: &mut CompilerContext, decompile_options: &DecompileOptions) -> Result<ast::ScriptFile, ErrorReported> {
        match self {
            EclFile::Olde(ecl) => ecl.decompile_to_ast(game, ctx, decompile_options),
            EclFile::Stack(ecl) => ecl.decompile_to_ast(game, ctx, decompile_options),
        }
    }

    pub fn compile_from_ast(game: Game, ast: &ast::ScriptFile, ctx: &mut CompilerContext) -> Result<Self, ErrorReported> {
        match EclFileKind::of_game(game) {
            EclFileKind::Olde => OldeEclFile::compile_from_ast(game, ast, ctx).map(EclFile::Olde),
            EclFileKind::Stack => StackEclFile::compile_from_ast(game, ast, ctx).map(EclFile::Stack),
        }
    }

    pub fn write_to_stream(&self, w: &mut BinWriter, game: Game) -> WriteResult {
        match self {
            EclFile::Olde(ecl) => ecl.write_to_stream(w, game),
            EclFile::Stack(ecl) => ecl.write_to_stream(w, game),
        }
    }

    pub fn read_from_stream(r: &mut BinReader, game: Game) -> ReadResult<Self> {
        match EclFileKind::of_game(game) {
            EclFileKind::Olde => OldeEclFile::read_from_stream(r, game).map(EclFile::Olde),
            EclFileKind::Stack => StackEclFile::read_from_stream(r, game).map(EclFile::Stack),
        }
    }
}

impl EclFileKind {
    pub fn of_game(game: Game) -> Self {
        if game < Game::Th10 {
            EclFileKind::Olde
        } else {
            EclFileKind::Stack
        }
    }
}
