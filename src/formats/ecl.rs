use std::fmt;
use std::io;
use std::num::NonZeroU64;

use enum_map::EnumMap;
use indexmap::{IndexSet, IndexMap};

use crate::ast;
use crate::io::{BinRead, BinWrite, BinReader, BinWriter, Encoded, ReadResult, WriteResult, DEFAULT_ENCODING};
use crate::diagnostic::{Emitter};
use crate::error::{GatherErrorIteratorExt, ErrorReported};
use crate::game::Game;
use crate::ident::{Ident, ResIdent};
use crate::llir::{self, ReadInstr, RawInstr, InstrFormat, IntrinsicInstrKind};
use crate::meta::{self, FromMeta, FromMetaError, Meta, ToMeta};
use crate::pos::{Sp, Span};
use crate::value::{ScalarType};
use crate::context::CompilerContext;
use crate::passes::DecompileKind;
use crate::resolve::RegId;

// =============================================================================

/// Game-independent representation of an ANM file.
#[derive(Debug, Clone)]
pub struct OldeEclFile {
    pub subs: IndexMap<Ident, Vec<RawInstr>>,
    pub timelines: IndexMap<Ident, Vec<RawInstr>>,
    /// Filename of a read binary file, for display purposes only.
    binary_filename: Option<String>,
}

impl OldeEclFile {
    // pub fn decompile_to_ast(&self, game: Game, ctx: &mut CompilerContext, decompile_kind: DecompileKind) -> Result<ast::ScriptFile, ErrorReported> {
    //     let emitter = ctx.emitter.while_decompiling(self.binary_filename.as_deref());
    //     decompile(self, &emitter, &game_format(game), ctx, decompile_kind)
    // }
    //
    // pub fn compile_from_ast(game: Game, ast: &ast::ScriptFile, ctx: &mut CompilerContext) -> Result<Self, ErrorReported> {
    //     compile(&game_format(game), ast, ctx)
    // }

    pub fn write_to_stream(&self, w: &mut BinWriter, game: Game) -> WriteResult {
        let emitter = w.emitter();
        write_olde_ecl(w, &emitter, &game_format(game)?, self)
    }

    pub fn read_from_stream(r: &mut BinReader, game: Game) -> ReadResult<Self> {
        let emitter = r.emitter();
        read_olde_ecl(r, &emitter, &game_format(game)?)
    }
}

// =============================================================================

#[cfg(nope)]
fn decompile(
    anm_file: &OldeEclFile,
    emitter: &impl Emitter,
    format: &OldeFileFormat,
    ctx: &mut CompilerContext,
    decompile_kind: DecompileKind,
) -> Result<ast::ScriptFile, ErrorReported> {

}

// =============================================================================

#[cfg(nope)]
fn compile(
    format: &OldeFileFormat,
    ast: &ast::ScriptFile,
    ctx: &mut CompilerContext,
) -> Result<OldeEclFile, ErrorReported> {

}

// =============================================================================

fn read_olde_ecl(
    reader: &mut BinReader,
    emitter: &impl Emitter,
    format: &OldeFileFormat,
) -> ReadResult<OldeEclFile> {
    let instr_format = &*format.instr_format();
    let timeline_format = &*format.timeline_format();

    let start_pos = reader.pos()?;

    reader.expect_magic(emitter, &format.magic().to_le_bytes())?;

    let num_subs = reader.read_u32()? as usize;
    let num_timelines = reader.read_u32()? as usize;

    let sub_offsets = reader.read_u32s(num_subs)?;
    let timeline_offsets = reader.read_u32s(num_timelines)?;

    let subs = sub_offsets.into_iter().enumerate().map(|(index, sub_offset)| {
        let name = auto_sub_name(index as u32);

        reader.seek_to(start_pos + sub_offset as u64)?;
        let instrs = emitter.chain_with(|f| write!(f, "in sub {}", index), |emitter| {
            llir::read_instrs(reader, emitter, instr_format, sub_offset as u64, None)
        })?;
        Ok((name, instrs))
    }).collect::<ReadResult<_>>()?;

    let timelines = timeline_offsets.into_iter().enumerate().map(|(index, sub_offset)| {
        let name = auto_timeline_name(index as u32);

        reader.seek_to(start_pos + sub_offset as u64)?;
        let instrs = emitter.chain_with(|f| write!(f, "in timeline sub {}", index), |emitter| {
            llir::read_instrs(reader, emitter, timeline_format, sub_offset as u64, None)
        })?;
        Ok((name, instrs))
    }).collect::<ReadResult<_>>()?;

    let binary_filename = Some(reader.display_filename().to_string());
    Ok(OldeEclFile { subs, timelines, binary_filename })
}

pub fn auto_sub_name(i: u32) -> Ident {
    format!("sub{}", i).parse::<Ident>().unwrap()
}
pub fn auto_timeline_name(i: u32) -> Ident {
    format!("timeline{}", i).parse::<Ident>().unwrap()
}

fn write_olde_ecl(
    w: &mut BinWriter,
    emitter: &impl Emitter,
    format: &OldeFileFormat,
    ecl: &OldeEclFile,
) -> WriteResult {
    let instr_format = &*format.instr_format();

    let start_pos = w.pos()?;

    w.write_u32(format.magic())?;
    w.write_u32(ecl.subs.len() as _)?;
    w.write_u32(ecl.timelines.len() as _)?;

    let script_offsets_pos = w.pos()?;
    for _ in 0..ecl.subs.len() + ecl.timelines.len() {
        w.write_u32(0)?;
    }

    let mut script_offsets = vec![];
    for (index, (ident, sub)) in ecl.subs.iter().enumerate() {
        script_offsets.push(w.pos()? - start_pos);
        emitter.chain_with(|f| write!(f, "in sub {} (index {})", ident, index), |emitter| {
            llir::write_instrs(w, emitter, instr_format, &sub)
        })?;
    }

    for (index, (ident, sub)) in ecl.timelines.iter().enumerate() {
        script_offsets.push(w.pos()? - start_pos);
        emitter.chain_with(|f| write!(f, "in sub {} (index {})", ident, index), |emitter| {
            llir::write_instrs(w, emitter, instr_format, &sub)
        })?;
    }
    let end_pos = w.pos()?;

    w.seek_to(script_offsets_pos)?;
    for offset in script_offsets {
        w.write_u32(offset as u32)?;
    }
    w.seek_to(end_pos)?;
    Ok(())
}

// =============================================================================

fn game_format(game: Game) -> Result<OldeFileFormat, ErrorReported> {
    match game {
        | Game::Th06 | Game::Th07 | Game::Th08 | Game::Th09 | Game::Th095
        => Ok(OldeFileFormat { game }),

        _ => Err(unimplemented!("game {} not yet supported", game)),
    }
}

pub fn game_core_mapfile(game: Game) -> crate::Eclmap {
    super::core_mapfiles::msg::core_signatures(game).to_mapfile(game)
}

// =============================================================================

struct OldeFileFormat { game: Game }

impl OldeFileFormat {
    fn magic(&self) -> u32 {
        match self.game {
            | Game::Th06 | Game::Th07 | Game::Th08 | Game::Th09 => 0x0000_0800,
            | Game::Th095 => 0x0000_0900,
            _ => unimplemented!("game not yet supported"),
        }
    }

    fn instr_format(&self) -> Box<dyn InstrFormat> { Box::new(InstrFormat06) }
    fn timeline_format(&self) -> Box<dyn InstrFormat> { Box::new(TimelineInstrFormat { game: self.game }) }
}

struct InstrFormat06;

impl InstrFormat for InstrFormat06 {
    fn intrinsic_opcode_pairs(&self) -> Vec<(llir::IntrinsicInstrKind, u16)> {
        vec![]
    }

    fn instr_header_size(&self) -> usize { 12 }

    fn read_instr(&self, f: &mut BinReader, _: &dyn Emitter) -> ReadResult<ReadInstr> {
        let time = f.read_i32()?;
        let opcode = f.read_u16()?;
        let size = f.read_u16()? as usize;
        let difficulty = f.read_u16()?;
        let param_mask = f.read_u16()?;

        let args_blob = f.read_byte_vec(size)?;
        let instr = RawInstr { time, opcode, param_mask, args_blob, difficulty, ..RawInstr::DEFAULTS };

        if opcode == (-1_i16) as u16 {
            Ok(ReadInstr::Terminal)
        } else {
            Ok(ReadInstr::Instr(instr))
        }
    }

    fn write_instr(&self, f: &mut BinWriter, _: &dyn Emitter, instr: &RawInstr) -> WriteResult {
        f.write_i32(instr.time)?;
        f.write_u16(instr.opcode)?;
        f.write_u16(self.instr_size(instr) as _)?;
        f.write_u16(instr.difficulty)?;
        f.write_u16(instr.param_mask)?;
        Ok(())
    }

    fn write_terminal_instr(&self, f: &mut BinWriter, _: &dyn Emitter) -> WriteResult {
        f.write_i32(-1)?; // time
        f.write_i16(-1)?; // opcode
        f.write_u16(self.instr_header_size() as _)?; // size
        f.write_u16(0xff00)?; // difficulty
        f.write_u16(0x00ff)?; // param_mask
        Ok(())
    }
}

struct TimelineInstrFormat { game: Game }
impl TimelineInstrFormat {
    /// In some games, the terminal instruction is shorter than an actual instruction.
    fn has_short_terminal(&self) -> bool {
        self.game < Game::Th08
    }
}

impl InstrFormat for TimelineInstrFormat {
    fn intrinsic_opcode_pairs(&self) -> Vec<(llir::IntrinsicInstrKind, u16)> {
        vec![]
    }

    fn instr_header_size(&self) -> usize { 8 }

    fn read_instr(&self, f: &mut BinReader, emitter: &dyn Emitter) -> ReadResult<ReadInstr> {
        let time = f.read_i16()? as i32;
        let arg_0 = f.read_i16()? as u32;

        // with some games the terminal instruction is only 4 bytes long so we must check now
        if self.has_short_terminal() && arg_0 == 4 {
            if time != -1 {
                emitter.as_sized().emit(warning!("unexpected time arg on terminal instruction: got {}, expected -1", time)).ignore();
            }
            return Ok(ReadInstr::Terminal);
        }

        let opcode = f.read_u16()?;
        let size = f.read_u8()? as usize;
        let difficulty = f.read_u8()? as u16;

        // in games with the normal-sized terminal, the size is incorrectly 0, so check before reading args
        if !self.has_short_terminal() && opcode == (-1_i16) as u16 {
            if (time, opcode, size, difficulty) != (-1, 0, 0, 0) {
                emitter.as_sized().emit(warning!("\
                    unexpected data on terminal instruction: \
                    expected (time, opcode, size, difficulty) = (-1, 0, 0, 0), got {:?}\
                ", (time, opcode, size, difficulty))).ignore();
            }
            return Ok(ReadInstr::Terminal);
        }

        let args_blob = f.read_byte_vec(size - self.instr_header_size())?;
        let instr = RawInstr {
            time, opcode, difficulty, args_blob,
            extra_arg: Some(arg_0 as _),
            ..RawInstr::DEFAULTS
        };
        Ok(ReadInstr::Instr(instr))
    }

    fn write_instr(&self, f: &mut BinWriter, _: &dyn Emitter, instr: &RawInstr) -> WriteResult {
        f.write_i16(instr.time as _)?;
        f.write_i16(instr.extra_arg.expect("missing extra_arg on timeline?!") as _)?;
        f.write_u16(instr.opcode)?;
        f.write_u8(self.instr_size(instr) as _)?;
        f.write_u8(instr.difficulty as _)?;
        Ok(())
    }

    fn write_terminal_instr(&self, f: &mut BinWriter, _: &dyn Emitter) -> WriteResult {
        if self.game < Game::Th08 {
            f.write_i16(-1)?; // time
            f.write_i16(4)?; // arg_0
        } else {
            f.write_i16(-1)?; // time
            f.write_i16(-1)?; // arg_0
            f.write_u32(0)?; // opcode, size, difficulty
        }
        Ok(())
    }
}
