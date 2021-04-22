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

    if let Some(magic) = format.magic() {
        reader.expect_magic(emitter, &magic.to_le_bytes())?;
    }

    let num_subs = reader.read_u16()? as usize;
    let num_subs_high_word = reader.read_u16()? as usize;

    let timeline_array_len; // how many u32s to read for timelines
    let expected_nonzero_timelines; // how many of them SHOULD be nonzero
    match format.timeline_array_kind() {
        TimelineArrayKind::Pofv => {
            timeline_array_len = num_subs_high_word;
            expected_nonzero_timelines = num_subs_high_word;
        },
        TimelineArrayKind::Pcb { cap } => {
            timeline_array_len = cap;
            expected_nonzero_timelines = num_subs_high_word + 1;
        }
        TimelineArrayKind::Eosd { cap } => {
            timeline_array_len = cap;
            expected_nonzero_timelines = 1;
            if num_subs_high_word != 0 {
                emitter.emit(warning!(
                    "unexpected nonzero high word for num_subs: {:#x}", num_subs_high_word,
                )).ignore();
            }
        },
    };
    let timeline_offsets = reader.read_u32s(timeline_array_len)?;
    let sub_offsets = reader.read_u32s(num_subs)?;

    // expect a prefix of the timeline array to be filled
    // (because we can't represent a sparsely filled timeline array in the AST)
    let mut num_timelines = timeline_offsets.iter().position(|&x| x == 0).unwrap_or(timeline_offsets.len());
    for &offset in &timeline_offsets[num_timelines..] {
        if offset != 0 {
            return Err(emitter.emit(error!("unexpected timeline offset {:#x} after a null offset", offset)));
        }
    }

    if num_timelines != expected_nonzero_timelines {
        emitter.emit(warning!(
            "expected {} nonzero entries in timeline table, but found {}",
            expected_nonzero_timelines, num_timelines,
        )).ignore();
    }
    if matches!(format.timeline_array_kind(), TimelineArrayKind::Pcb { .. }) {
        num_timelines -= 1;  // in these games, that last entry points to the end of the file
    }

    eprintln!("NUM_SUBS {}", num_subs);
    eprintln!("NUM_TIMELINES {}", num_timelines);

    let subs = sub_offsets.into_iter().enumerate().map(|(index, sub_offset)| {
        let name = auto_sub_name(index as u32);

        eprintln!(": SUB {} AT {:#x}", index, sub_offset);
        reader.seek_to(start_pos + sub_offset as u64)?;
        let instrs = emitter.chain_with(|f| write!(f, "in sub {}", index), |emitter| {
            eprintln!("    TIME _OP_ SIZE DIFF MASK  ARGS");
            llir::read_instrs(reader, emitter, instr_format, sub_offset as u64, None)
        })?;
        Ok((name, instrs))
    }).collect::<ReadResult<_>>()?;

    let timelines = timeline_offsets[..num_timelines].iter().enumerate().map(|(index, &sub_offset)| {
        let name = auto_timeline_name(index as u32);

        eprintln!(": TIMELINE {} AT {:#x}", index, sub_offset);
        reader.seek_to(start_pos + sub_offset as u64)?;
        let instrs = emitter.chain_with(|f| write!(f, "in timeline sub {}", index), |emitter| {
            eprintln!("TIME ARG0 _OP_ SZ DF  ARGS");
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
    let timeline_format = &*format.timeline_format();

    let start_pos = w.pos()?;

    if let Some(magic) = format.magic() {
        w.write_u32(magic)?;
    }

    if ecl.timelines.len() > format.timeline_array_kind().max_timelines() {
        // FIXME: NEEDSTEST for each game
        return Err(emitter.emit(error!("too many timelines! (max allowed in this game is {})", ecl.timelines.len())));
    }

    match format.timeline_array_kind() {
        | TimelineArrayKind::Pofv { .. }
        | TimelineArrayKind::Pcb { .. } => {
            w.write_u16(ecl.subs.len() as _)?;
            w.write_u16(ecl.timelines.len() as _)?;
        },
        | TimelineArrayKind::Eosd { .. } => {
            w.write_u16(ecl.subs.len() as _)?;
            w.write_u16(0)?;
        },
    };

    let timeline_array_len = match format.timeline_array_kind() {
        TimelineArrayKind::Pcb { cap } => cap,
        TimelineArrayKind::Eosd { cap, .. } => cap,
        TimelineArrayKind::Pofv => ecl.timelines.len(),
    };

    let script_offsets_pos = w.pos()?;
    for _ in 0..ecl.subs.len() + timeline_array_len {
        w.write_u32(0)?;
    }

    let mut sub_offsets = vec![];
    for (index, (ident, sub)) in ecl.subs.iter().enumerate() {
        sub_offsets.push(w.pos()? - start_pos);
        emitter.chain_with(|f| write!(f, "in sub {} (index {})", ident, index), |emitter| {
            llir::write_instrs(w, emitter, instr_format, &sub)
        })?;
    }

    let mut timeline_offsets = vec![];
    for (index, (ident, sub)) in ecl.timelines.iter().enumerate() {
        timeline_offsets.push(w.pos()? - start_pos);
        emitter.chain_with(|f| write!(f, "in sub {} (index {})", ident, index), |emitter| {
            llir::write_instrs(w, emitter, timeline_format, &sub)
        })?;
    }

    let end_pos = w.pos()?;
    if matches!(format.timeline_array_kind(), TimelineArrayKind::Pcb { .. }) {
        // in these games, that last entry points to the end of the file
        timeline_offsets.push(end_pos - start_pos);
    }
    timeline_offsets.resize(timeline_array_len, 0);

    w.seek_to(script_offsets_pos)?;
    for offset in timeline_offsets {
        w.write_u32(offset as u32)?;
    }
    for offset in sub_offsets {
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

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum TimelineArrayKind {
    /// There appears to be space for `cap` items, but only the first is used.
    Eosd { cap: usize },
    /// The timeline offset array is a fixed size, but the file specifies how many are actually used.
    ///
    /// (there will be that many nonzero entries *plus one*; the final one will be the ending offset of
    ///  the last timeline, which should coincide with the size of the file)
    Pcb { cap: usize },
    /// The length of the timeline offset array is specified in the file.  All entries are used.
    Pofv,
}

impl TimelineArrayKind {
    fn max_timelines(&self) -> usize {
        match *self {
            TimelineArrayKind::Eosd { .. } => 1,
            TimelineArrayKind::Pcb { cap } => cap - 1, // room for file size
            TimelineArrayKind::Pofv => usize::MAX,
        }
    }
}

impl OldeFileFormat {
    fn magic(&self) -> Option<u32> {
        match self.game {
            | Game::Th06 | Game::Th07 => None,
            | Game::Th08 | Game::Th095 => Some(0x00_00_08_00),
            | Game::Th09 => Some(0x00_00_09_00),
            _ => unimplemented!("game not yet supported"),
        }
    }

    fn timeline_array_kind(&self) -> TimelineArrayKind {
        match self.game {
            | Game::Th06 => TimelineArrayKind::Eosd { cap: 3 },

            | Game::Th07 | Game::Th08 | Game::Th095
            => TimelineArrayKind::Pcb { cap: 16 },

            | Game::Th09 => TimelineArrayKind::Pofv,

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

        let args_blob = f.read_byte_vec(size - self.instr_header_size())?;

        eprintln!("{:08x} {:04x} {:04x} {:04x} {:04x}  {}", time, opcode, size, difficulty, param_mask, crate::io::hexify(&args_blob));
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
        f.write_all(&instr.args_blob)?;
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
        let arg_0 = f.read_i16()? as i32;

        // with some games the terminal instruction is only 4 bytes long so we must check now
        if self.has_short_terminal() && (time, arg_0) == (-1, 4) {
            // FIXME: really should be MaybeTerminal since both arg_0 = 4 and time = -1
            //        are things that naturally occur on real instructions.
            return Ok(ReadInstr::Terminal);
        }

        let opcode = f.read_u16()?;
        let size = f.read_u8()? as usize;
        let difficulty = f.read_u8()? as u16;

        // in games with the normal-sized terminal, the size is incorrectly 0, so check before reading args
        if !self.has_short_terminal() && (time, arg_0, opcode, size, difficulty) == (-1, -1, 0, 0, 0) {
            // FIXME: really should be MaybeTerminal
            return Ok(ReadInstr::Terminal);
        }

        let args_blob = f.read_byte_vec(size - self.instr_header_size())?;
        eprintln!("{:04x} {:04x} {:04x} {:02x} {:02x}  {}", time as i16, arg_0 as u16, opcode as u16, size as u8, difficulty as u8, crate::io::hexify(&args_blob));

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
        f.write_all(&instr.args_blob)?;
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
