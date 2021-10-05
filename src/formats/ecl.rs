use indexmap::{IndexMap};

use crate::ast;
use crate::pos::Sp;
use crate::io::{BinRead, BinWrite, BinReader, BinWriter, ReadResult, WriteResult};
use crate::diagnostic::{Diagnostic, Emitter};
use crate::error::{ErrorReported};
use crate::game::{Game, InstrLanguage};
use crate::ident::{Ident, ResIdent};
use crate::value::{ScalarType};
use crate::llir::{self, ReadInstr, RawInstr, InstrFormat, DecompileOptions};
use crate::context::CompilerContext;

// =============================================================================

/// Game-independent representation of an ANM file.
#[derive(Debug, Clone)]
pub struct OldeEclFile {
    pub subs: IndexMap<Ident, Vec<RawInstr>>,
    pub timelines: Vec<Vec<RawInstr>>,
    /// Filename of a read binary file, for display purposes only.
    binary_filename: Option<String>,
}

impl OldeEclFile {
    pub fn decompile_to_ast(&self, game: Game, ctx: &mut CompilerContext, decompile_options: &DecompileOptions) -> Result<ast::ScriptFile, ErrorReported> {
        let emitter = ctx.emitter.while_decompiling(self.binary_filename.as_deref());
        decompile(self, &emitter, &game_format(game)?, ctx, decompile_options)
    }

    pub fn compile_from_ast(game: Game, ast: &ast::ScriptFile, ctx: &mut CompilerContext) -> Result<Self, ErrorReported> {
        compile(&game_format(game)?, ast, ctx)
    }

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

fn decompile(
    ecl: &OldeEclFile,
    emitter: &impl Emitter,
    format: &OldeFileFormat,
    ctx: &mut CompilerContext,
    decompile_options: &DecompileOptions,
) -> Result<ast::ScriptFile, ErrorReported> {
    let instr_format = &*format.instr_format();
    let timeline_format = &*format.timeline_format();

    let mut items = vec![];
    let mut timeline_raiser = llir::Raiser::new(timeline_format, &ctx.emitter, decompile_options);
    for (index, instrs) in ecl.timelines.iter().enumerate() {
        items.push(sp!(ast::Item::Timeline {
            keyword: sp!(()),
            number: sp!(index as i32),
            code: ast::Block({
                timeline_raiser.raise_instrs_to_sub_ast(emitter, instrs, &ctx.defs)?
            }),
        }));
    }

    let mut sub_raiser = llir::Raiser::new(instr_format, &ctx.emitter, decompile_options);
    for (ident, instrs) in ecl.subs.iter() {
        items.push(sp!(ast::Item::Func {
            qualifier: None,
            ty_keyword: sp!(ast::TypeKeyword::Void),
            ident: sp!(ResIdent::new_null(ident.clone())),
            params: vec![],
            code: Some(ast::Block({
                sub_raiser.raise_instrs_to_sub_ast(emitter, instrs, &ctx.defs)?
            })),
        }));
    }

    let mut out = ast::ScriptFile {
        items,
        mapfiles: ctx.mapfiles_to_ast(),
        image_sources: vec![],
    };
    crate::passes::postprocess_decompiled(&mut out, ctx, decompile_options)?;
    Ok(out)
}

// =============================================================================

fn compile(
    format: &OldeFileFormat,
    ast: &ast::ScriptFile,
    ctx: &mut CompilerContext,
) -> Result<OldeEclFile, ErrorReported> {
    let instr_format = format.instr_format();
    let timeline_format = format.timeline_format();

    let mut ast = ast.clone();
    crate::passes::resolve_names::assign_res_ids(&mut ast, ctx)?;
    crate::passes::resolve_names::assign_languages(&mut ast, instr_format.language(), ctx)?;

    // an early pass to define global constants for sub names
    let sub_ids = gather_sub_ids(&ast, ctx)?;
    for (index, sub_name) in sub_ids.values().enumerate() {
        let const_value: Sp<ast::Expr> = sp!(sub_name.span => (index as i32).into());
        ctx.define_auto_const_var(sub_name.clone(), ScalarType::Int, const_value);
    }

    // preprocess
    let ast = {
        let mut ast = ast;
        crate::passes::resolve_names::run(&ast, ctx)?;
        crate::passes::type_check::run(&ast, ctx)?;
        crate::passes::evaluate_const_vars::run(ctx)?;
        crate::passes::const_simplify::run(&mut ast, ctx)?;
        crate::passes::desugar_blocks::run(&mut ast, ctx)?;
        ast
    };

    // Compilation pass
    let emitter = ctx.emitter;
    let emit = |e| emitter.emit(e);
    let mut subs = IndexMap::new();
    let mut timelines = vec![];
    for item in ast.items.iter() {
        match &item.value {
            ast::Item::Meta { keyword, .. } => return Err(emit(error!(
                message("unexpected '{}' in old ECL format file", keyword),
                primary(keyword, "not valid in old format ECL files"),
            ))),
            ast::Item::AnmScript { number: Some(number), .. } => return Err(emit(error!(
                message("unexpected numbered script in STD file"),
                primary(number, "unexpected number"),
            ))),
            ast::Item::ConstVar { .. } => {},
            ast::Item::AnmScript { .. } => return Err(emit(unsupported(&item.span))),
            ast::Item::Timeline { code, .. } => {
                let instrs = llir::lower_sub_ast_to_instrs(&*timeline_format, &code.0, ctx)?;
                timelines.push(instrs)
            },
            ast::Item::Func { qualifier: None, code: None, .. } => {
                emit(warning!(
                    message("function declarations have no effect in old-style ECL file"),
                    primary(item, "meaningless declaration"),
                )).ignore();
            },

            ast::Item::Func { qualifier: None, code: Some(code), ref ident, ref params, ty_keyword } => {
                // make double sure that the order of the subs we're compiling matches the numbers we assigned them
                assert_eq!(sub_ids.get_index_of(ident.as_raw()).unwrap(), subs.len());

                if params.len() > 0 {
                    let (_, first_param_name) = &params[0];
                    return Err(ctx.emitter.emit(error!(
                        message("parameters are not supported in old-style ECL subs like '{}'", ident),
                        primary(first_param_name, "unsupported parameter"),
                    )));
                }

                if ty_keyword.value != ast::TypeKeyword::Void {
                    return Err(ctx.emitter.emit(error!(
                        message("return types are not supported in old-style ECL subs like '{}'", ident),
                        primary(ty_keyword, "unsupported return type"),
                    )));
                }

                let instrs = llir::lower_sub_ast_to_instrs(&*instr_format, &code.0, ctx)?;
                subs.insert(ident.value.as_raw().clone(), instrs);
            }

            // TODO: support inline and const
            ast::Item::Func { qualifier: Some(_), .. } => return Err(emit(unsupported(&item.span))),
        } // match item
    }; // for item in script

    Ok(OldeEclFile { subs, timelines, binary_filename: None })
}

fn gather_sub_ids(ast: &ast::ScriptFile, ctx: &mut CompilerContext) -> Result<IndexMap<Ident, Sp<ResIdent>>, ErrorReported> {
    let mut script_ids = IndexMap::new();
    for item in sub_items(&ast.items) {
        match &item.value {
            &ast::Item::Func { qualifier: None, ref ident, .. } => {
                // give a better error on redefinitions than the generic "ambiguous auto const" message
                match script_ids.entry(ident.value.as_raw().clone()) {
                    indexmap::map::Entry::Vacant(e) => {
                        e.insert(ident.clone());
                    },
                    indexmap::map::Entry::Occupied(e) => {
                        let prev_ident = e.get();
                        return Err(ctx.emitter.emit(error!(
                            message("duplicate script '{}'", ident),
                            primary(ident, "redefined here"),
                            secondary(prev_ident, "originally defined here"),
                        )));
                    },
                }
            },
            _ => unreachable!("should've been filtered by sub_items"),
        }
    }
    Ok(script_ids)
}

/// Produces an iterator over just the ECL subs in a list of items.
///
/// Even if this doesn't help with factoring out the match pattern for the items,
/// it helps prevent bugs where different pieces of code differ on which items they consider
/// as "subs".  (as this could lead to using the wrong indices in compilation)
fn sub_items(items: &[Sp<ast::Item>]) -> impl Iterator<Item=&Sp<ast::Item>> {
    items.iter().filter(|item| matches!(item.value, ast::Item::Func { qualifier: None, .. }))
}

fn unsupported(span: &crate::pos::Span) -> Diagnostic {
    error!(
        message("feature not supported by format"),
        primary(span, "not supported by old-format ECL files"),
    )
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

    let subs = sub_offsets.into_iter().enumerate().map(|(index, sub_offset)| {
        let name = auto_sub_name(index as u32);

        reader.seek_to(start_pos + sub_offset as u64)?;
        let instrs = emitter.chain_with(|f| write!(f, "in sub {}", index), |emitter| {
            llir::read_instrs(reader, emitter, instr_format, sub_offset as u64, None)
        })?;
        Ok((name, instrs))
    }).collect::<ReadResult<_>>()?;

    let timelines = timeline_offsets[..num_timelines].iter().enumerate().map(|(index, &sub_offset)| {
        reader.seek_to(start_pos + sub_offset as u64)?;
        let instrs = emitter.chain_with(|f| write!(f, "in timeline sub {}", index), |emitter| {
            llir::read_instrs(reader, emitter, timeline_format, sub_offset as u64, None)
        })?;
        Ok(instrs)
    }).collect::<ReadResult<_>>()?;

    let binary_filename = Some(reader.display_filename().to_string());
    Ok(OldeEclFile { subs, timelines, binary_filename })
}

pub fn auto_sub_name(i: u32) -> Ident {
    format!("sub{}", i).parse::<Ident>().unwrap()
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
    for (index, (ident, instrs)) in ecl.subs.iter().enumerate() {
        sub_offsets.push(w.pos()? - start_pos);
        emitter.chain_with(|f| write!(f, "in sub {} (index {})", ident, index), |emitter| {
            llir::write_instrs(w, emitter, instr_format, instrs)
        })?;
    }

    let mut timeline_offsets = vec![];
    for (index, instrs) in ecl.timelines.iter().enumerate() {
        timeline_offsets.push(w.pos()? - start_pos);
        emitter.chain_with(|f| write!(f, "in timeline {}", index), |emitter| {
            llir::write_instrs(w, emitter, timeline_format, instrs)
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

        _ => unimplemented!("game {} not yet supported", game),
    }
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
    fn language(&self) -> InstrLanguage { InstrLanguage::Ecl }

    fn intrinsic_opcode_pairs(&self) -> Vec<(llir::IntrinsicInstrKind, u16)> {
        vec![] // TODO
    }

    fn instr_header_size(&self) -> usize { 12 }

    fn read_instr(&self, f: &mut BinReader, _: &dyn Emitter) -> ReadResult<ReadInstr> {
        let time = f.read_i32()?;
        let opcode = f.read_u16()?;
        let size = f.read_u16()? as usize;
        let difficulty = f.read_u16()?;
        let param_mask = f.read_u16()?;  // NOTE: Even in EoSD there is space for this, but it's always 0xFFFF.

        let args_blob = f.read_byte_vec(size - self.instr_header_size())?;

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

// ------------

struct TimelineInstrFormat { game: Game }
impl TimelineInstrFormat {
    /// In some games, the terminal instruction is shorter than an actual instruction.
    fn has_short_terminal(&self) -> bool {
        self.game < Game::Th08
    }
}

impl InstrFormat for TimelineInstrFormat {
    fn language(&self) -> InstrLanguage { InstrLanguage::Timeline }

    fn intrinsic_opcode_pairs(&self) -> Vec<(llir::IntrinsicInstrKind, u16)> {
        vec![] // TODO
    }

    fn instr_header_size(&self) -> usize { 8 }

    fn read_instr(&self, f: &mut BinReader, _: &dyn Emitter) -> ReadResult<ReadInstr> {
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
