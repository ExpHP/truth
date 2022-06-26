use indexmap::{IndexMap};
use enum_map::{EnumMap};
use arrayvec::ArrayVec;
use std::collections::{HashSet, BTreeMap};

use crate::raw;
use crate::ast;
use crate::pos::{Sp, Span};
use crate::io::{BinRead, BinWrite, BinReader, BinWriter, ReadResult, WriteResult, DEFAULT_ENCODING, Encoded};
use crate::diagnostic::{Diagnostic, Emitter};
use crate::error::{ErrorReported, ErrorFlag, GatherErrorIteratorExt};
use crate::game::{Game, LanguageKey};
use crate::ident::{Ident, ResIdent};
use crate::value::{ScalarType, ScalarValue, ReadType, VarType};
use crate::llir::{self, ReadInstr, RawInstr, InstrFormat, LanguageHooks, DecompileOptions, RegisterEncodingStyle, HowBadIsIt};
use crate::resolve::{RegId, DefId, IdMap};
use crate::context::CompilerContext;
use crate::context::defs::auto_enum_names;
use crate::debug_info;

// =============================================================================

/// Game-independent representation of an ECL file from TH10 onwards.
#[derive(Debug, Clone)]
pub struct StackEclFile {
    pub subs: IndexMap<Sp<Ident>, Vec<RawInstr>>,
    pub anim_list: Vec<Sp<String>>,
    pub ecli_list: Vec<Sp<String>>,
    /// Filename of a read binary file, for display purposes only.
    binary_filename: Option<String>,
}

impl StackEclFile {
    pub fn decompile_to_ast(&self, game: Game, ctx: &mut CompilerContext, decompile_options: &DecompileOptions) -> Result<ast::ScriptFile, ErrorReported> {
        let emitter = ctx.emitter.while_decompiling(self.binary_filename.as_deref());
        decompile(self, &emitter, game, ctx, decompile_options)
    }

    pub fn compile_from_ast(game: Game, ast: &ast::ScriptFile, ctx: &mut CompilerContext) -> Result<Self, ErrorReported> {
        compile(game, ast, ctx)
    }

    pub fn write_to_stream(&self, w: &mut BinWriter, game: Game) -> WriteResult {
        let emitter = w.emitter();
        write(w, &emitter, game, self)
    }

    pub fn read_from_stream(r: &mut BinReader, game: Game) -> ReadResult<Self> {
        let emitter = r.emitter();
        read(r, &emitter, game)
    }
}

// =============================================================================

fn decompile(
    ecl: &StackEclFile,
    emitter: &impl Emitter,
    game: Game,
    ctx: &mut CompilerContext,
    decompile_options: &DecompileOptions,
) -> Result<ast::ScriptFile, ErrorReported> {
    let hooks = game_hooks(game);

    // TODO: define string consts for sub names

    let const_proof = crate::passes::evaluate_const_vars::run(ctx)?;

    let mut raiser = llir::Raiser::new(&*hooks, ctx.emitter, ctx, decompile_options, const_proof)?;
    // raiser.set_olde_sub_format(sub_format);

    // Decompile ECL subs only halfway
    let mut decompiled_subs = IndexMap::new();
    for (ident, instrs) in ecl.subs.iter() {
        decompiled_subs.insert(ident.clone(), {
            emitter.chain_with(|f| write!(f, "in {}", ident), |emitter| {
                raiser.raise_instrs_to_sub_ast(emitter, instrs, ctx)
            })?
        });
    }

    let mut items = vec![];
    for (ident, stmts) in decompiled_subs{
        items.push(sp!(ast::Item::Func(ast::ItemFunc {
            qualifier: None,
            ty_keyword: sp!(ast::TypeKeyword::Void),
            ident: sp!(ResIdent::new_null(ident.value.clone())),
            params: vec![],
            code: Some(ast::Block(stmts)),
        })));
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
    _game: Game,
    _ast: &ast::ScriptFile,
    _ctx: &mut CompilerContext,
) -> Result<StackEclFile, ErrorReported> {
    todo!()
}

fn unsupported(span: &crate::pos::Span) -> Diagnostic {
    error!(
        message("feature not supported by format"),
        primary(span, "not supported by old-format ECL files"),
    )
}

// =============================================================================

fn read(
    reader: &mut BinReader,
    emitter: &impl Emitter,
    game: Game,
) -> ReadResult<StackEclFile> {
    let hooks = game_hooks(game);
    let instr_format = hooks.instr_format();

    let start_pos = reader.pos()?;
    reader.expect_magic(emitter, "SCPT")?;

    let unknown_1 = reader.read_i16()?;
    if unknown_1 != 1 {
        emitter.emit(warning!("unexpected data in unknown_1 field: {unknown_1:#x}")).ignore();
    }

    let include_length = reader.read_u16()?;
    let include_offset = reader.read_u32()?;

    let zero_1 = reader.read_u32()?;
    if zero_1 != 0 {
        emitter.emit(warning!("unexpected data in zero_1 field: {zero_1:#x}")).ignore();
    }

    let sub_count = reader.read_u32()?;

    for dword_index in 0..4 {
        let zero = reader.read_u32()?;
        if zero != 0 {
            emitter.emit(warning!("unexpected data in zero_2 dword {dword_index}: {zero:#x}")).ignore();
        }
    }

    // trust what the file says...
    let include_pos = start_pos + u64::from(include_offset);
    // ...but complain if it isn't what we expect
    let expected_include_offset = reader.pos()? - start_pos;
    if expected_include_offset != u64::from(include_offset) {
        emitter.emit(warning!("unexpected value of include_offset: {include_offset:#x}, expected {expected_include_offset:#x}")).ignore();
        reader.seek_to(include_pos)?;
    }
    assert_eq!(reader.pos()?, include_pos);

    let anim_list = read_include_section(reader, emitter, "ANIM")?;
    let ecli_list = read_include_section(reader, emitter, "ECLI")?;

    // trust what the file says...
    let sub_list_pos = include_pos + u64::from(include_length);
    // ...but complain if it isn't what we expect
    let expected_include_length = reader.pos()? - include_pos;
    if expected_include_length != u64::from(include_length) {
        emitter.emit(warning!("unexpected value of include_length: {include_length:#x}, expected {expected_include_length:#x}")).ignore();
        reader.seek_to(sub_list_pos)?;
    }
    assert_eq!(reader.pos()?, sub_list_pos);

    let mut sub_offsets = reader.read_u32s(sub_count as usize)?.into_iter().map(u64::from).collect::<Vec<_>>();
    sub_offsets.push(reader.file_size()?);

    let sub_names = {
        read_string_list(reader, emitter, sub_count as usize)?
            .into_iter()
            .map(|string| match Ident::new_user(&string) {
                Ok(ident) => Ok(sp!(ident)),
                // FIXME: substitute with a valid identifier and downgrade to a warning
                Err(_) => Err(emitter.emit(error!("encountered sub with non-identifier name {}", crate::fmt::stringify_lit_str(&string)))),
            })
            .collect::<Result<Vec<_>, _>>()?
    };

    let mut subs = IndexMap::new();
    let mut end_offsets = sub_offsets.iter().copied().skip(1);
    for (sub_index, &sub_header_offset, name) in zip!(0.., &sub_offsets, sub_names) {
        let sub_end_offset = end_offsets.next();
        if let Some(sub_end_offset) = sub_end_offset {
            if sub_end_offset < sub_header_offset {
                return Err(emitter.emit(error!("sub offsets are not sorted!")));
            }
        }

        let instrs = emitter.chain_with(|f| write!(f, "in sub {sub_index} ({name})"), |emitter| {
            reader.seek_to(start_pos + sub_header_offset)?;
            read_sub_header(reader, emitter)?;

            let sub_start_offset = reader.pos()?;
            llir::read_instrs(reader, emitter, instr_format, sub_start_offset, sub_end_offset)
        })?;


        if subs.insert(name.clone(), instrs).is_some() {
            emitter.emit({
                warning!("multiple subs with the name '{name}'! Only one will appear in the output.")
            }).ignore();
        }
    }

    let binary_filename = Some(reader.display_filename().to_string());
    Ok(StackEclFile { subs, anim_list, ecli_list, binary_filename })
}

fn read_include_section(
    reader: &mut BinReader,
    emitter: &impl Emitter,
    magic: &str,
) -> ReadResult<Vec<Sp<String>>> {
    reader.expect_magic(emitter, magic)?;
    emitter.chain_with(|f| write!(f, "in {magic} list"), |emitter| {
        let count = reader.read_u32()?;
        read_string_list(reader, emitter, count as usize)
    })
}

fn read_string_list(
    reader: &mut BinReader,
    emitter: &impl Emitter,
    count: usize,
) -> ReadResult<Vec<Sp<String>>> {
    let mut num_bytes_read = 0;

    let strings = (0..count).map(|_| {
        let encoded = reader.read_cstring_blockwise(1)?;
        num_bytes_read += encoded.len() + 1;

        let string = encoded.decode(DEFAULT_ENCODING).map_err(|e| emitter.emit(e))?;
        Ok(sp!(string))
    }).collect::<Result<Vec<_>, _>>()?;

    let padding = reader.align_to(num_bytes_read, 4)?;
    if padding.into_iter().any(|b| b != 0) {
        emitter.emit(warning!("unexpected data in padding after last string")).ignore();
    }

    Ok(strings)
}

fn read_sub_header(
    reader: &mut BinReader,
    emitter: &impl Emitter,
) -> ReadResult<()> {
    reader.expect_magic(emitter, "ECLH")?;
    let data = reader.read_u32s(3)?;
    let expected_data = &[0x10, 0, 0];
    for (index, data_dword, &expected_dword) in zip!(0.., data, expected_data) {
        if data_dword != expected_dword {
            emitter.emit(warning!("unexpected data in sub header dword {index} (value: {data_dword:#x}")).ignore();
        }
    }
    Ok(())
}

// =============================================================================

fn write(
    writer: &mut BinWriter,
    emitter: &impl Emitter,
    game: Game,
    ecl: &StackEclFile,
) -> WriteResult {
    let hooks = game_hooks(game);
    let instr_format = hooks.instr_format();

    let start_pos = writer.pos()?;
    writer.write_all(b"SCPT")?;
    writer.write_i16(1)?;

    // we'll come back to these
    let include_sizes_pos = writer.pos()?;
    writer.write_i16(-1)?;  // include_length
    writer.write_i32(-1)?;  // include_offset

    writer.write_u32(0)?;
    writer.write_u32(ecl.subs.len() as u32)?;
    writer.write_u32s(&[0; 4])?;

    let include_pos = writer.pos()?;
    let include_offset = include_pos - start_pos;

    write_include_section(writer, emitter, "ANIM", ecl.anim_list.iter().map(|s| sp!(s.span => s.as_str())))?;
    write_include_section(writer, emitter, "ECLI", ecl.ecli_list.iter().map(|s| sp!(s.span => s.as_str())))?;

    let sub_list_pos = writer.pos()?;
    let include_length = sub_list_pos - include_pos;

    writer.seek_to(include_sizes_pos)?;
    match u16::try_from(include_length) {
        Ok(include_length) => writer.write_u16(include_length)?,
        Err(_) => return Err(emitter.emit(error!("include section is too large to fit! ({include_length:#x} bytes)"))),
    }
    writer.write_u32(u32::try_from(include_offset).unwrap())?;  // this is always 0x24

    writer.seek_to(sub_list_pos)?;
    writer.write_u32s(&vec![0xDEADBEEF; ecl.subs.len()])?;
    write_string_list(writer, emitter, ecl.subs.keys().map(|s| sp!(s.span => s.as_str())))?;

    let mut sub_offsets = vec![];
    for (sub_index, (name, instrs)) in ecl.subs.iter().enumerate() {
        sub_offsets.push(writer.pos()?);
        emitter.chain_with(|f| write!(f, "in sub {sub_index} ({name})"), |emitter| {
            write_sub_header(writer)?;
            llir::write_instrs(writer, emitter, instr_format, instrs)
        })?;
    }

    let end_pos = writer.pos()?;

    writer.seek_to(sub_list_pos)?;
    assert_eq!(sub_offsets.len(), ecl.subs.len());
    for offset in sub_offsets {
        writer.write_u32(offset as u32)?;
    }

    writer.seek_to(end_pos)?;
    Ok(())
}

fn write_include_section<'a>(
    writer: &mut BinWriter,
    emitter: &impl Emitter,
    magic: &str,
    strings: impl ExactSizeIterator<Item=Sp<&'a str>>,
) -> ReadResult<()> {
    writer.write_all(magic.as_bytes())?;
    emitter.chain_with(|f| write!(f, "in {magic} list"), |emitter| {
        writer.write_u32(strings.len() as u32)?;
        write_string_list(writer, emitter, strings)
    })
}

fn write_string_list<'a>(
    writer: &mut BinWriter,
    emitter: &impl Emitter,
    strings: impl ExactSizeIterator<Item=Sp<&'a str>>,
) -> ReadResult<()> {
    let mut num_bytes_written = 0;

    for string in strings {
        let encoded = Encoded::encode(&string, DEFAULT_ENCODING).map_err(|e| emitter.emit(e))?;
        writer.write_cstring(&encoded, 1)?;

        num_bytes_written += encoded.len() + 1;
    }
    writer.align_to(num_bytes_written, 4)?;

    Ok(())
}

fn write_sub_header(
    writer: &mut BinWriter,
) -> WriteResult<()> {
    writer.write_all(b"ECLH")?;
    writer.write_u32(0x10)?;  // offset to data
    writer.write_u32s(&[0; 2])
}

// =============================================================================

fn game_hooks(game: Game) -> Box<dyn LanguageHooks> {
    Box::new(ModernEclHooks { game })
}

// =============================================================================

struct ModernEclHooks { game: Game }

impl LanguageHooks for ModernEclHooks {
    fn language(&self) -> LanguageKey { LanguageKey::Ecl }

    fn has_registers(&self) -> bool { true }

    fn default_difficulty_mask(&self) -> Option<raw::DifficultyMask> {
        Some(crate::passes::semantics::time_and_difficulty::DEFAULT_DIFFICULTY_MASK_BYTE)
    }

    // offsets are written as relative in these files
    fn encode_label(&self, current_offset: raw::BytePos, dest_offset: raw::BytePos) -> raw::RawDwordBits {
        todo!()
    }
    fn decode_label(&self, current_offset: raw::BytePos, bits: raw::RawDwordBits) -> raw::BytePos {
        todo!()
    }

    fn general_use_regs(&self) -> EnumMap<ScalarType, Vec<RegId>> {
        todo!()
    }

    fn instr_disables_scratch_regs(&self, opcode: u16) -> Option<HowBadIsIt> {
        todo!()
    }

    fn difficulty_register(&self) -> Option<RegId> {
        Some(RegId::from(-9959))
    }

    fn instr_format(&self) -> &dyn InstrFormat { self }
}

impl InstrFormat for ModernEclHooks {
    fn instr_header_size(&self) -> usize { 16 }

    fn has_terminal_instr(&self) -> bool { false }

    fn read_instr(&self, f: &mut BinReader, emitter: &dyn Emitter) -> ReadResult<ReadInstr> {
        let time = f.read_i32()?;
        let opcode = f.read_u16()?;  // i16 according to zero but we always store as u16...
        let size = usize::from(f.read_u16()?);
        let param_mask = f.read_u16()?;
        let difficulty = f.read_u8()?;
        let arg_count = f.read_u8()?;
        let pop = f.read_u8()?;
        for padding_byte_index in 0..3 {
            let byte = f.read_u8()?;
            if byte != 0 {
                emitter.as_sized().emit(warning!("nonzero data in padding byte {padding_byte_index} will be lost (value: {byte:#x})")).ignore();
            }
        }

        let args_size = size.checked_sub(self.instr_header_size()).ok_or_else(|| {
            emitter.as_sized().emit(error!("bad instruction size ({size} < {})", self.instr_header_size()))
        })?;
        let args_blob = f.read_byte_vec(args_size)?;

        Ok(ReadInstr::Instr(RawInstr {
            time, opcode, param_mask, difficulty, pop, args_blob,
            arg_count: Some(arg_count),
            extra_arg: None,
        }))
    }

    fn write_instr(&self, f: &mut BinWriter, _: &dyn Emitter, instr: &RawInstr) -> WriteResult {
        f.write_i32(instr.time)?;
        f.write_u16(instr.opcode)?;
        f.write_u16(self.instr_size(instr) as _)?;
        f.write_u16(instr.param_mask)?;
        f.write_u8(instr.difficulty)?;
        f.write_u8(instr.arg_count.unwrap())?;
        f.write_u8(instr.pop)?;
        f.write_all(&[0; 3])?;
        f.write_all(&instr.args_blob)
    }

    fn write_terminal_instr(&self, _: &mut BinWriter, _: &dyn Emitter) -> WriteResult {
        panic!("stack ECL has no terminal instr")
    }
}
