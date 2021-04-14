use std::collections::{BTreeMap, BTreeSet};

use crate::ast;
use crate::io::{BinRead, BinWrite, BinReader, BinWriter, ReadResult, WriteResult};
use crate::diagnostic::{Diagnostic, Emitter};
use crate::ident::Ident;
use crate::error::{GatherErrorIteratorExt, ErrorReported};
use crate::game::Game;
use crate::llir::{self, ReadInstr, RawInstr, InstrFormat};
use crate::pos::Sp;
use crate::context::CompilerContext;
use crate::passes::DecompileKind;
use crate::meta::{self, Meta, ToMeta, FromMeta, FromMetaError};
use crate::value::ScalarValue;

use indexmap::IndexMap;

// =============================================================================

/// Game-independent representation of a MSG file.
#[derive(Debug, Clone, PartialEq)]
pub struct MsgFile {
    pub dense_table: Vec<ScriptTableEntry>,
    pub scripts: IndexMap<Ident, Vec<RawInstr>>,
    /// Filename of a read binary file, for display purposes only.
    binary_filename: Option<String>,
}

impl MsgFile {
    pub fn decompile_to_ast(&self, game: Game, ctx: &mut CompilerContext<'_>, decompile_kind: DecompileKind) -> Result<ast::Script, ErrorReported> {
        let emitter = ctx.emitter.while_decompiling(self.binary_filename.as_deref());
        decompile(self, &emitter, &game_format(game), ctx, decompile_kind)
    }

    pub fn compile_from_ast(game: Game, script: &ast::Script, ctx: &mut CompilerContext<'_>) -> Result<Self, ErrorReported> {
        compile(&game_format(game), script, ctx)
    }

    pub fn write_to_stream(&self, w: &mut BinWriter, game: Game) -> WriteResult {
        let emitter = w.emitter();
        write_msg(w, &emitter, &game_format(game), self)
    }

    pub fn read_from_stream(r: &mut BinReader, game: Game) -> ReadResult<Self> {
        let emitter = r.emitter();
        read_msg(r, &emitter, &game_format(game))
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct ScriptTableEntry {
    /// Offset of script, from beginning of file.
    pub script: Sp<ScriptTableOffset>,
    /// Unknown.  First appears in PoFV.
    pub flags: Sp<u32>,
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum ScriptTableOffset {
    Name(Ident),
    Zero,
}

impl Default for ScriptTableEntry {
    fn default() -> Self {
        ScriptTableEntry { script: sp!(ScriptTableOffset::Zero), flags: sp!(0) }
    }
}

// =============================================================================

/// An alternative structure closer to the Meta representation.
#[derive(Debug, Clone, PartialEq)]
struct SparseScriptTable {
    /// The script table is sparsely filled and could potentially have empty entries after the
    /// last full one, so we must store its true length.
    table_len: Sp<u32>,
    table: IndexMap<Sp<u32>, ScriptTableEntry>,
    default: ScriptTableEntry,
}

impl SparseScriptTable {
    fn make_meta(&self) -> meta::Fields {
        let mut builder = Meta::make_object();

        // suppress table_len if it isn't necessary
        let auto_len = sparse_table_implicit_len(&self.table);
        assert!(self.table_len >= auto_len);
        if self.table_len > auto_len {
            builder.field("table_len", &self.table_len.value);
        };

        builder.field("table", &{
            let mut inner = Meta::make_object();
            for (&id, entry) in &self.table {
                inner.field(format!("{}", id), entry);
            }
            inner.field_default("default", &self.default, &Default::default());
            inner.build()
        });

        builder.build_fields()
    }

    fn from_fields(fields: &Sp<meta::Fields>) -> Result<Self, FromMetaError<'_>> {
        meta::ParseObject::scope(fields, |m| {
            let ident_map: IndexMap<Sp<Ident>, ScriptTableEntry> = m.expect_field("table")?;

            let mut default = None;
            let mut int_map = IndexMap::new();
            for (key, value) in ident_map {
                if &key == "default" {
                    default = Some(value);
                } else if let Ok(num) = key.as_str().parse() {
                    let old_value = int_map.insert(sp!(key.span => num), value);
                    assert!(old_value.is_none(), "duplicate integer key; was one non-canonical?!");
                } else {
                    return Err(FromMetaError::BadKey {
                        expected: "an integer or 'default'",
                        got: key,
                    });
                }
            }
            let default = default.unwrap_or_default();

            let table_len = m.get_field("table_len")?.unwrap_or_else(|| {
                sp!(fields.span => sparse_table_implicit_len(&int_map))
            });
            Ok(SparseScriptTable { table_len, table: int_map, default })
        })
    }

    fn densify(&self) -> Vec<ScriptTableEntry> {
        (0..self.table_len.value)
            .map(|index| {
                self.table.get(&index).unwrap_or_else(|| &self.default).clone()
            }).collect()
    }
}

impl ToMeta for ScriptTableEntry {
    fn to_meta(&self) -> Meta {
        Meta::make_object()
            .field("script", &self.script.value)
            .field_default("flags", &self.flags.value, &0)
            .build()
    }
}

impl FromMeta<'_> for ScriptTableEntry {
    fn from_meta(meta: &'_ Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
        meta.parse_object(|m| {
            Ok(ScriptTableEntry {
                script: m.expect_field("script")?,
                flags: m.get_field("flags")?.unwrap_or(sp!(meta.span => 0)),
            })
        })
    }
}

impl ToMeta for ScriptTableOffset {
    fn to_meta(&self) -> Meta {
        match self {
            ScriptTableOffset::Name(ident) => ident.to_meta(),
            ScriptTableOffset::Zero => 0.to_meta(),
        }
    }
}

impl FromMeta<'_> for ScriptTableOffset {
    fn from_meta(meta: &'_ Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
        match meta.parse()? {
            ScalarValue::String(_) => Ok(ScriptTableOffset::Name(meta.parse()?)),
            ScalarValue::Int(0) => Ok(ScriptTableOffset::Zero),
            _ => Err(FromMetaError::expected("a string holding a valid identifier, or a literal 0", meta)),
        }
    }
}

// =============================================================================

fn decompile(
    msg: &MsgFile,
    emitter: &impl Emitter,
    format: &FileFormat,
    ctx: &mut CompilerContext,
    decompile_kind: DecompileKind,
) -> Result<ast::Script, ErrorReported> {
    let instr_format = &*format.instr_format();

    let sparse_script_table = sparsify_script_table(&msg.dense_table);

    let mut raiser = llir::Raiser::new(&ctx.emitter);
    let mut items = vec![sp!(ast::Item::Meta {
        keyword: sp!(token![meta]),
        fields: sp!(sparse_script_table.make_meta()),
    })];
    items.extend(msg.scripts.iter().map(|(ident, instrs)| {
        let code = raiser.raise_instrs_to_sub_ast(emitter, instr_format, instrs, &ctx.defs)?;

        Ok(sp!(ast::Item::AnmScript {
            number: None,
            ident: sp!(ident.clone()),
            code: ast::Block(code),
            keyword: sp!(()),
        }))
    }).collect_with_recovery::<Vec<_>>()?);

    let mut script = ast::Script {
        mapfiles: ctx.mapfiles_to_ast(),
        image_sources: vec![],
        items,
    };
    crate::passes::postprocess_decompiled(&mut script, ctx, decompile_kind)?;
    Ok(script)
}

fn sparsify_script_table(dense_table: &[ScriptTableEntry]) -> SparseScriptTable {
    let counts = get_counts(dense_table.iter());

    // get first index of all nonzero entries
    let ident_first_indices = {
        get_first_indices(dense_table.iter().map(|entry| &entry.script))
            .into_iter().collect::<BTreeMap<_, _>>()
    };

    // if there's a single obvious default, use it.
    let use_default = counts.values().filter(|&&x| x > 1).count() == 1;
    let default = if use_default {
        let &entry = counts.iter().filter(|&(_, &count)| count > 1).next().unwrap().0;
        entry.clone()
    } else {
        Default::default()
    };

    // erase defaults
    let table = {
        dense_table.iter().cloned().enumerate()
            .filter(|&(i, ref entry)| {
                // suppress matches of the default unless they name it
                entry != &default || {
                    i == ident_first_indices[&default.script]
                    && matches!(default.script.value, ScriptTableOffset::Name(_))
                }
            })
            .map(|(i, entry)| (sp!(i as u32), entry))
            .collect()
    };

    let table_len = sp!(dense_table.len() as u32);
    SparseScriptTable { table_len, table, default }
}

fn get_counts<T: Eq + Ord>(items: impl IntoIterator<Item=T>) -> BTreeMap<T, u32> {
    let mut out = BTreeMap::new();
    for x in items {
        *out.entry(x).or_insert(0) += 1;
    }
    out
}

// =============================================================================

fn compile(
    format: &FileFormat,
    ast: &ast::Script,
    ctx: &mut CompilerContext,
) -> Result<MsgFile, ErrorReported> {
    let instr_format = &*format.instr_format();
    let ast = {
        let mut ast = ast.clone();

        crate::passes::resolve_names::assign_res_ids(&mut ast, ctx)?;
        crate::passes::resolve_names::run(&ast, ctx)?;
        crate::passes::type_check::run(&ast, ctx)?;
        crate::passes::evaluate_const_vars::run(ctx)?;
        crate::passes::const_simplify::run(&mut ast, ctx)?;
        crate::passes::desugar_blocks::run(&mut ast, ctx)?;
        ast
    };

    let emit = |e| ctx.emitter.emit(e);
    let (meta, script_code) = {
        // FIXME: copypasta with std.rs  (both languages appear to want very similar things)
        let (mut found_meta, mut script_code) = (None, IndexMap::new());
        for item in ast.items.iter() {
            match &item.value {
                ast::Item::Meta { keyword: sp_pat![kw_span => token![meta]], fields: meta } => {
                    if let Some((prev_kw_span, _)) = found_meta.replace((kw_span, meta)) {
                        return Err(emit(error!(
                            message("'meta' supplied multiple times"),
                            secondary(prev_kw_span, "previously supplied here"),
                            primary(kw_span, "duplicate 'meta'"),
                        )));
                    }
                },
                ast::Item::Meta { keyword, .. } => return Err(emit(error!(
                    message("unexpected '{}' in MSG file", keyword),
                    primary(keyword, "not valid in MSG files"),
                ))),
                ast::Item::AnmScript { number: Some(number), .. } => return Err(emit(error!(
                    message("unexpected numbered script in MSG file"),
                    primary(number, "unexpected number"),
                ))),
                ast::Item::AnmScript { number: None, ident, code, .. } => {
                    match script_code.entry(ident.clone()) {
                        indexmap::map::Entry::Vacant(e) => { e.insert(code); },
                        indexmap::map::Entry::Occupied(prev) => return Err(emit(error!(
                            message("redefinition of script '{}'", ident),
                            primary(ident, "this defines a script called '{}'...", ident),
                            secondary(prev.key(), "...but '{}' was already defined here", ident),
                        ))),
                    }
                },
                ast::Item::ConstVar { .. } => {},
                ast::Item::Func { .. } => return Err(emit(unsupported(&item.span))),
            }
        }

        match found_meta {
            Some((_, meta)) => (meta, script_code),
            None => return Err(emit(error!("missing 'meta' section"))),
        }
    };
    let sparse_table: SparseScriptTable = {
        SparseScriptTable::from_fields(meta).map_err(|e| ctx.emitter.emit(e))?
    };

    let scripts = script_code.iter().map(|(name, code)| {
        let instrs = crate::llir::lower_sub_ast_to_instrs(instr_format, &code.0, ctx)?;
        Ok((name.value.clone(), instrs))
    }).collect_with_recovery()?;

    let unused_table_keys = {
        sparse_table.table.keys().copied()
            .filter(|&key| key >= sparse_table.table_len).collect::<Vec<_>>()
    };
    if !unused_table_keys.is_empty() {
        let mut diag = warning!(
            message("unused script table entry"),
            secondary(sparse_table.table_len, "unused due to this length"),
        );
        for key in unused_table_keys {
            diag.primary(key.span, format!("unused table entry"));
        };
        ctx.emitter.emit(diag).ignore();
    }

    let used_scripts = {
        std::iter::once(sparse_table.default.clone())
            .chain(sparse_table.table.values().cloned())
            .filter_map(|entry| match entry.script.value {
                ScriptTableOffset::Zero => None,
                ScriptTableOffset::Name(ref ident) => Some(ident.clone()),
            }).collect::<BTreeSet<_>>()
    };
    for name in script_code.keys() {
        if !used_scripts.contains(&name.value) {
            ctx.emitter.emit(warning!(
                message("unused script '{}'", name),
                primary(name, "unused script"),
            )).ignore();
        }
    }

    Ok(MsgFile {
        dense_table: sparse_table.densify(),
        scripts,
        /// Filename of a read binary file, for display purposes only.
        binary_filename: None,
    })
}

fn unsupported(span: &crate::pos::Span) -> Diagnostic {
    error!(
        message("feature not supported by format"),
        primary(span, "not supported by MSG files"),
    )
}

fn sparse_table_implicit_len(table: &IndexMap<Sp<u32>, ScriptTableEntry>) -> u32 {
    table.keys().copied().max().map_or(0, |max| max.value + 1)
}

// =============================================================================

fn read_msg(
    reader: &mut BinReader,
    emitter: &impl Emitter,
    format: &FileFormat,
) -> ReadResult<MsgFile> {
    let instr_format = &*format.instr_format();

    let start_pos = reader.pos()?;

    let script_table_len = reader.read_u32()?;
    let script_table = {
        (0..script_table_len).map(|_| {
            Ok(RawScriptTableEntry {
                offset: reader.read_u32()? as u64,
                flags: if format.table_has_flags() {
                    reader.read_u32()?
                } else {
                    0
                },
            })
        }).collect::<ReadResult<Vec<_>>>()?
    };

    // The script offset table tends to look like
    //
    //    [52, 1364, 52, 52, 52, 52, 52, 52, 52, 52, 2376, 1516]
    //
    // i.e. a script may be reused for multiple IDs, their offsets may not be in order,
    // and one script tends to be used as a filler.
    let sorted_script_offsets = {
        script_table.iter().map(|entry| entry.offset)
            .filter(|&x| x > 0).collect::<BTreeSet<_>>()
    };
    let script_names = generate_script_names(&script_table);

    let mut end_offsets = sorted_script_offsets.iter().copied().skip(1);
    let scripts = sorted_script_offsets.iter().map(|&script_offset| {
        // note: for the last script end_pos is None and we read to EOF.
        let script_pos = start_pos + script_offset;
        let end_pos = end_offsets.next().map(|offset| start_pos + offset);
        reader.seek_to(script_pos)?;

        let ident = script_names[&script_offset].clone();
        let script = emitter.chain_with(|f| write!(f, "{}", ident), |emitter| {
            llir::read_instrs(reader, emitter, instr_format, script_pos, end_pos)
        })?;
        Ok((ident, script))
    }).collect_with_recovery()?;

    let dense_table = script_table.into_iter().map(|RawScriptTableEntry { offset, flags }| {
        ScriptTableEntry {
            script: match offset {
                0 => sp!(ScriptTableOffset::Zero),
                _ => sp!(ScriptTableOffset::Name(script_names[&offset].clone())),
            },
            flags: sp!(flags),
        }
    }).collect();

    let binary_filename = Some(reader.display_filename().to_owned());
    Ok(MsgFile { dense_table, scripts, binary_filename })
}

#[derive(Debug)]
struct RawScriptTableEntry {
    offset: u64,
    flags: u32,
}

fn generate_script_names(raw_entries: &[RawScriptTableEntry]) -> BTreeMap<u64, Ident> {
    // name each offset after the first script to use it
    let offset_first_indices = get_first_indices({
        raw_entries.iter().map(|entry| entry.offset)
            .filter(|&offset| offset != 0)  // but don't assign a name to offset 0!
    });
    offset_first_indices.iter().map(|&(offset, index)| {
        let ident = format!("script{}", index).parse::<Ident>().unwrap();
        (offset, ident)
    }).collect::<BTreeMap<_, _>>()
}

/// Get the first index that each value appears at, in order of first appearance.
fn get_first_indices<T: Eq + Ord + Clone>(items: impl IntoIterator<Item=T>) -> Vec<(T, usize)> {
    let mut seen = BTreeSet::new();
    let mut out = vec![];
    for (i, x) in items.into_iter().enumerate() {
        if seen.insert(x.clone()) {
            out.push((x, i));
        }
    }
    out
}

// =============================================================================

fn write_msg(
    w: &mut BinWriter,
    emitter: &impl Emitter,
    format: &FileFormat,
    msg: &MsgFile,
) -> WriteResult {
    let instr_format = &*format.instr_format();

    let start_pos = w.pos()?;

    w.write_u32(msg.dense_table.len() as _)?;

    let script_offsets_pos = w.pos()?;
    for _ in 0..msg.dense_table.len() {
        w.write_u32(0)?;
        if format.table_has_flags() {
            w.write_u32(0)?;
        }
    }

    let mut script_offsets = BTreeMap::new();
    for (ident, script) in &msg.scripts {
        let script_offset = w.pos()? - start_pos;

        script_offsets.insert(ident.clone(), script_offset);
        emitter.chain_with(|f| write!(f, "script {}", ident), |emitter| {
            llir::write_instrs(w, emitter, instr_format, script)
        })?;
    }
    assert_eq!(script_offsets.len(), msg.scripts.len());

    let end_pos = w.pos()?;

    w.seek_to(script_offsets_pos)?;
    for entry in &msg.dense_table {
        let script_offset = match entry.script.value {
            ScriptTableOffset::Zero => 0,
            ScriptTableOffset::Name(ref ident) => *script_offsets.get(ident).ok_or_else(|| {
                emitter.emit(error!(
                    message("invalid script '{}'", ident),
                    primary(entry.script, "no such script"),
                ))
            })?,
        };

        w.write_u32(script_offset as u32)?;
        if format.table_has_flags() {
            w.write_u32(entry.flags.value)?;
        } else {
            if entry.flags.value != 0 {
                emitter.emit(warning!(
                    message("script flags are not supported in this game"),
                    primary(entry.flags, "has no effect in games before TH09"),
                )).ignore();
            }
        }
    }
    w.seek_to(end_pos)?;
    Ok(())
}

// =============================================================================

fn game_format(game: Game) -> FileFormat {
    FileFormat { game }
}

pub fn game_core_mapfile(game: Game) -> crate::Eclmap {
    super::core_mapfiles::msg::core_signatures(game).to_mapfile(game)
}

// =============================================================================

struct FileFormat {
    game: Game,
}

impl FileFormat {
    fn table_has_flags(&self) -> bool {
        self.game >= Game::Th09
    }

    fn instr_format(&self) -> Box<dyn InstrFormat> {
        match self.game {
            | Game::Th06 | Game::Th07 | Game::Th08
            | Game::Th09 | Game::Th10 | Game::Alcostg | Game::Th11
            | Game::Th12 | Game::Th128 | Game::Th13
            | Game::Th14 | Game::Th143 | Game::Th15
            | Game::Th16 | Game::Th165 | Game::Th17
            => Box::new(InstrFormat06),

            | Game::Th095 | Game::Th125
            => unimplemented!("game does not have instructions!"),
        }
    }
}

/// MSG format, EoSD.
struct InstrFormat06;

impl InstrFormat for InstrFormat06 {
    fn intrinsic_opcode_pairs(&self) -> Vec<(llir::IntrinsicInstrKind, u16)> {
        vec![]  // msg is vapid
    }

    fn instr_header_size(&self) -> usize { 4 }

    fn read_instr(&self, f: &mut BinReader, _: &dyn Emitter) -> ReadResult<ReadInstr> {
        let time = match f.read_i16_or_eof() {
            Ok(Some(time)) => time,
            Ok(None) => return Ok(ReadInstr::EndOfFile),
            Err(e) => return Err(e),
        };

        let opcode = f.read_i8()?;
        let argsize = f.read_u8()?;
        let args_blob = f.read_byte_vec(argsize as usize)?;
        let instr = RawInstr { time: time as i32, opcode: opcode as u16, param_mask: 0, args_blob };

        // eprintln!("pos: {:#06x} - time: {:#06x} opcode: {:#04x} argsize: {:#04x} args: {:02x?}", pos, time as u16, opcode as u8, argsize, args_blob);
        if (time, opcode, argsize) == (0, 0, 0) {
            Ok(ReadInstr::MaybeTerminal(instr))
        } else {
            Ok(ReadInstr::Instr(instr))
        }
    }

    fn write_instr(&self, f: &mut BinWriter, _: &dyn Emitter, instr: &RawInstr) -> WriteResult {
        f.write_i16(instr.time as _)?;
        f.write_u8(instr.opcode as _)?;
        f.write_u8(instr.args_blob.len() as _)?;  // this version writes argsize rather than instr size
        f.write_all(&instr.args_blob)?;
        Ok(())
    }

    fn write_terminal_instr(&self, f: &mut BinWriter, _: &dyn Emitter) -> WriteResult {
        f.write_u32(0)
    }
}
