use std::collections::{BTreeMap, BTreeSet, btree_map};
use std::convert::TryFrom;

use crate::ast;
use crate::io::{BinRead, BinWrite, BinReader, BinWriter, ReadResult, WriteResult};
use crate::diagnostic::{Diagnostic, Emitter};
use crate::ident::Ident;
use crate::error::{GatherErrorIteratorExt, ErrorReported};
use crate::game::Game;
use crate::llir::{self, ReadInstr, RawInstr, InstrFormat};
use crate::pos::{Sp, Span};
use crate::context::CompilerContext;
use crate::passes::DecompileKind;
use crate::meta::{self, Meta, ToMeta};

// =============================================================================

/// Game-independent representation of a MSG file.
#[derive(Debug, Clone, PartialEq)]
pub struct MsgFile {
    pub script_table: Vec<ScriptTableEntry>,
    pub scripts: BTreeMap<Ident, Vec<RawInstr>>,
    /// Filename of a read binary file, for display purposes only.
    binary_filename: Option<String>,
}

impl MsgFile {
    pub fn decompile_to_ast(&self, game: Game, ctx: &mut CompilerContext<'_>, decompile_kind: DecompileKind) -> Result<ast::Script, ErrorReported> {
        let emitter = ctx.emitter.while_decompiling(self.binary_filename.as_deref());
        decompile(self, &emitter, &*game_format(game), ctx, decompile_kind)
    }

    pub fn compile_from_ast(game: Game, script: &ast::Script, ctx: &mut CompilerContext<'_>) -> Result<Self, ErrorReported> {
        // compile(&*game_format(game), script, ctx)
        unimplemented!()
    }

    pub fn write_to_stream(&self, w: &mut BinWriter, game: Game) -> WriteResult {
        unimplemented!()
        // let emitter = w.emitter();
        // write_msg(w, &emitter, &*game_format(game), self)
    }

    pub fn read_from_stream(r: &mut BinReader, game: Game) -> ReadResult<Self> {
        let emitter = r.emitter();
        read_msg(r, &emitter, &*game_format(game))
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct ScriptTableEntry {
    /// Offset of script, from beginning of file.
    pub script: Ident,
    /// Unknown.  First appears in PoFV.
    pub flags: u32,
}

// =============================================================================

/// An alternative structure closer to the Meta representation.
#[derive(Debug, Clone, PartialEq)]
struct SparseScriptTable {
    /// The script table is sparsely filled and could potentially have empty entries after the
    /// last full one, so we must store its true length.
    table_len: u32,
    table: BTreeMap<u32, ScriptTableEntry>,
    default: Option<ScriptTableEntry>,
}

impl SparseScriptTable {
    fn make_meta(&self) -> meta::Fields {
        let mut builder = Meta::make_object();

        // (if this overflows, the table is so large that we should have had trouble reading it)
        let auto_len = self.table.keys().last().map(|&max| max + 1).unwrap_or(0);
        assert!(self.table_len >= auto_len);
        if self.table_len > auto_len {
            builder.field("table_len", &self.table_len);
        };

        builder.field("table", &{
            let mut inner = Meta::make_object();
            for (&id, entry) in &self.table {
                inner.field(format!("{}", id), entry);
            }
            inner.opt_field("default", self.default.as_ref());
            inner.build()
        });

        builder.build_fields()
    }
}

impl ToMeta for ScriptTableEntry {
    fn to_meta(&self) -> Meta {
        Meta::make_object()
            .field("script", &self.script)
            .field_default("flags", &self.flags, &0)
            .build()
    }
}

// =============================================================================

fn decompile(
    msg: &MsgFile,
    emitter: &impl Emitter,
    instr_format: &dyn InstrFormat,
    ctx: &mut CompilerContext,
    decompile_kind: DecompileKind,
) -> Result<ast::Script, ErrorReported> {
    let sparse_script_table = sparsify_script_table(&msg.script_table);

    let mut raiser = llir::Raiser::new(&ctx.emitter);
    let mut items = vec![sp!(ast::Item::Meta {
        keyword: sp!(token![meta]),
        ident: None,
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

fn sparsify_script_table(script_table: &[ScriptTableEntry]) -> SparseScriptTable {
    let table_len = u32::try_from(script_table.len()).expect("table len was initially read as u32 but...!?");
    let default = None;
    let table = script_table.iter().enumerate().map(|(id, entry)| {
        (id as u32, entry.clone())
    }).collect();
    SparseScriptTable { table_len, table, default }
}

//
// #[cfg(nope)]
// fn process_raw_script_table(raw_entries: &[RawScriptTableEntry]) -> ProcessScriptTableOutput {
//     let counts = get_counts(raw_entries.iter());
//
//     let convert_entry = {
//         let offset_labels = label_offsets.iter()
//             .map(|(ident, &offset)| (offset, ident.clone()))
//             .collect::<BTreeMap<_, _>>();
//
//         move |&ScriptTableEntry { offset, flags }| {
//             let label = offset_labels[&offset].clone();
//             LabeledScriptTableEntry { label, flags }
//         }
//     };
//
//     // if there's a single obvious default, use it.
//     let use_default = counts.values().filter(|&&x| x > 1).count() == 1;
//     let default = if use_default {
//         let entry = counts.iter().filter(|&(_, &count)| count > 1).next().unwrap().0;
//         Some(convert_entry(entry))
//     } else {
//         None
//     };
//
//     // erase defaults
//     let table = {
//         raw_entries.iter().map(convert_entry).enumerate()
//             .filter(|(i, entry)| match default {
//                 Some(default) => entry != default || i == offset_first_indices[&default.offset],
//                 None => true,
//             })
//             .map(|(i, entry)| (i as u32, entry))
//             .collect()
//     };
//
//     let table_len = raw_entries.len() as u32;
//     let table = LabeledScriptTable { table_len, table, default };
//     ProcessScriptTableOutput { table, label_offsets }
// }
//
// fn get_counts<T: Eq + Ord>(items: impl IntoIterator<Item=T>) -> BTreeMap<T, u32> {
//     let mut out = BTreeMap::new();
//     for x in items {
//         *out.entry(x).or_insert(0) += 1;
//     }
//     out
// }

// =============================================================================

#[cfg(nope)]
fn compile(
    instr_format: &dyn InstrFormat,
    ast: &ast::Script,
    ctx: &mut CompilerContext,
) -> Result<MsgFile, ErrorReported> {
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

    let mut scripts_by_id = BTreeMap::<u32, (Span, &ast::Block)>::new();

    let mut next_auto_id = 0_i32;
    for item in ast.items.iter() {
        match &item.value {
            ast::Item::AnmScript { number, ident, code, .. } => {
                // scripts with no number automatically use the next integer
                let id = number.map(|sp| sp.value).unwrap_or(next_auto_id);
                next_auto_id = id + 1;

                if id < 0 {
                    let span = number.expect("since it's the first negative it must be explicit!").span;
                    return Err(ctx.emitter.emit(error!(
                        message("unexpected negative script id in MSG file"),
                        primary(span, "negative id in MSG file")
                    )));
                }

                match scripts_by_id.entry(id as u32) {
                    btree_map::Entry::Occupied(e) => return Err(ctx.emitter.emit(error!(
                        message("multiple scripts with same ID number"),
                        secondary(e.get().0, "original script here"),
                        primary(ident, "script with duplicate id"),
                    ))),
                    btree_map::Entry::Vacant(e) => e.insert((ident.span, code)),
                };
            },
            ast::Item::Meta { keyword, .. } => return Err(ctx.emitter.emit(error!(
                message("unexpected '{}' in MSG file", keyword),
                primary(keyword, "not valid in MSG files"),
            ))),
            ast::Item::ConstVar { .. } => {},

            ast::Item::Func { .. } => return Err(ctx.emitter.emit(unsupported(&item.span))),
        }
    }

    let script_table_len = scripts_by_id.keys().max().map_or(0, |max| max + 1);
    Ok(MsgFile {
        script_table_len,
        scripts: scripts_by_id.into_iter().map(|(id, (_, script_ast))| {
            llir::lower_sub_ast_to_instrs(instr_format, &script_ast.0, ctx)
                .map(|compiled| (id, compiled))
        }).collect_with_recovery()?,
        binary_filename: None,
    })
}


fn unsupported(span: &crate::pos::Span) -> Diagnostic {
    error!(
        message("feature not supported by format"),
        primary(span, "not supported by MSG files"),
    )
}

// =============================================================================

fn read_msg(
    reader: &mut BinReader,
    emitter: &impl Emitter,
    instr_format: &dyn InstrFormat,
) -> ReadResult<MsgFile> {
    let start_pos = reader.pos()?;

    let script_table_len = reader.read_u32()?;
    let script_table = {
        (0..script_table_len).map(|_| Ok(RawScriptTableEntry {
            offset: reader.read_u32()? as u64,
            flags: 0,
        })).collect::<ReadResult<Vec<_>>>()?
    };
    eprintln!("{:?}", script_table);

    // The script offset table tends to look like
    //
    //    [52, 1364, 52, 52, 52, 52, 52, 52, 52, 52, 2376, 1516]
    //
    // i.e. a script may be reused for multiple IDs, their offsets may not be in order,
    // and one script tends to be used as a filler.
    //
    // Get the sorted
    let sorted_script_offsets = script_table.iter().map(|entry| entry.offset).collect::<BTreeSet<_>>();
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

    let script_table = script_table.into_iter().map(|RawScriptTableEntry { offset, flags }| {
        ScriptTableEntry { script: script_names[&offset].clone(), flags }
    }).collect();

    let binary_filename = Some(reader.display_filename().to_owned());
    Ok(MsgFile { script_table, scripts, binary_filename })
}

#[derive(Debug)]
struct RawScriptTableEntry {
    offset: u64,
    flags: u32,
}

fn generate_script_names(raw_entries: &[RawScriptTableEntry]) -> BTreeMap<u64, Ident> {
    // name each offset after the first script to use it
    let offset_first_indices = get_first_indices(raw_entries.iter().map(|entry| entry.offset));
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

#[cfg(nope)]
fn write_msg(
    w: &mut BinWriter,
    emitter: &impl Emitter,
    instr_format: &dyn InstrFormat,
    msg: &MsgFile,
) -> WriteResult {
    let start_pos = w.pos()?;

    w.write_u32(msg.script_table_len as _)?;

    let script_offsets_pos = w.pos()?;
    for _ in 0..msg.script_table_len {
        w.write_u32(0)?;
    }

    // The script offset table tends to look like
    //    [52, 1364, 52, 52, 52, 52, 52, 52, 52, 52, 1516, 2376]
    // i.e. the first script is used as a filler for all of the others
    let mut default_script_offset = None;
    let mut script_offsets = vec![None; msg.script_table_len as usize];
    for (&id, script) in &msg.scripts {
        let script_offset = w.pos()? - start_pos;
        default_script_offset = default_script_offset.or(Some(script_offset));

        script_offsets[id as usize] = Some(script_offset);
        emitter.chain_with(|f| write!(f, "script id {}", id), |emitter| {
            llir::write_instrs(w, emitter, instr_format, script)
        })?;
    }

    if default_script_offset.is_none() && msg.script_table_len > 0 {
        emitter.emit(warning!("script table has no entries to use as a default!")).ignore();
    }
    let default_script_offset = default_script_offset.unwrap_or(0);

    let end_pos = w.pos()?;

    w.seek_to(script_offsets_pos)?;
    assert_eq!(script_offsets.len(), msg.script_table_len as usize);
    for offset in script_offsets {
        w.write_u32(offset.unwrap_or(default_script_offset) as u32)?;
    }
    w.seek_to(end_pos)?;
    Ok(())
}

// =============================================================================

fn game_format(game: Game) -> Box<dyn InstrFormat> {
    match game {
        | Game::Th06 | Game::Th07 | Game::Th08
        => Box::new(InstrFormat06),

        _ => unimplemented!("msg InstrFormat"),
    }
}

pub fn game_core_mapfile(game: Game) -> &'static str {
    match game {
        | Game::Th06 | Game::Th07
        => include_str!("../../map/core/th06.msgm"),

        | Game::Th08
        => include_str!("../../map/core/th08.msgm"),

        _ => unimplemented!("msg mapfiles"),
    }
}

// =============================================================================

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

    fn write_instr(&self, f: &mut BinWriter, emitter: &dyn Emitter, instr: &RawInstr) -> WriteResult {
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
