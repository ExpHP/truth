use std::io;
use std::collections::{BTreeMap, btree_map};

use crate::ast;
use crate::binary_io::{BinRead, BinWrite, ReadResult, WriteResult};
use crate::error::{GatherErrorIteratorExt, CompileError, SimpleError};
use crate::game::Game;
use crate::llir::{self, RawInstr, InstrFormat};
use crate::pos::{Span};
use crate::context::CompilerContext;
use crate::diagnostic::DiagnosticEmitter;
use crate::passes::DecompileKind;

// =============================================================================

/// Game-independent representation of a MSG file.
#[derive(Debug, Clone, PartialEq)]
pub struct MsgFile {
    /// The script table is sparsely filled and could potentially have empty entries after the
    /// last full one, so we must store its true length.
    pub script_table_len: u32,
    pub scripts: BTreeMap<u32, Vec<RawInstr>>,
}

impl MsgFile {
    pub fn decompile_to_ast(&self, game: Game, ctx: &CompilerContext<'_>, decompile_kind: DecompileKind) -> Result<ast::Script, SimpleError> {
        decompile(&*game_format(game), self, ctx, decompile_kind)
    }

    pub fn compile_from_ast(game: Game, script: &ast::Script, ctx: &mut CompilerContext<'_>) -> Result<Self, CompileError> {
        compile(&*game_format(game), script, ctx)
    }

    pub fn write_to_stream(&self, mut w: impl io::Write + io::Seek, game: Game, diagnostics: &DiagnosticEmitter) -> WriteResult {
        write_msg(diagnostics, &mut w, &*game_format(game), self)
    }

    pub fn read_from_stream(mut r: impl io::Read + io::Seek, game: Game, diagnostics: &DiagnosticEmitter) -> ReadResult<Self> {
        read_msg(diagnostics, &mut r, &*game_format(game))
    }
}

// =============================================================================

fn decompile(
    instr_format: &dyn InstrFormat,
    msg: &MsgFile,
    ctx: &CompilerContext,
    decompile_kind: DecompileKind,
) -> Result<ast::Script, SimpleError> {
    let mut raiser = llir::Raiser::new(&ctx.diagnostics);
    let mut script = ast::Script {
        mapfiles: ctx.mapfiles_to_ast(),
        image_sources: vec![],
        items: msg.scripts.iter().map(|(&id, instrs)| {
            let code = raiser.raise_instrs_to_sub_ast(instr_format, instrs, &ctx.defs)?;

            Ok(sp!(ast::Item::AnmScript {
                number: Some(sp!(id as _)),
                ident: sp!("main".parse().unwrap()),
                code: ast::Block(code),
                keyword: sp!(()),
            }))
        }).collect::<Result<_, SimpleError>>()?
    };
    crate::passes::postprocess_decompiled(&mut script, ctx, decompile_kind)?;
    Ok(script)
}

fn unsupported(span: &crate::pos::Span) -> CompileError {
    error!(
        message("feature not supported by format"),
        primary(span, "not supported by MSG files"),
    )
}

fn compile(
    instr_format: &dyn InstrFormat,
    ast: &ast::Script,
    ctx: &mut CompilerContext,
) -> Result<MsgFile, CompileError> {
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
                    return Err(error!(
                        message("unexpected negative script id in MSG file"),
                        primary(span, "negative id in MSG file")
                    ));
                }

                match scripts_by_id.entry(id as u32) {
                    btree_map::Entry::Occupied(e) => return Err(error!(
                        message("multiple scripts with same ID number"),
                        primary(ident, "script with duplicate id"),
                        secondary(e.get().0, "original script here"),
                    )),
                    btree_map::Entry::Vacant(e) => e.insert((ident.span, code)),
                };
            },
            ast::Item::Meta { keyword, .. } => return Err(error!(
                message("unexpected '{}' in MSG file", keyword),
                primary(keyword, "not valid in MSG files"),
            )),
            ast::Item::ConstVar { .. } => {},

            ast::Item::Func { .. } => return Err(unsupported(&item.span)),
        }
    }

    let script_table_len = scripts_by_id.keys().max().map_or(0, |max| max + 1);
    Ok(MsgFile {
        script_table_len,
        scripts: scripts_by_id.into_iter().map(|(id, (_, script_ast))| {
            let compiled = llir::lower_sub_ast_to_instrs(instr_format, &script_ast.0, ctx)?;
            Ok((id, compiled))
        }).collect_with_recovery()?,
    })
}

// =============================================================================

fn read_msg(
    diagnostics: &DiagnosticEmitter,
    reader: &mut dyn BinRead,
    instr_format: &dyn InstrFormat,
) -> ReadResult<MsgFile> {
    let start_pos = reader.pos()?;

    let script_table_len = reader.read_u32()?;
    let script_offsets = {
        (0..script_table_len).map(|_| reader.read_u32()).collect::<ReadResult<Vec<_>>>()?
    };

    // The script offset table tends to look like
    //
    //    [52, 1364, 52, 52, 52, 52, 52, 52, 52, 52, 1516, 2376]
    //
    // i.e. a script may be reused for multiple IDs, and the first script in particular is used as a filler
    let mut scripts = BTreeMap::new();
    let mut first_id_for_offsets = BTreeMap::new();  // maps offsets to first id they're associated with
    let mut default_offset = None;
    for (id, offset) in script_offsets.into_iter().enumerate() {
        // leave filler scripts out of the output object
        if default_offset == Some(offset) {
            continue;
        }

        default_offset.get_or_insert(offset);

        // Currently, when compiling we assume that the only script that ever gets reused is the first script.
        // (and we have no way to represent other methods of script reuse)
        //
        // Generate a warning if we're wrong, as we will fail to round trip this file.
        if let Some(old_id) = first_id_for_offsets.get(&offset) {
            warning!(
                "script id {} reuses script id {}, but due to language limitations, when recompiled it will reuse script {} instead",
                id, old_id, default_offset.unwrap(),
            );
        } else {
            first_id_for_offsets.insert(offset, id);
        }

        let script_pos = start_pos + offset as u64;
        reader.seek_to(script_pos)?;

        let script = llir::read_instrs(reader, instr_format, diagnostics, script_pos, None)?;
        scripts.insert(id as u32, script);
    }

    Ok(MsgFile { script_table_len, scripts })
}

fn write_msg(
    diagnostics: &DiagnosticEmitter,
    f: &mut dyn BinWrite,
    instr_format: &dyn InstrFormat,
    msg: &MsgFile,
) -> WriteResult {
    let start_pos = f.pos()?;

    f.write_u32(msg.script_table_len as _)?;

    let script_offsets_pos = f.pos()?;
    for _ in 0..msg.script_table_len {
        f.write_u32(0)?;
    }

    // The script offset table tends to look like
    //    [52, 1364, 52, 52, 52, 52, 52, 52, 52, 52, 1516, 2376]
    // i.e. the first script is used as a filler for all of the others
    let mut default_script_offset = None;
    let mut script_offsets = vec![None; msg.script_table_len as usize];
    for (&id, script) in &msg.scripts {
        let script_offset = f.pos()? - start_pos;
        default_script_offset = default_script_offset.or(Some(script_offset));

        script_offsets[id as usize] = Some(script_offset);
        llir::write_instrs(f, instr_format, script, diagnostics)?;
    }

    if default_script_offset.is_none() && msg.script_table_len > 0 {
        diagnostics.emit(warning!("script table has no entries to use as a default!"));
    }
    let default_script_offset = default_script_offset.unwrap_or(0);

    let end_pos = f.pos()?;

    f.seek_to(script_offsets_pos)?;
    assert_eq!(script_offsets.len(), msg.script_table_len as usize);
    for offset in script_offsets {
        f.write_u32(offset.unwrap_or(default_script_offset) as u32)?;
    }
    f.seek_to(end_pos)?;
    Ok(())
}

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

    fn read_instr(&self, f: &mut dyn BinRead, _: &DiagnosticEmitter) -> ReadResult<Option<RawInstr>> {
        let time = f.read_i16()?;
        let opcode = f.read_i8()?;
        let argsize = f.read_u8()?;

        // detect terminal instruction
        //
        // NOTE: *technically* this could be a valid instruction too.
        //       The *true* terminal instruction can only be identified by always reading up to the next script's offset.
        //       However, then this creates the problem that, for that last script (which ends at EoF) there is no "next offset"!
        //       So for now we're stuck treating (0, 0, 0) as a "hard" terminal instruction.
        if (time, opcode, argsize) == (0, 0, 0) {
            // eprintln!("pos: {:#06x} - time: {:#06x} opcode: {:#04x} argsize: {:#04x} args: []", pos, time as u16, opcode as u8, argsize);
            return Ok(None)
        }

        let args_blob = f.read_byte_vec(argsize as usize)?;
        // eprintln!("pos: {:#06x} - time: {:#06x} opcode: {:#04x} argsize: {:#04x} args: {:02x?}", pos, time as u16, opcode as u8, argsize, args_blob);
        Ok(Some(RawInstr {
            time: time as i32,
            opcode: opcode as u16,
            param_mask: 0,
            args_blob,
        }))
    }

    fn write_instr(&self, f: &mut dyn BinWrite, instr: &RawInstr, diagnostics: &DiagnosticEmitter) -> WriteResult {
        f.write_i16(instr.time as _)?;
        f.write_u8(instr.opcode as _)?;
        f.write_u8(instr.args_blob.len() as _)?;  // this version writes argsize rather than instr size
        f.write_all(&instr.args_blob)?;

        if (instr.time, instr.opcode, instr.args_blob.len()) == (0, 0, 0) {
            diagnostics.emit(warning!("\
                wrote an instruction with time 0, opcode 0.  In TH06 MSG, truth will not read the resulting file back \
                correctly due to a known limitation of the current implementation.\
            "));
        }
        Ok(())
    }

    fn write_terminal_instr(&self, f: &mut dyn BinWrite) -> WriteResult {
        f.write_u32(0)
    }
}
