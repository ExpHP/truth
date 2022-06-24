use indexmap::{IndexMap};
use enum_map::{EnumMap};
use arrayvec::ArrayVec;
use std::collections::{HashSet, BTreeMap};

use crate::raw;
use crate::ast;
use crate::pos::{Sp, Span};
use crate::io::{BinRead, BinWrite, BinReader, BinWriter, ReadResult, WriteResult};
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
    let ecl_hooks = &*format.ecl_hooks;
    let timeline_hooks = &*format.timeline_hooks;
    let sub_format = &*game_sub_format(format.game);

    for i in 0..ecl.subs.len() {
        let name = ecl.subs.get_index(i).unwrap().0.clone();
        ctx.define_enum_const_fresh(name, i as _, auto_enum_names::ecl_sub());
    }

    let const_proof = crate::passes::evaluate_const_vars::run(ctx)?;

    // Generate timelines
    let mut items = vec![];
    let mut timeline_raiser = llir::Raiser::new(timeline_hooks, ctx.emitter, ctx, decompile_options, const_proof)?;
    for (index, instrs) in ecl.timelines.iter().enumerate() {
        items.push(sp!(ast::Item::Script {
            keyword: sp!(()),
            number: None,
            ident: sp!(ident!("timeline{index}")),
            code: ast::Block({
                timeline_raiser.raise_instrs_to_sub_ast(emitter, instrs, ctx)?
            }),
        }));
    }

    let mut sub_raiser = llir::Raiser::new(ecl_hooks, ctx.emitter, ctx, decompile_options, const_proof)?;
    sub_raiser.set_olde_sub_format(sub_format);

    // Decompile ECL subs only halfway
    let mut sub_middles = IndexMap::new();
    for (ident, instrs) in ecl.subs.iter() {
        sub_middles.insert(ident.clone(), {
            emitter.chain_with(|f| write!(f, "in {}", ident), |emitter| {
                sub_raiser.raise_instrs_to_middle(emitter, instrs, ctx)
            })?
        });
    }

    // In this intermediate form we can easily deduce signatures of exported subs.
    let pcb_call_signatures = sub_raiser.infer_pcb_signatures_and_certify_calls(sub_middles.values_mut(), ctx);

    let mut decompiled_subs = IndexMap::new();
    for (ident, middle) in sub_middles.iter() {
        decompiled_subs.insert(ident.clone(), ast::Block({
            emitter.chain_with(|f| write!(f, "in {}", ident), |emitter| {
                sub_raiser.raise_middle_to_sub_ast(emitter, middle, ctx)
            })?
        }));
    }

    let param_infos = OldeRaiseSubs::from_subs(sub_format, decompiled_subs.iter().map(|(ident, stmts)| (ident, &stmts.0[..])), &pcb_call_signatures);

    // Rename registers in each sub after their parameters.
    for (stmts, param_info) in decompiled_subs.values_mut().zip(param_infos.subs.iter()) {
        crate::passes::resolution::raw_reg_to_aliases_with(stmts, ctx, param_info.reg_lookup_function())?;
    }

    for ((ident, stmts), param_info) in decompiled_subs.into_iter().zip(param_infos.subs) {
        items.push(sp!(ast::Item::Func(ast::ItemFunc {
            qualifier: None,
            ty_keyword: sp!(ast::TypeKeyword::Void),
            ident: sp!(ResIdent::new_null(ident.clone())),
            params: param_info.params_ast(),
            code: Some(stmts),
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
    format: &OldeFileFormat,
    ast: &ast::ScriptFile,
    ctx: &mut CompilerContext,
) -> Result<OldeEclFile, ErrorReported> {
    let sub_format = &*game_sub_format(format.game);

    let mut ast = ast.clone();
    crate::passes::resolution::AssignLanguagesOptions {
        funcs: LanguageKey::Ecl,
        scripts: LanguageKey::Timeline,
    }.run(&mut ast, ctx)?;
    crate::passes::resolution::compute_diff_label_masks(&mut ast, ctx)?;

    // an early pass to define global constants for sub names
    //
    // (these become relevant when using ins_ syntax or instruction aliases, but not call sugar)
    let sub_ids = gather_sub_ids(&ast, ctx)?;
    for (index, sub_name) in sub_ids.values().enumerate() {
        let const_value: Sp<ast::Expr> = sp!(sub_name.span => (index as i32).into());
        ctx.define_enum_const(sub_name.clone(), const_value, sp!(auto_enum_names::ecl_sub()));
    }

    // preprocess
    let sub_info;
    let ast = {
        let mut ast = ast;
        crate::passes::resolution::resolve_names(&ast, ctx)?;

        // FIXME: Q: Heeeeey exp, why do you have to make another pass over all the exported functions
        //           when you already made a pass a couple of lines above to define global constants?
        //        A: Well you see, a whole bunch of internal design bits just sort of gnashed together
        //           and started making a horrible noise:
        //            1. When lowering a call, to gather info about the called sub, the Correct Thing
        //               To Do is to use the DefId.
        //            2. That means that when we generate this data, it should be keyed by DefId.
        //            3. That means DefIds have to exist.
        //            4. DefIds for functions are generated during name resolution.
        //               (imho right now this is the part that seems sus)
        //            5. That means name resolution has to have run before this step.
        //            6. But name resolution can only run AFTER generating the consts used by non-call-sugar
        //               calls, or else nothing will resolve to them.
        //
        // gather information about exported subs to use for handling call sugar.
        sub_info = OldeExportedSubs::extract_from_items(sub_format, format.game, &ast.items, ctx)?;

        crate::passes::validate_difficulty::run(&ast, ctx, &*format.ecl_hooks)?;
        crate::passes::type_check::run(&ast, ctx)?;
        crate::passes::evaluate_const_vars::run(ctx)?;
        crate::passes::const_simplify::run(&mut ast, ctx)?;
        crate::passes::desugar_blocks::run(&mut ast, ctx, format.ecl_hooks.language())?;
        ast
    };

    // Compilation pass
    let emitter = ctx.emitter;
    let emit = |e| emitter.emit(e);
    let do_debug_info = true;
    let mut subs = IndexMap::new();
    let mut timeline_indices_in_ast_order = get_and_validate_timeline_indices(&ast.items, emitter)?.into_iter();
    let mut compiled_timelines = vec![None; timeline_indices_in_ast_order.len()];  // to be filled later

    // From this point onwards we must be careful about early exits from the function.
    // Use an ErrorFlag to delay returns for panic bombs.
    let mut errors = ErrorFlag::new();
    let mut ecl_lowerer = llir::Lowerer::new(&*format.ecl_hooks).with_export_info(sub_format, &sub_info);
    let mut timeline_lowerer = llir::Lowerer::new(&*format.timeline_hooks);

    ast.items.iter().map(|item| {
        // eprintln!("{:?}", item);
        match &item.value {
            ast::Item::Meta { keyword, .. } => return Err(emit(error!(
                message("unexpected '{keyword}' in old ECL format file"),
                primary(keyword, "not valid in old format ECL files"),
            ))),
            ast::Item::ConstVar { .. } => {},
            ast::Item::Script { code, ident, .. } => {
                let timeline_index = timeline_indices_in_ast_order.next().unwrap();

                let def_id = None;
                let (instrs, lowering_info) = timeline_lowerer.lower_sub(&code.0, def_id, ctx, do_debug_info)?;

                assert!(compiled_timelines[timeline_index].is_none());
                compiled_timelines[timeline_index] = Some(instrs);

                if let Some(lowering_info) = lowering_info {
                    let export_info = debug_info::ScriptExportInfo {
                        exported_as: debug_info::ScriptType::SclScript { index: timeline_index },
                        name: Some(ident.to_string()),
                        name_span: ident.span.into(),
                    };
                    ctx.script_debug_info.push(debug_info::Script { export_info, lowering_info });
                }
            },

            ast::Item::Func(ast::ItemFunc { qualifier: None, code: None, ref ident, .. }) => {
                subs.insert(ident.value.as_raw().clone(), vec![]); // dummy output to preserve sub indices
                return Err(emit(error!(
                    message("extern functions are not supported in old-style ECL file"),
                    primary(item, "unsupported extern function"),
                )));
            },

            ast::Item::Func(ast::ItemFunc { qualifier: None, code: Some(code), ref ident, params: _, ty_keyword }) => {
                let sub_index = subs.len();

                // make double sure that the order of the subs we're compiling matches the numbers we assigned them
                let def_id = ctx.resolutions.expect_def(ident);
                assert_eq!(sub_info.subs.get_index_of(&def_id).unwrap(), subs.len());

                if ty_keyword.value != ast::TypeKeyword::Void {
                    subs.insert(ident.value.as_raw().clone(), vec![]); // dummy output to preserve sub indices
                    return Err(emit(error!(
                        message("return types are not supported in old-style ECL subs like '{ident}'"),
                        primary(ty_keyword, "unsupported return type"),
                    )));
                }

                let (instrs, lowering_info) = ecl_lowerer.lower_sub(&code.0, Some(def_id), ctx, do_debug_info).unwrap_or_else(|e| {
                    errors.set(e);
                    (vec![], None)  // dummy instrs so that we can still insert an item into 'subs' and get the right indices
                });
                subs.insert(ident.value.as_raw().clone(), instrs);

                if let Some(lowering_info) = lowering_info {
                    let export_info = debug_info::ScriptExportInfo {
                        exported_as: debug_info::ScriptType::EclSub { index: sub_index },
                        name: Some(ident.to_string()),
                        name_span: ident.span.into(),
                    };
                    ctx.script_debug_info.push(debug_info::Script { export_info, lowering_info });
                }
            }

            // TODO: support inline and const
            ast::Item::Func(ast::ItemFunc { qualifier: Some(_), .. }) => return Err(emit(unsupported(&item.span))),
        } // match item
        Ok(())
    }).collect_with_recovery().unwrap_or_else(|e| errors.set(e));

    assert_eq!(timeline_indices_in_ast_order.next(), None);

    ecl_lowerer.finish(ctx).unwrap_or_else(|e| errors.set(e));
    timeline_lowerer.finish(ctx).unwrap_or_else(|e| errors.set(e));
    errors.into_result(())?;

    Ok(OldeEclFile {
        subs,
        // each index of compiled_timelines should have been set exactly once
        timelines: compiled_timelines.into_iter().map(|opt| opt.unwrap()).collect(),
        binary_filename: None,
    })
}

fn gather_sub_ids(ast: &ast::ScriptFile, ctx: &mut CompilerContext) -> Result<IndexMap<Ident, Sp<ResIdent>>, ErrorReported> {
    let mut script_ids = IndexMap::new();
    for item in &ast.items {
        match &item.value {
            &ast::Item::Func(ast::ItemFunc { qualifier: None, ref ident, .. }) => {
                // give a better error on redefinitions than the generic "ambiguous auto const" message
                match script_ids.entry(ident.value.as_raw().clone()) {
                    indexmap::map::Entry::Vacant(e) => {
                        e.insert(ident.clone());
                    },
                    indexmap::map::Entry::Occupied(e) => {
                        let prev_ident = e.get();
                        return Err(ctx.emitter.emit(error!(
                            message("duplicate script '{ident}'"),
                            primary(ident, "redefined here"),
                            secondary(prev_ident, "originally defined here"),
                        )));
                    },
                }
            },
            _ => {},
        }
    }
    Ok(script_ids)
}

/// Computes indices for timelines without indices, and reports warnings and errors about bad index usage.
///
/// The output `vec` will be a permutation of the indices `0..vec.len()` describing the index in the output ECL
/// file for each timeline in the AST.
fn get_and_validate_timeline_indices(
    items: &[Sp<ast::Item>],
    emitter: &impl Emitter,
) -> Result<Vec<usize>, ErrorReported> {
    let mut next_auto_number = 0;
    let mut explicit_spans = vec![];
    let mut auto_spans = vec![];
    let mut names = HashSet::new();
    let mut timeline_indices = vec![];
    let mut ast_spans_by_timeline = BTreeMap::<usize, Vec<Span>>::new();  // spans for redeclaration checks
    let mut errors = ErrorFlag::new();

    for item in items {
        match &item.value {
            &ast::Item::Script { number, ref ident, .. } => {
                if let Some(existing_ident) = names.replace(ident) {
                    emitter.emit(warning!(
                        message("timeline '{ident}' already defined"),
                        primary(ident, "redefined here"),
                        secondary(existing_ident, "previously defined here"),
                    )).ignore();
                }

                let ast_span = number.map(|x| x.span).unwrap_or(ident.span);
                match number {
                    Some(_) => explicit_spans.push(ast_span),
                    None => auto_spans.push(ast_span),
                }

                let timeline_index = match number {
                    Some(number) if number < 0 => {
                        errors.set(emitter.emit(error!(
                            message("negative timeline indices are forbidden"),
                            primary(number, "")
                        )));
                        continue;
                    },
                    Some(number) => number.value as usize,
                    None => {
                        next_auto_number += 1;
                        next_auto_number - 1
                    },
                };

                timeline_indices.push(timeline_index);
                ast_spans_by_timeline.entry(timeline_index).or_default().push(ast_span);
            },
            _ => {},  // not timeline
        }
    }

    if !explicit_spans.is_empty() && !auto_spans.is_empty() {
        let mut diag = warning!(
            message("mixture of explicit and automatic timeline indices"),
            primary(explicit_spans.iter().next().unwrap(), "explicit index"),
        );
        for (index, &span) in auto_spans.iter().enumerate() {
            diag.secondary(span, format!("implicitly has index {index}"));
        }
        emitter.emit(diag).ignore();
    }

    let num_unique_timeline_indices = ast_spans_by_timeline.len();
    let expected_unique_timeline_count = ast_spans_by_timeline.keys().copied().next_back().map_or(0, |max| max + 1);

    if num_unique_timeline_indices != expected_unique_timeline_count as usize {
        let missing_string = {
            (0..expected_unique_timeline_count).filter(|index| !ast_spans_by_timeline.contains_key(index))
                .map(|index| index.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        };
        let max_index_span = ast_spans_by_timeline.values().next_back().unwrap()[0];
        errors.set(emitter.emit(error!(
            message("missing timeline(s) for index {missing_string}"),
            primary(max_index_span, "defining this timeline requires all lesser indices"),
        )));
    }

    for timeline_index in 0..expected_unique_timeline_count {
        match ast_spans_by_timeline.get(&timeline_index).map_or(0, |x| x.len()) {
            0 => {},  // already handled by "missing timeline" check above
            1 => {},
            _ => {
                let ast_spans = &ast_spans_by_timeline[&timeline_index];
                let first_span = ast_spans[0];
                for &redefinition_span in &ast_spans[1..] {
                    errors.set(emitter.emit(error!(
                        message("duplicate timeline for index {timeline_index}"),
                        primary(redefinition_span, "redefined here"),
                        secondary(first_span, "previously defined here")
                    )));
                }
            }
        }
    }

    errors.into_result(timeline_indices)
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
    let ecl_format = format.ecl_hooks.instr_format();
    let timeline_format = format.timeline_hooks.instr_format();

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
                    "unexpected nonzero high word for num_subs: {num_subs_high_word:#x}",
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
            return Err(emitter.emit(error!("unexpected timeline offset {offset:#x} after a null offset")));
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
        let instrs = emitter.chain_with(|f| write!(f, "in sub {index}"), |emitter| {
            llir::read_instrs(reader, emitter, ecl_format, sub_offset as u64, None)
        })?;
        Ok((name, instrs))
    }).collect::<ReadResult<_>>()?;

    let timelines = timeline_offsets[..num_timelines].iter().enumerate().map(|(index, &sub_offset)| {
        reader.seek_to(start_pos + sub_offset as u64)?;
        let instrs = emitter.chain_with(|f| write!(f, "in timeline sub {index}"), |emitter| {
            llir::read_instrs(reader, emitter, timeline_format, sub_offset as u64, None)
        })?;
        Ok(instrs)
    }).collect::<ReadResult<_>>()?;

    let binary_filename = Some(reader.display_filename().to_string());
    Ok(OldeEclFile { subs, timelines, binary_filename })
}

fn auto_sub_name(i: u32) -> Ident {
    ident!("sub{i}")
}

fn write_olde_ecl(
    w: &mut BinWriter,
    emitter: &impl Emitter,
    format: &OldeFileFormat,
    ecl: &OldeEclFile,
) -> WriteResult {
    let ecl_format = format.ecl_hooks.instr_format();
    let timeline_format = format.timeline_hooks.instr_format();

    let start_pos = w.pos()?;

    if let Some(magic) = format.magic() {
        w.write_u32(magic)?;
    }

    let max_timelines = format.timeline_array_kind().max_timelines();
    if ecl.timelines.len() > max_timelines {
        // FIXME: NEEDSTEST for each game
        return Err(emitter.emit(error!("too many timelines! (max allowed in this game is {max_timelines})")));
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
        emitter.chain_with(|f| write!(f, "in sub {ident} (index {index})"), |emitter| {
            llir::write_instrs(w, emitter, ecl_format, instrs)
        })?;
    }

    let mut timeline_offsets = vec![];
    for (index, instrs) in ecl.timelines.iter().enumerate() {
        timeline_offsets.push(w.pos()? - start_pos);
        emitter.chain_with(|f| write!(f, "in timeline {index}"), |emitter| {
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

struct EosdSubFormat { game: Game }
struct PcbSubFormat { game: Game }

fn game_sub_format(game: Game) -> Box<dyn OldeSubFormat> {
    match game {
        Game::Th06
            => Box::new(EosdSubFormat { game }),

        Game::Th07 | Game::Th08 | Game::Th09 | Game::Th095
            => Box::new(PcbSubFormat { game }),

        _ => unreachable!(),
    }
}

pub trait OldeSubFormat {
    fn param_reg_id(&self, ty: ReadType, number: usize) -> RegId;

    /// Info for [`IntrinsicInstrKind::CallReg`] for games that use it.
    fn call_reg_info(&self) -> Option<CallRegInfo>;

    // ---------
    // --- used during compilation ---

    fn max_params_per_type(&self) -> usize;

    /// Generate a message used to explain which regs are used by parameters in this format.
    fn reg_usage_explanation(&self, ctx: &CompilerContext<'_>) -> Option<String>;

    fn limits_msg(&self) -> &'static str;

    // ---------
    // --- used during decompilation ---

    fn infer_params(&self, ident: &Ident, sub: &[Sp<ast::Stmt>], call_reg_signatures: &llir::CallRegSignatures) -> OldeRaiseSub;
}

pub struct CallRegInfo {
    pub arg_regs_by_type: EnumMap<ReadType, Vec<RegId>>,
}

impl OldeSubFormat for EosdSubFormat {
    fn max_params_per_type(&self) -> usize { 1 }

    fn reg_usage_explanation(&self, ctx: &CompilerContext<'_>) -> Option<String> {
        let stringify_reg = |reg| crate::fmt::stringify(&ctx.reg_to_ast(LanguageKey::Ecl, reg));
        Some(format!(
            "{} ECL subs pass their arguments in {} and {}",
            self.game.abbr(),
            stringify_reg(self.param_reg_id(ReadType::Int, 0)),
            stringify_reg(self.param_reg_id(ReadType::Float, 0)),
        ))
    }

    fn limits_msg(&self) -> &'static str {
        "limited to 1 int and 1 float"
    }

    fn param_reg_id(&self, ty: ReadType, number: usize) -> RegId {
        assert_eq!(number, 0);
        match ty {
            ReadType::Int => RegId(-10001),
            ReadType::Float => RegId(-10005),
        }
    }

    fn call_reg_info(&self) -> Option<CallRegInfo> { None }  // uses a different intrinsic

    fn infer_params(&self, _ident: &Ident, _sub: &[Sp<ast::Stmt>], _: &llir::CallRegSignatures) -> OldeRaiseSub {
        // TODO: detect which params are actually used in each sub
        let tys = [(ReadType::Int, "I"), (ReadType::Float, "F")];
        OldeRaiseSub {
            params: tys.into_iter().map(|(ty, tychar)| {
                (self.param_reg_id(ty, 0), ty.into(), ident!("{tychar}PAR"))
            }).collect(),
        }
    }
}

impl OldeSubFormat for PcbSubFormat {
    fn max_params_per_type(&self) -> usize { 4 }

    fn reg_usage_explanation(&self, ctx: &CompilerContext<'_>) -> Option<String> {
        let stringify_reg = |reg| crate::fmt::stringify(&ctx.reg_to_ast(LanguageKey::Ecl, reg));
        Some(format!(
            "{} ECL subs receive their arguments in {} through {} and {} through {}",
            self.game.abbr(),
            stringify_reg(self.param_reg_id(ReadType::Int, 0)),
            stringify_reg(self.param_reg_id(ReadType::Int, 3)),
            stringify_reg(self.param_reg_id(ReadType::Float, 0)),
            stringify_reg(self.param_reg_id(ReadType::Float, 3)),
        ))
    }

    fn limits_msg(&self) -> &'static str {
        "limited to 4 ints and 4 floats"
    }

    fn param_reg_id(&self, ty: ReadType, number: usize) -> RegId {
        assert!(number < self.max_params_per_type());

        let ty_offset = match ty {
            ReadType::Int => 0,
            ReadType::Float => 4,
        };
        let param_a_id = match self.game {
            Game::Th07 => 10029,
            Game::Th08 => 10053,
            Game::Th09 => 10053,
            Game::Th095 => 10036,
            _ => unreachable!(),
        };
        RegId(param_a_id + ty_offset + number as i32)
    }

    fn call_reg_info(&self) -> Option<CallRegInfo> {
        Some(CallRegInfo {
            arg_regs_by_type: enum_map::enum_map!{
                ty => {
                    (0..self.max_params_per_type())
                        .map(|index| RegId(self.param_reg_id(ty, index).0 + 8)).collect()
                },
            },
        })
    }

    fn infer_params(&self, ident: &Ident, _sub: &[Sp<ast::Stmt>], call_reg_signatures: &llir::CallRegSignatures) -> OldeRaiseSub {
        // For PCB subs we look at callsites to infer parameters, rather than the function body.
        let ty_chars = enum_map::enum_map!{
            ReadType::Int => "I",
            ReadType::Float => "F",
        };
        let mut next_indices = enum_map::enum_map!(_ => 0..);

        let param_tys = call_reg_signatures.signatures.get(ident).map(|x| &x[..]).unwrap_or(&[][..]);

        OldeRaiseSub {
            params: param_tys.iter().map(|&ty| {
                let i = next_indices[ty].next().unwrap();
                let ty_char = ty_chars[ty];
                let name = ident!("{ty_char}PAR_{i}");
                (self.param_reg_id(ty, i), ty.into(), name)
            }).collect(),
        }
    }
}

// -- compilation --
pub struct OldeExportedSubs {
    pub subs: IndexMap<DefId, OldeExportedSub>,
}

pub struct OldeExportedSub {
    pub index: raw::LangInt,
    pub name: Sp<ResIdent>,
    /// The params that this sub actually has, grouped by type.
    pub params_by_ty: EnumMap<ReadType, ArrayVec<(usize, Sp<ast::FuncParam>), 4>>,
    /// The params that this sub actually has, in their order in the signature.
    pub params_in_sig: Vec<(Option<DefId>, ReadType, Span)>,
}

impl OldeExportedSubs {
    /// Scan through items and gather information on the parameters of all exported subs.
    fn extract_from_items(
        sub_format: &dyn OldeSubFormat,
        game: Game,
        items: &[Sp<ast::Item>],
        ctx: &CompilerContext<'_>,
    ) -> Result<Self, ErrorReported> {
        let mut subs = IndexMap::new();
        let mut sub_index = 0;
        let mut errors = ErrorFlag::new();
        for item in items {
            if let ast::Item::Func(func@ast::ItemFunc { qualifier: None, ident, .. }) = &item.value {
                match OldeExportedSub::from_item(sub_format, game, func, sub_index, ctx) {
                    Ok(sub) => {
                        subs.insert(ctx.resolutions.expect_def(ident), sub);
                        sub_index += 1;
                    },
                    Err(e) => errors.set(e),
                };
            }
        }
        errors.into_result(OldeExportedSubs { subs })
    }
}

impl OldeExportedSub {
    fn from_item(
        sub_format: &dyn OldeSubFormat,
        game: Game,
        func: &ast::ItemFunc,
        sub_index: usize,
        ctx: &CompilerContext<'_>,
    ) -> Result<Self, ErrorReported> {
        assert!(func.qualifier.is_none());  // shouldn't be called on const/inline

        let mut out = OldeExportedSub {
            index: sub_index as _,
            name: func.ident.clone(),
            params_by_ty: Default::default(),
            params_in_sig: Default::default(),
        };

        for (param_index, param) in func.params.iter().enumerate() {
            if let Some(qualifier) = &param.qualifier {
                return Err(ctx.emitter.emit(error!(
                    message("unexpected {qualifier} param in exported function"),
                    primary(qualifier, ""),
                )));
            }

            let param_ty = match param.ty_keyword.var_ty().as_known_ty().and_then(ReadType::from_ty) {
                Some(ty) => ty,
                None => return Err(ctx.emitter.emit(error!(
                    message("invalid type for param in {} ECL", game.abbr()),
                    primary(param.ty_keyword, ""),
                ))),
            };

            if out.params_by_ty[param_ty].len() >= sub_format.max_params_per_type() {
                return Err(ctx.emitter.emit(error!(
                    message("too many {} params for {} ECL function", param.ty_keyword, game.abbr()),
                    primary(param, "extra {} param", param.ty_keyword),
                    note("exported {} ECL functions are {}", game.abbr(), sub_format.limits_msg()),
                )));
            }
            out.params_by_ty[param_ty].push((param_index, param.clone()));

            let param_def_id = param.ident.as_ref().map(|ident| ctx.resolutions.expect_def(ident));
            out.params_in_sig.push((param_def_id, param_ty, param.span));
        }
        Ok(out)
    }

    /// Produces the RegId for each parameter, along with other info needed by the register allocator.
    pub fn param_registers<'a>(&'a self, sub_format: &'a dyn OldeSubFormat) -> impl IntoIterator<Item=(Option<DefId>, RegId, ReadType, Span)> + 'a {
        let mut offsets = enum_map::enum_map!(_ => 0..);
        self.params_in_sig.iter().map(move |&(def_id, ty, span)| {
            let reg = sub_format.param_reg_id(ty, offsets[ty].next().unwrap());
            (def_id, reg, ty, span)
        })
    }
}

// -- decompilation --
pub struct OldeRaiseSubs {
    pub subs: Vec<OldeRaiseSub>,
}

pub struct OldeRaiseSub {
    pub params: Vec<(RegId, VarType, Ident)>,
}

impl OldeRaiseSubs {
    fn from_subs<'a>(
        sub_format: &dyn OldeSubFormat,
        subs: impl IntoIterator<Item=(&'a Ident, &'a [Sp<ast::Stmt>])>,
        pcb_call_signatures: &llir::CallRegSignatures,
    ) -> Self {
        let subs = subs.into_iter().map(|(ident, sub)| {
            sub_format.infer_params(ident, sub, pcb_call_signatures)
        }).collect();
        OldeRaiseSubs { subs }
    }
}

impl OldeRaiseSub {
    /// Get a function for looking up registers in use for backing parameters.
    pub fn reg_lookup_function(&self) -> impl Fn(LanguageKey, RegId) -> Option<(ResIdent, VarType)> + '_ {
        let precomputed_map = {
            self.params.iter()
                .map(|&(reg, var_ty, ref ident)| (reg, (ResIdent::new_null(ident.clone()), var_ty)))
                .collect::<IdMap<_, _>>()
        };
        move |language, reg| match language {
            LanguageKey::Ecl => precomputed_map.get(&reg).cloned(),
            _ => None,
        }
    }

    pub fn params_ast(&self) -> Vec<Sp<ast::FuncParam>> {
        self.params.iter().map(|&(_, var_ty, ref ident)| sp!(ast::FuncParam {
            qualifier: None,
            ty_keyword: sp!(var_ty.into()),
            ident: Some(sp!(ResIdent::new_null(ident.clone()))),
        })).collect()
    }
}

// =============================================================================

fn game_format(game: Game) -> Result<OldeFileFormat, ErrorReported> {
    match game {
        | Game::Th06 | Game::Th07 | Game::Th08 | Game::Th09 | Game::Th095
        => Ok(OldeFileFormat::new(game)),

        _ => unimplemented!("game {game} not yet supported"),
    }
}

// =============================================================================

struct OldeFileFormat {
    game: Game,
    ecl_hooks: Box<dyn LanguageHooks>,
    timeline_hooks: Box<dyn LanguageHooks>,
}

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
    fn new(game: Game) -> Self {
        assert!(game < Game::Th10);
        let ecl_hooks = Box::new(OldeEclHooks { game });
        let timeline_hooks = Box::new(TimelineHooks { format: match game {
            Game::Th06 | Game::Th07 => Box::new(TimelineFormat06),
            _ => Box::new(TimelineFormat08),
        }});
        Self { game, ecl_hooks, timeline_hooks }
    }

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
}

struct OldeEclHooks { game: Game }

impl LanguageHooks for OldeEclHooks {
    fn language(&self) -> LanguageKey { LanguageKey::Ecl }

    fn has_registers(&self) -> bool { true }

    fn default_difficulty_mask(&self) -> Option<raw::DifficultyMask> {
        Some(crate::passes::semantics::time_and_difficulty::DEFAULT_DIFFICULTY_MASK_BYTE)
    }

    // offsets are written as relative in these files
    fn encode_label(&self, current_offset: raw::BytePos, dest_offset: raw::BytePos) -> raw::RawDwordBits {
        let relative = dest_offset as i64 - current_offset as i64;
        relative as i32 as u32
    }
    fn decode_label(&self, current_offset: raw::BytePos, bits: raw::RawDwordBits) -> raw::BytePos {
        let relative = bits as i32 as i64; // double cast for sign-extension
        (current_offset as i64 + relative) as u64
    }

    fn register_style(&self) -> RegisterEncodingStyle {
        if self.game == Game::Th06 {
            RegisterEncodingStyle::EosdEcl { does_value_look_like_a_register: |value| {
                let id = match *value {
                    ScalarValue::Int(x) => x,
                    ScalarValue::Float(x) => x as i32,
                    ScalarValue::String(_) => return false,
                };
                -10_025 <= id && id <= -10_001
            }}
        } else {
            RegisterEncodingStyle::ByParamMask
        }
    }

    fn general_use_regs(&self) -> EnumMap<ScalarType, Vec<RegId>> {
        use RegId as R;

        match self.game {
            Game::Th06 => enum_map::enum_map!{
                ScalarType::Int => vec![
                    R(-10001), R(-10002), R(-10003), R(-10004), // I0-I3
                    R(-10009), R(-10010), R(-10011), R(-10012), // IC0-IC3
                ],
                ScalarType::Float => vec![
                    R(-10005), R(-10006), R(-10007), R(-10008), // F0-F3
                ],
                ScalarType::String => vec![],
            },
            Game::Th07 => enum_map::enum_map!{
                ScalarType::Int => vec![
                    R(10000), R(10001), R(10002), R(10003), // I0-I3
                    R(10012), R(10013), R(10014), R(10015), // IC0-IC3
                    //R(10029), R(10030), R(10031), R(10032), // PARAM_A-PARAM_D
                ],
                ScalarType::Float => vec![
                    R(10004), R(10005), R(10006), R(10007), // F0-F3
                    R(10008), R(10009), R(10010), R(10011), // F4-F7
                    R(10072), R(10074),                     // F8-F9
                    //R(10033), R(10034), R(10035), R(10036), // PARAM_R-PARAM_N
                ],
                ScalarType::String => vec![],
            },
            Game::Th08 | Game::Th09 => enum_map::enum_map!{
                ScalarType::Int => vec![
                    R(10000), R(10001), R(10002), R(10003), // I0-I3
                    R(10004), R(10005), R(10006), R(10007), // I4-I7
                    R(10036), R(10037), R(10038), R(10039), // IC0-IC3
                    //R(10053), R(10054), R(10055), R(10056), // PARAM_A-PARAM_D
                ],
                ScalarType::Float => vec![
                    R(10016), R(10017), R(10018), R(10019), // F0-F3
                    R(10020), R(10021), R(10022), R(10023), // F4-F7
                    R(10094), R(10095),                     // F8-F9
                    //R(10057), R(10058), R(10059), R(10060), // PARAM_R-PARAM_N
                ],
                ScalarType::String => vec![],
            },
            Game::Th095 => enum_map::enum_map!{
                ScalarType::Int => vec![
                    R(10000), R(10001), R(10002), R(10003), // I0-I3
                    R(10004), R(10005), R(10006), R(10007), // I4-I7
                    R(10020), R(10021), R(10022), R(10023), // IC0-IC3
                    //R(10036), R(10037), R(10038), R(10039), // PARAM_A-PARAM_D
                ],
                ScalarType::Float => vec![
                    R(10008), R(10009), R(10010), R(10011), // F0-F3
                    R(10012), R(10013), R(10014), R(10015), // F4-F7
                    R(10077), R(10078), R(10079), R(10080), // F8-F11
                    //R(10040), R(10041), R(10042), R(10043), // PARAM_R-PARAM_N
                ],
                ScalarType::String => vec![],
            },
            _ => enum_map::enum_map!{
                _ => vec![],
            },
        }
    }

    fn instr_disables_scratch_regs(&self, opcode: u16) -> Option<HowBadIsIt> {
        // that one that disables the callstack
        match (self.game, opcode) {
            | (Game::Th06, 130)
            | (Game::Th07, 130)
            | (Game::Th08, 151)
            | (Game::Th09, 151)
            | (Game::Th095, 126)
            => Some(HowBadIsIt::ItsWaterElf),
            _ => None
        }
    }

    fn difficulty_register(&self) -> Option<RegId> {
        match self.game {
            Game::Th06 => Some(RegId(-10013)),
            Game::Th07 => Some(RegId(10016)),
            Game::Th08 => Some(RegId(10040)),
            Game::Th09 => Some(RegId(10040)),
            Game::Th095 => None,  // literally does not exist
            _ => None,
        }
    }

    fn has_auto_casts(&self) -> bool {
        self.game != Game::Th06
    }

    fn instr_format(&self) -> &dyn InstrFormat { self }
}

impl InstrFormat for OldeEclHooks {
    fn instr_header_size(&self) -> usize { 12 }

    fn read_instr(&self, f: &mut BinReader, emitter: &dyn Emitter) -> ReadResult<ReadInstr> {
        let time = f.read_i32()?;
        let opcode = f.read_u16()?;
        let size = f.read_i16()? as usize;
        let before_difficulty = f.read_u8()?;  // according to zero, not referenced in any game
        let difficulty = f.read_u8()?;
        let param_mask = f.read_u16()?;

        if before_difficulty != 0 {
            emitter.as_sized().emit(warning!(
                message("unexpected nonzero byte before difficulty mask: {:#04X}", before_difficulty)
            )).ignore();
        }
        if self.game == Game::Th06 && param_mask != 0xFF {
            emitter.as_sized().emit(warning!(
                message("unexpected non-FF parameter mask in EoSD: {:#04X}", param_mask)
            )).ignore();
        }

        let args_blob = f.read_byte_vec(size - self.instr_header_size())?;

        let instr = RawInstr {
            time, opcode, args_blob,
            param_mask: param_mask.into(), difficulty: difficulty.into(),
            ..RawInstr::DEFAULTS
        };

        if opcode == (-1_i16) as u16 {
            Ok(ReadInstr::Terminal)
        } else {
            Ok(ReadInstr::Instr(instr))
        }
    }

    fn write_instr(&self, f: &mut BinWriter, _: &dyn Emitter, instr: &RawInstr) -> WriteResult {
        f.write_i32(instr.time)?;
        f.write_u16(instr.opcode)?;
        f.write_i16(self.instr_size(instr) as _)?;

        f.write_u8(0)?;
        f.write_u8(instr.difficulty)?;
        f.write_u16(match self.game {
            Game::Th06 => 0x00FF,
            _ => instr.param_mask as _,
        })?;

        f.write_all(&instr.args_blob)?;
        Ok(())
    }

    fn write_terminal_instr(&self, f: &mut BinWriter, _: &dyn Emitter) -> WriteResult {
        f.write_i32(-1)?; // time
        f.write_i16(-1)?; // opcode
        f.write_i16(self.instr_header_size() as _)?; // size
        f.write_u16(0xff00)?; // difficulty
        f.write_u16(0x00ff)?; // param_mask
        Ok(())
    }
}

// ------------

struct TimelineHooks { format: Box<dyn InstrFormat> }
struct TimelineFormat06;
struct TimelineFormat08;

impl LanguageHooks for TimelineHooks {
    fn language(&self) -> LanguageKey { LanguageKey::Timeline }

    fn has_registers(&self) -> bool { false }

    fn instr_format(&self) -> &dyn InstrFormat { &*self.format }
}

impl InstrFormat for TimelineFormat06 {
    fn instr_header_size(&self) -> usize { 8 }

    fn read_instr(&self, f: &mut BinReader, emitter: &dyn Emitter) -> ReadResult<ReadInstr> {
        let time = f.read_i16()? as i32;
        let arg_0 = f.read_i16()? as i32;

        // the terminal instruction is only 4 bytes long so we must check now
        if (time, arg_0) == (-1, 4) {
            // FIXME: really should be MaybeTerminal since both arg_0 = 4 and time = -1
            //        are things that naturally occur on real instructions.
            return Ok(ReadInstr::Terminal);
        }

        let opcode = f.read_u16()?;
        let size = f.read_i16()? as usize;

        let args_size = size.checked_sub(self.instr_header_size()).ok_or_else(|| {
            emitter.as_sized().emit(error!("bad instruction size ({} < {})", size, self.instr_header_size()))
        })?;
        let args_blob = f.read_byte_vec(args_size)?;

        let instr = RawInstr {
            time, opcode, args_blob,
            extra_arg: Some(arg_0 as _),
            ..RawInstr::DEFAULTS
        };
        Ok(ReadInstr::Instr(instr))
    }

    fn write_instr(&self, f: &mut BinWriter, _: &dyn Emitter, instr: &RawInstr) -> WriteResult {
        f.write_i16(instr.time as _)?;
        f.write_i16(instr.extra_arg.unwrap_or(0) as _)?;
        f.write_u16(instr.opcode)?;
        f.write_u16(self.instr_size(instr) as _)?;
        f.write_all(&instr.args_blob)?;
        Ok(())
    }

    fn write_terminal_instr(&self, f: &mut BinWriter, _: &dyn Emitter) -> WriteResult {
        f.write_i16(-1)?; // time
        f.write_i16(4)?; // arg_0
        Ok(())
    }
}


impl InstrFormat for TimelineFormat08 {
    fn instr_header_size(&self) -> usize { 8 }

    fn read_instr(&self, f: &mut BinReader, emitter: &dyn Emitter) -> ReadResult<ReadInstr> {
        let time = f.read_i32()? as i32;
        let opcode = f.read_u16()?;
        let size = f.read_u8()? as usize;
        let difficulty = f.read_u8()?;

        // the size is incorrectly 0, so check before reading args
        if (time, opcode, size, difficulty) == (-1, 0, 0, 0) {
            // FIXME: really should be MaybeTerminal
            return Ok(ReadInstr::Terminal);
        }

        let args_size = size.checked_sub(self.instr_header_size()).ok_or_else(|| {
            emitter.as_sized().emit(error!("bad instruction size ({} < {})", size, self.instr_header_size()))
        })?;
        let args_blob = f.read_byte_vec(args_size)?;

        let instr = RawInstr { time, opcode, difficulty, args_blob, ..RawInstr::DEFAULTS };
        Ok(ReadInstr::Instr(instr))
    }

    fn write_instr(&self, f: &mut BinWriter, _: &dyn Emitter, instr: &RawInstr) -> WriteResult {
        f.write_i32(instr.time as _)?;
        f.write_u16(instr.opcode)?;
        f.write_u8(self.instr_size(instr) as _)?;
        f.write_u8(instr.difficulty as _)?;
        f.write_all(&instr.args_blob)?;
        Ok(())
    }

    fn write_terminal_instr(&self, f: &mut BinWriter, _: &dyn Emitter) -> WriteResult {
        f.write_i32(-1)?; // time
        f.write_u32(0)?; // opcode, size, difficulty
        Ok(())
    }
}
