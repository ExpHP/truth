use indexmap::{IndexMap};
use enum_map::{EnumMap};
use arrayvec::ArrayVec;

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

    // Generate timelines
    let mut items = vec![];
    let mut timeline_raiser = llir::Raiser::new(timeline_hooks, &ctx.emitter, &ctx.defs, decompile_options)?;
    for (index, instrs) in ecl.timelines.iter().enumerate() {
        items.push(sp!(ast::Item::Timeline {
            keyword: sp!(()),
            number: sp!(index as i32),
            code: ast::Block({
                timeline_raiser.raise_instrs_to_sub_ast(emitter, instrs, ctx)?
            }),
        }));
    }

    // Decompile bodies of ECL subs
    let mut sub_raiser = llir::Raiser::new(ecl_hooks, &ctx.emitter, &ctx.defs, decompile_options)?;
    sub_raiser.add_ecl_sub_names((0..ecl.subs.len()).map(|i| (i as i32, ecl.subs.get_index(i).unwrap().0.clone())));
    sub_raiser.set_olde_sub_format(sub_format);

    let mut decompiled_subs = IndexMap::new();
    for (ident, instrs) in ecl.subs.iter() {
        decompiled_subs.insert(ident.clone(), ast::Block({
            emitter.chain_with(|f| write!(f, "in {}", ident), |emitter| {
                sub_raiser.raise_instrs_to_sub_ast(emitter, instrs, ctx)
            })?
        }));
    }

    // Detect which subs have parameters; this may involve a bit of global analysis
    // so we had to be wait until after decompiling everything to do this.
    let param_infos = OldeRaiseSubs::from_subs(sub_format, decompiled_subs.values().map(|stmts| &stmts.0[..]));

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
    crate::passes::resolution::assign_languages(&mut ast, LanguageKey::Ecl, ctx)?;
    crate::passes::resolution::compute_diff_label_masks(&mut ast, ctx)?;

    // an early pass to define global constants for sub names
    //
    // (these become relevant when using ins_ syntax or instruction aliases, but not call sugar)
    let sub_ids = gather_sub_ids(&ast, ctx)?;
    for (index, sub_name) in sub_ids.values().enumerate() {
        let const_value: Sp<ast::Expr> = sp!(sub_name.span => (index as i32).into());
        ctx.define_auto_const_var(sub_name.clone(), ScalarType::Int, const_value);
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
        crate::passes::desugar_blocks::run(&mut ast, ctx)?;
        ast
    };

    // Compilation pass
    let emitter = ctx.emitter;
    let emit = |e| emitter.emit(e);
    let mut errors = ErrorFlag::new(); // delay returns for panic bombs
    let mut subs = IndexMap::new();
    let mut timelines = vec![];
    let mut ecl_lowerer = llir::Lowerer::new(&*format.ecl_hooks).with_export_info(sub_format, &sub_info);
    let mut timeline_lowerer = llir::Lowerer::new(&*format.timeline_hooks);

    ast.items.iter().map(|item| {
        // eprintln!("{:?}", item);
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
                let instrs = timeline_lowerer.lower_sub(&code.0, None, ctx)?;
                timelines.push(instrs)
            },

            ast::Item::Func(ast::ItemFunc { qualifier: None, code: None, ref ident, .. }) => {
                subs.insert(ident.value.as_raw().clone(), vec![]); // dummy output to preserve sub indices
                return Err(emit(error!(
                    message("extern functions are not supported in old-style ECL file"),
                    primary(item, "unsupported extern function"),
                )));
            },

            ast::Item::Func(ast::ItemFunc { qualifier: None, code: Some(code), ref ident, params: _, ty_keyword }) => {
                // make double sure that the order of the subs we're compiling matches the numbers we assigned them
                let def_id = ctx.resolutions.expect_def(ident);
                assert_eq!(sub_info.subs.get_index_of(&def_id).unwrap(), subs.len());

                if ty_keyword.value != ast::TypeKeyword::Void {
                    subs.insert(ident.value.as_raw().clone(), vec![]); // dummy output to preserve sub indices
                    return Err(emit(error!(
                        message("return types are not supported in old-style ECL subs like '{}'", ident),
                        primary(ty_keyword, "unsupported return type"),
                    )));
                }

                let instrs = ecl_lowerer.lower_sub(&code.0, Some(def_id), ctx).unwrap_or_else(|e| {
                    errors.set(e);
                    vec![]
                });
                subs.insert(ident.value.as_raw().clone(), instrs);
            }

            // TODO: support inline and const
            ast::Item::Func(ast::ItemFunc { qualifier: Some(_), .. }) => return Err(emit(unsupported(&item.span))),
        } // match item
        Ok(())
    }).collect_with_recovery().unwrap_or_else(|e| errors.set(e));

    ecl_lowerer.finish(ctx).unwrap_or_else(|e| errors.set(e));
    timeline_lowerer.finish(ctx).unwrap_or_else(|e| errors.set(e));
    errors.into_result(())?;

    Ok(OldeEclFile { subs, timelines, binary_filename: None })
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
                            message("duplicate script '{}'", ident),
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
            llir::read_instrs(reader, emitter, ecl_format, sub_offset as u64, None)
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

fn auto_sub_name(i: u32) -> Ident {
    format!("sub{}", i).parse::<Ident>().unwrap()
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
            llir::write_instrs(w, emitter, ecl_format, instrs)
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

    fn infer_params(&self, sub: &[Sp<ast::Stmt>]) -> OldeRaiseSub;
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

    fn infer_params(&self, _sub: &[Sp<ast::Stmt>]) -> OldeRaiseSub {
        // TODO: detect which params are actually used in each sub
        let tys = [(ReadType::Int, "I"), (ReadType::Float, "F")];
        OldeRaiseSub {
            params: tys.into_iter().map(|(ty, tychar)| {
                (self.param_reg_id(ty, 0), ty.into(), format!("{}PAR", tychar).parse().unwrap())
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

    fn infer_params(&self, _sub: &[Sp<ast::Stmt>]) -> OldeRaiseSub {
        // TODO: detect which params are actually used in each sub
        let tys = [(ReadType::Int, "I"), (ReadType::Float, "F")];
        OldeRaiseSub {
            params: tys.into_iter().flat_map(|(ty, tychar)| (0..4).map(move |i| {
                (self.param_reg_id(ty, i), ty.into(), format!("{}PAR_{}", tychar, i).parse().unwrap())
            })).collect(),
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
    // EoSD params have at most one of each type; for PCB+ it's 4
    pub params_by_ty: EnumMap<ReadType, ArrayVec<(usize, Sp<ast::FuncParam>), 4>>,
    param_info: Vec<(DefId, ReadType, Span)>,
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
            param_info: Default::default(),
        };

        for (param_index, param) in func.params.iter().enumerate() {
            if let Some(qualifier) = &param.qualifier {
                return Err(ctx.emitter.emit(error!(
                    message("unexpected {} param in exported function", qualifier),
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

            let param_def_id = ctx.resolutions.expect_def(&param.ident);
            out.param_info.push((param_def_id, param_ty, param.span));
        }
        Ok(out)
    }

    /// Produces the RegId for each parameter, along with other info needed by the register allocator.
    pub fn param_registers<'a>(&'a self, sub_format: &'a dyn OldeSubFormat) -> impl IntoIterator<Item=(DefId, RegId, ReadType, Span)> + 'a {
        let mut offsets = enum_map::enum_map!(_ => 0..);
        self.param_info.iter().map(move |&(def_id, ty, span)| {
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
    fn from_subs<'a>(sub_format: &dyn OldeSubFormat, subs: impl IntoIterator<Item=&'a [Sp<ast::Stmt>]>) -> Self {
        let subs = subs.into_iter().map(|sub| sub_format.infer_params(sub)).collect();
        OldeRaiseSubs { subs }
    }
}

impl OldeRaiseSub {
    /// Get a function for looking up registers in use for backing parameters.
    pub fn reg_lookup_function(&self) -> impl Fn(LanguageKey, RegId) -> Option<(ResIdent, VarType)> + '_ {
        let lookup = {
            self.params.iter()
                .map(|&(reg, var_ty, ref ident)| (reg, (ResIdent::new_null(ident.clone()), var_ty)))
                .collect::<IdMap<_, _>>()
        };
        move |language, reg| match language {
            LanguageKey::Ecl => lookup.get(&reg).cloned(),
            _ => None,
        }
    }

    pub fn params_ast(&self) -> Vec<Sp<ast::FuncParam>> {
        self.params.iter().map(|&(_, var_ty, ref ident)| sp!(ast::FuncParam {
            qualifier: None,
            ty_keyword: sp!(var_ty.into()),
            ident: sp!(ResIdent::new_null(ident.clone())),
        })).collect()
    }
}

// =============================================================================

fn game_format(game: Game) -> Result<OldeFileFormat, ErrorReported> {
    match game {
        | Game::Th06 | Game::Th07 | Game::Th08 | Game::Th09 | Game::Th095
        => Ok(OldeFileFormat::new(game)),

        _ => unimplemented!("game {} not yet supported", game),
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
        let timeline_hooks = Box::new(TimelineHooks { game });
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

    fn intrinsic_opcode_pairs(&self) -> Vec<(llir::IntrinsicInstrKind, raw::Opcode)> {
        use llir::IntrinsicInstrKind as I;

        match self.game {
            Game::Th06 => {
                let mut out = vec![
                    (I::Jmp, 2),
                    (I::CountJmp, 3),
                    (I::AssignOp(ast::AssignOpKind::Assign, ScalarType::Int), 4),
                    (I::AssignOp(ast::AssignOpKind::Assign, ScalarType::Float), 5),
                    (I::CondJmp2A(ScalarType::Int), 27),
                    (I::CondJmp2A(ScalarType::Float), 28),
                    (I::CallEosd, 35),
                    // (I::Return, 36),
                ];
                I::register_binary_ops_of_type(&mut out, 13, ScalarType::Int);
                I::register_binary_ops_of_type(&mut out, 20, ScalarType::Float);
                I::register_eosd_ecl_comp_ops(&mut out, 29, |op| I::CondJmp2B(op));
                // I::register_olde_ecl_comp_ops(&mut out, 37, |op| I::CondCall(op, ScalarType::Int));
                out
            },
            Game::Th07 => {
                let mut out = vec![
                    (I::Jmp, 2),
                    (I::CountJmp, 3),
                    (I::AssignOp(ast::AssignOpKind::Assign, ScalarType::Int), 4),
                    (I::AssignOp(ast::AssignOpKind::Assign, ScalarType::Float), 5),
                    (I::UnOp(ast::UnOpKind::Sin, ScalarType::Float), 24),
                    (I::UnOp(ast::UnOpKind::Cos, ScalarType::Float), 25),
                    (I::CallReg, 41),
                    // (I::Return, 42),
                ];
                I::register_binary_ops_of_type(&mut out, 12, ScalarType::Int);
                I::register_binary_ops_of_type(&mut out, 19, ScalarType::Float);
                I::register_cond_jumps(&mut out, 28);
                // I::register_olde_ecl_comp_ops(&mut out, 37, |op| I::CondCall(op, ScalarType::Int));
                out
            },
            Game::Th08 => vec![],
            Game::Th09 => vec![],
            Game::Th095 => vec![],
            _ => unreachable!(),
        }
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
                    R(-10001), R(-10002), R(-10003), R(-10004),
                    R(-10009), R(-10010), R(-10011), R(-10012)
                ],
                ScalarType::Float => vec![
                    R(-10005), R(-10006), R(-10007), R(-10008),
                ],
                ScalarType::String => vec![],
            },
            Game::Th07 => enum_map::enum_map!{
                ScalarType::Int => vec![
                    R(10000), R(10001), R(10002), R(10003),
                    R(10012), R(10013), R(10014), R(10015),
                ],
                ScalarType::Float => vec![
                    R(10004), R(10005), R(10006), R(10007),
                    R(10008), R(10009), R(10010), R(10011),
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
        (self.game == Game::Th06 && opcode == 130)
            .then(|| HowBadIsIt::ItsWaterElf)
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

    fn instr_format(&self) -> &dyn InstrFormat { self }
}

impl InstrFormat for OldeEclHooks {
    fn instr_header_size(&self) -> usize { 12 }

    fn read_instr(&self, f: &mut BinReader, emitter: &dyn Emitter) -> ReadResult<ReadInstr> {
        let time = f.read_i32()?;
        let opcode = f.read_u16()?;
        let size = f.read_u16()? as usize;
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
        f.write_u16(self.instr_size(instr) as _)?;

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
        f.write_u16(self.instr_header_size() as _)?; // size
        f.write_u16(0xff00)?; // difficulty
        f.write_u16(0x00ff)?; // param_mask
        Ok(())
    }
}

// ------------

struct TimelineHooks { game: Game }
impl TimelineHooks {
    /// In some games, the terminal instruction is shorter than an actual instruction.
    fn has_short_terminal(&self) -> bool {
        self.game < Game::Th08
    }
    fn has_difficulty(&self) -> bool {
        self.game >= Game::Th08
    }
}

impl LanguageHooks for TimelineHooks {
    fn language(&self) -> LanguageKey { LanguageKey::Timeline }

    fn has_registers(&self) -> bool { false }

    fn intrinsic_opcode_pairs(&self) -> Vec<(llir::IntrinsicInstrKind, raw::Opcode)> {
        vec![]
    }

    fn instr_format(&self) -> &dyn InstrFormat { self }
}

impl InstrFormat for TimelineHooks {
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

        let (size, difficulty): (usize, _);
        if self.has_difficulty() {
            size = f.read_u8()? as _;
            difficulty = f.read_u8()? as _;
        } else {
            size = f.read_u16()? as _;
            difficulty = RawInstr::DEFAULTS.difficulty;
        }

        // in games with the normal-sized terminal, the size is incorrectly 0, so check before reading args
        if !self.has_short_terminal() && (time, arg_0, opcode, size, difficulty) == (-1, -1, 0, 0, 0) {
            // FIXME: really should be MaybeTerminal
            return Ok(ReadInstr::Terminal);
        }

        let args_size = size.checked_sub(self.instr_header_size()).ok_or_else(|| {
            emitter.as_sized().emit(error!("bad instruction size ({} < {})", size, self.instr_header_size()))
        })?;
        let args_blob = f.read_byte_vec(args_size)?;

        let instr = RawInstr {
            time, opcode, difficulty, args_blob,
            extra_arg: Some(arg_0 as _),
            ..RawInstr::DEFAULTS
        };
        Ok(ReadInstr::Instr(instr))
    }

    fn write_instr(&self, f: &mut BinWriter, _: &dyn Emitter, instr: &RawInstr) -> WriteResult {
        f.write_i16(instr.time as _)?;
        f.write_i16(instr.extra_arg.unwrap_or(0) as _)?;
        f.write_u16(instr.opcode)?;
        if self.has_difficulty() {
            f.write_u8(self.instr_size(instr) as _)?;
            f.write_u8(instr.difficulty as _)?;
        } else {
            f.write_u16(self.instr_size(instr) as _)?;
        }
        f.write_all(&instr.args_blob)?;
        Ok(())
    }

    fn write_terminal_instr(&self, f: &mut BinWriter, _: &dyn Emitter) -> WriteResult {
        if self.has_short_terminal() {
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
