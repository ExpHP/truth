use indexmap::IndexMap;

use crate::ast;
use crate::io::{BinRead, BinWrite, BinReader, BinWriter, Encoded, ReadResult, WriteResult, DEFAULT_ENCODING};
use crate::diagnostic::{Diagnostic, Emitter};
use crate::error::ErrorReported;
use crate::game::Game;
use crate::ident::{Ident};
use crate::llir::{self, ReadInstr, RawInstr, InstrFormat, AcceleratingByteMask};
use crate::meta::{self, FromMeta, FromMetaError, Meta, ToMeta};
use crate::pos::Sp;
use crate::context::CompilerContext;
use crate::passes::DecompileKind;

// =============================================================================

/// Game-independent representation of a STD file.
#[derive(Debug, Clone, PartialEq)]
pub struct StdFile {
    pub unknown: u32,
    pub objects: IndexMap<Sp<Ident>, Object>,
    pub instances: Vec<Instance>,
    pub script: Vec<RawInstr>,
    pub extra: StdExtra,
    /// Filename of a read binary file, for display purposes only.
    binary_filename: Option<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum StdExtra {
    Th06 {
        stage_name: Sp<String>,
        bgm: [Std06Bgm; 4],
    },
    Th10 {
        anm_path: Sp<String>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Std06Bgm {
    pub path: Sp<String>,
    pub name: Sp<String>,
}

impl FromMeta<'_> for Std06Bgm {
    fn from_meta(meta: &Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
        meta.parse_object(|m| Ok(Std06Bgm {
            path: m.expect_field("path")?,
            name: m.expect_field("name")?,
        }))
    }
}

impl ToMeta for Std06Bgm {
    fn to_meta(&self) -> Meta {
        Meta::make_object()
            .field("path", &self.path.value)
            .field("name", &self.name.value)
            .build()
    }
}

impl StdFile {
    pub fn decompile_to_ast(&self, game: Game, ctx: &mut CompilerContext, decompile_kind: DecompileKind) -> Result<ast::ScriptFile, ErrorReported> {
        let emitter = ctx.emitter.while_decompiling(self.binary_filename.as_deref());
        decompile_std(self, &emitter, &*game_format(game), ctx, decompile_kind)
    }

    pub fn compile_from_ast(game: Game, script: &ast::ScriptFile, ctx: &mut CompilerContext) -> Result<Self, ErrorReported> {
        compile_std(&*game_format(game), script, ctx)
    }

    pub fn write_to_stream(&self, w: &mut BinWriter, game: Game) -> WriteResult {
        let emitter = w.emitter();
        write_std(w, &emitter, &*game_format(game), self)
    }

    pub fn read_from_stream(r: &mut BinReader, game: Game) -> ReadResult<Self> {
        let emitter = r.emitter();
        read_std(r, &emitter, &*game_format(game))
    }
}

impl StdFile {
    fn init_from_meta<'m>(file_format: &dyn FileFormat, fields: &'m Sp<meta::Fields>) -> Result<Self, FromMetaError<'m>> {
        let mut m = meta::ParseObject::new(fields);
        let out = StdFile {
            unknown: m.expect_field("unknown")?,
            objects: m.expect_field("objects")?,
            instances: m.expect_field("instances")?,
            script: vec![],
            extra: file_format.extra_from_meta(&mut m)?,
            binary_filename: None,
        };
        m.finish()?;
        Ok(out)
    }

    fn make_meta(&self, file_format: &dyn FileFormat) -> meta::Fields {
        Meta::make_object()
            .field("unknown", &self.unknown)
            .with_mut(|b| file_format.extra_to_meta(&self.extra, b))
            .field("objects", &self.objects)
            .field("instances", &self.instances)
            .build_fields()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Object {
    pub unknown: u16,
    pub pos: [f32; 3],
    pub size: [f32; 3],
    pub quads: Vec<Quad>,
}

impl FromMeta<'_> for Object {
    fn from_meta(meta: &Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
        meta.parse_object(|m| Ok(Object {
            unknown: m.expect_field::<i32>("unknown")? as u16,
            pos: m.expect_field("pos")?,
            size: m.expect_field("size")?,
            quads: m.expect_field("quads")?,
        }))
    }
}

impl ToMeta for Object {
    fn to_meta(&self) -> Meta {
        Meta::make_object()
            .field("unknown", &(self.unknown as i32))
            .field("pos", &self.pos)
            .field("size", &self.size)
            .field("quads", &self.quads)
            .build()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Quad {
    pub anm_script: u16,
    pub extra: QuadExtra,
}

#[derive(Debug, Clone, PartialEq)]
pub enum QuadExtra {
    /// Type 0 quad.
    Rect {
        pos: [f32; 3],
        size: [f32; 2],
    },
    /// Type 1 quad. Only available in IN and PoFV.
    Strip {
        start: [f32; 3],
        end: [f32; 3],
        width: f32,
    }
}

impl FromMeta<'_> for Quad {
    fn from_meta(meta: &Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
        meta.parse_variant()?
            .variant("rect", |m| Ok(Quad {
                anm_script: m.expect_field::<i32>("anm_script")? as u16,
                extra: QuadExtra::Rect {
                    pos: m.expect_field("pos")?,
                    size: m.expect_field("size")?,
                },
            }))
            .variant("strip", |m| Ok(Quad {
                anm_script: m.expect_field::<i32>("anm_script")? as u16,
                extra: QuadExtra::Strip {
                    start: m.expect_field("start")?,
                    end: m.expect_field("end")?,
                    width: m.expect_field("width")?,
                },
            }))
            .finish()
    }
}

impl ToMeta for Quad {
    fn to_meta(&self) -> Meta {
        let variant = match self.extra {
            QuadExtra::Rect { .. } => "rect",
            QuadExtra::Strip { .. } => "strip",
        };

        Meta::make_variant(variant)
            .field("anm_script", &(self.anm_script as i32))
            .with_mut(|b| match &self.extra {
                QuadExtra::Rect { pos, size } => {
                    b.field("pos", pos);
                    b.field("size", size);
                },
                QuadExtra::Strip { start, end, width } => {
                    b.field("start", start);
                    b.field("end", end);
                    b.field("width", width);
                },
            })
            .build()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Instance {
    pub object: Sp<Ident>,
    pub unknown: u16,
    pub pos: [f32; 3],
}

impl FromMeta<'_> for Instance {
    fn from_meta(meta: &Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
        meta.parse_any_variant(|ident, meta| Ok(Instance {
            object: ident.clone(),
            unknown: meta.get_field::<i32>("unknown")?.unwrap_or(256) as u16,
            pos: meta.expect_field("pos")?,
        }))
    }
}

impl ToMeta for Instance {
    fn to_meta(&self) -> Meta {
        Meta::make_variant(&self.object)
            .field_default("unknown", &(self.unknown as i32), &256)
            .field("pos", &self.pos)
            .build()
    }
}

// =============================================================================

fn decompile_std(
    std: &StdFile,
    emitter: &impl Emitter,
    format: &dyn FileFormat,
    ctx: &mut CompilerContext,
    decompile_kind: DecompileKind,
) -> Result<ast::ScriptFile, ErrorReported> {
    let instr_format = format.instr_format();
    let script = &std.script;

    let code = llir::Raiser::new(&ctx.emitter).raise_instrs_to_sub_ast(emitter, instr_format, script, &ctx.defs)?;

    let mut script = ast::ScriptFile {
        mapfiles: ctx.mapfiles_to_ast(),
        image_sources: vec![],
        items: vec! [
            sp!(ast::Item::Meta {
                keyword: sp!(ast::MetaKeyword::Meta),
                fields: sp!(std.make_meta(format)),
            }),
            sp!(ast::Item::AnmScript {
                number: None,
                ident: sp!("main".parse().unwrap()),
                code: ast::Block(code),
                keyword: sp!(()),
            }),
        ],
    };
    crate::passes::postprocess_decompiled(&mut script, ctx, decompile_kind)?;
    Ok(script)
}

fn unsupported(span: &crate::pos::Span) -> Diagnostic {
    error!(
        message("feature not supported by format"),
        primary(span, "not supported by STD files"),
    )
}

fn compile_std(
    format: &dyn FileFormat,
    script: &ast::ScriptFile,
    ctx: &mut CompilerContext,
) -> Result<StdFile, ErrorReported> {
    let script = {
        let mut script = script.clone();

        crate::passes::resolve_names::assign_res_ids(&mut script, ctx)?;
        crate::passes::resolve_names::run(&script, ctx)?;
        crate::passes::type_check::run(&script, ctx)?;
        crate::passes::evaluate_const_vars::run(ctx)?;
        crate::passes::const_simplify::run(&mut script, ctx)?;
        crate::passes::desugar_blocks::run(&mut script, ctx)?;
        script
    };

    let emit = |e| ctx.emitter.emit(e);
    let (meta, main_sub) = {
        // FIXME: copypasta with msg.rs  (both languages appear to want very similar things)
        let (mut found_meta, mut found_main_sub) = (None, None);
        for item in script.items.iter() {
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
                    message("unexpected '{}' in STD file", keyword),
                    primary(keyword, "not valid in STD files"),
                ))),
                ast::Item::AnmScript { number: Some(number), .. } => return Err(emit(error!(
                    message("unexpected numbered script in STD file"),
                    primary(number, "unexpected number"),
                ))),
                ast::Item::AnmScript { number: None, ident, code, .. } => {
                    if ident != "main" {
                        return Err(emit(error!(
                            message("STD script must be called 'main'"),
                            primary(ident, "invalid name for STD script"),
                        )));
                    }
                    if let Some((prev_ident, _)) = found_main_sub.replace((ident, code)) {
                        return Err(emit(error!(
                            message("redefinition of script 'main'"),
                            primary(ident, "this defines a script called 'main'..."),
                            secondary(prev_ident, "...but 'main' was already defined here"),
                        )));
                    }
                },
                ast::Item::ConstVar { .. } => {},
                ast::Item::Func { .. } => return Err(emit(unsupported(&item.span))),
            }
        }
        match (found_meta, found_main_sub) {
            (Some((_, meta)), Some((_, main))) => (meta, main),
            (None, _) => return Err(emit(error!("missing 'main' sub"))),
            (Some(_), None) => return Err(emit(error!("missing 'meta' section"))),
        }
    };

    let mut out = StdFile::init_from_meta(format, meta).map_err(|e| ctx.emitter.emit(e))?;
    out.script = crate::llir::lower_sub_ast_to_instrs(format.instr_format(), &main_sub.0, ctx)?;
    Ok(out)
}

// =============================================================================

fn read_std(reader: &mut BinReader, emitter: &impl Emitter, format: &dyn FileFormat) -> ReadResult<StdFile> {
    let start_pos = reader.pos()?;

    let num_objects = reader.read_u16()? as usize;
    let num_quads = reader.read_u16()? as usize;
    let instances_offset = reader.read_u32()? as u64;
    let script_offset = reader.read_u32()? as u64;
    let unknown = reader.read_u32()?;
    let extra = format.read_extra(reader, emitter)?;

    let object_offsets = (0..num_objects).map(|_| reader.read_u32()).collect::<ReadResult<Vec<_>>>()?;
    let objects = (0..num_objects)
        .map(|i| {
            let key = sp!(format!("object{}", i).parse::<Ident>().unwrap());

            reader.seek_to(start_pos + object_offsets[i] as u64)?;

            let expected_id = i;
            let value = emitter.chain_with(|f| write!(f, "object at index {}", i), |emitter| {
                read_object(reader, emitter, expected_id)
            })?;
            Ok((key, value))
        }).collect::<ReadResult<IndexMap<_, _>>>()?;
    assert_eq!(num_quads, objects.values().map(|x| x.quads.len()).sum::<usize>());

    let instances = {
        reader.seek_to(start_pos + instances_offset)?;
        let mut vec = vec![];
        while let Some(instance) = read_instance(reader, emitter, &objects)? {
            vec.push(instance);
        }
        vec
    };

    reader.seek_to(start_pos + script_offset)?;
    let script = llir::read_instrs(reader, emitter, format.instr_format(), 0, None)?;

    let binary_filename = Some(reader.display_filename().to_string());
    Ok(StdFile { unknown, extra, objects, instances, script, binary_filename })
}

fn write_std(
    f: &mut BinWriter,
    emitter: &impl Emitter,
    format: &dyn FileFormat,
    std: &StdFile,
) -> WriteResult {
    let start_pos = f.pos()?;

    f.write_u16(std.objects.len() as u16)?;
    f.write_u16(std.objects.values().map(|x| x.quads.len()).sum::<usize>() as u16)?;

    let instances_offset_pos = f.pos()?;
    f.write_u32(0)?;
    let script_offset_pos = f.pos()?;
    f.write_u32(0)?;

    f.write_u32(std.unknown)?;

    format.write_extra(f, emitter, &std.extra)?;

    let object_offsets_pos = f.pos()?;
    for _ in &std.objects {
        f.write_u32(0)?;
    }

    let mut object_offsets = vec![];
    for (object_id, object) in std.objects.values().enumerate() {
        object_offsets.push(f.pos()? - start_pos);
        write_object(f, emitter, &*format, object_id, object)?;
    }

    let instances_offset = f.pos()? - start_pos;
    for instance in &std.instances {
        write_instance(f, emitter, instance, &std.objects)?;
    }
    write_terminal_instance(f)?;

    let instr_format = format.instr_format();

    let script_offset = f.pos()? - start_pos;
    llir::write_instrs(f, emitter, instr_format, &std.script)?;

    let end_pos = f.pos()?;
    f.seek_to(instances_offset_pos)?;
    f.write_u32(instances_offset as u32)?;
    f.seek_to(script_offset_pos)?;
    f.write_u32(script_offset as u32)?;
    f.seek_to(object_offsets_pos)?;
    for offset in object_offsets {
        f.write_u32(offset as u32)?;
    }
    f.seek_to(end_pos)?;
    Ok(())
}

fn read_string_128(r: &mut BinReader, emitter: &dyn Emitter) -> ReadResult<Sp<String>> {
    r.read_cstring_masked_exact(128, AcceleratingByteMask::constant(0x00), emitter)?
        .decode(DEFAULT_ENCODING).map(|x| sp!(x))
        .map_err(|e| emitter.as_sized().emit(e))
}
fn write_string_128<S: AsRef<str>>(f: &mut BinWriter, emitter: &dyn Emitter, s: &Sp<S>) -> WriteResult {
    let encoded = Encoded::encode(&s, DEFAULT_ENCODING).map_err(|e| emitter.as_sized().emit(e))?;
    if encoded.len() >= 128 {
        return Err(emitter.as_sized().emit(error!(
            message("string too long for STD header"),
            primary(s, "{} bytes (max allowed: 127)", encoded.len()),
        )));
    }
    f.write_cstring_masked(&encoded, 128, AcceleratingByteMask::constant(0x00))?;
    Ok(())
}

fn read_object(f: &mut BinReader, emitter: &impl Emitter, expected_id: usize) -> ReadResult<Object> {
    let id = f.read_u16()?;
    if id as usize != expected_id {
        emitter.emit(warning!("object has non-sequential id (expected {}, got {})", expected_id, id)).ignore();
    }

    let unknown = f.read_u16()?;
    let pos = f.read_f32s_3()?;
    let size = f.read_f32s_3()?;
    let mut quads = vec![];
    while let Some(quad) = read_quad(f, emitter)? {
        quads.push(quad);
    }
    Ok(Object { unknown, pos, size, quads })
}

fn write_object(f: &mut BinWriter, emitter: &impl Emitter, format: &dyn FileFormat, id: usize, x: &Object) -> WriteResult {
    f.write_u16(id as u16)?;
    f.write_u16(x.unknown)?;
    f.write_f32s(&x.pos)?;
    f.write_f32s(&x.size)?;
    for quad in &x.quads {
        write_quad(f, emitter, format, quad)?;
    }
    write_terminal_quad(f)
}

fn read_quad(f: &mut BinReader, emitter: &impl Emitter) -> ReadResult<Option<Quad>> {
    let kind = f.read_i16()?;
    let size = f.read_u16()?;
    match (kind, size) {
        (-1, 4) => return Ok(None), // no more quads
        (0, 0x1c) => {},
        (1, 0x24) => {},
        (-1, _) | (0, _) | (1, _) => {
            return Err(emitter.emit(error!("unexpected size for type {} quad: {:#x}", kind, size)));
        },
        _ => return Err(emitter.emit(error!("unknown quad type: {}", kind))),
    };

    let anm_script = f.read_u16()?;
    match f.read_u16()? {
        0 => {},  // This word is zero in the file, and used to store an index in-game.
        s => return Err(emitter.emit(warning!("unexpected data in quad index field: {:#04x}", s))),
    };

    Ok(Some(Quad {
        anm_script,
        extra: match kind {
            0 => QuadExtra::Rect {
                pos: f.read_f32s_3()?,
                size: f.read_f32s_2()?,
            },
            1 => QuadExtra::Strip {
                start: f.read_f32s_3()?,
                end: f.read_f32s_3()?,
                width: f.read_f32()?,
            },
            _ => unreachable!(),
        },
    }))
}

fn write_quad(f: &mut BinWriter, emitter: &impl Emitter, format: &dyn FileFormat, quad: &Quad) -> WriteResult {
    let (kind, size) = match quad.extra {
        QuadExtra::Rect { .. } => (0, 0x1c),
        QuadExtra::Strip { .. } => (1, 0x24),
    };
    f.write_i16(kind)?;
    f.write_u16(size)?;
    f.write_u16(quad.anm_script)?;
    f.write_u16(0)?;
    match quad.extra {
        QuadExtra::Rect { pos, size } => {
            f.write_f32s(&pos)?;
            f.write_f32s(&size)?;
        },
        QuadExtra::Strip { start, end, width } => {
            if !format.has_strips() {
                // FIXME: Could be better with a span, maybe check earlier
                emitter.emit(warning!("'strip' quads can only be used in TH08 and TH09!")).ignore();
            }
            f.write_f32s(&start)?;
            f.write_f32s(&end)?;
            f.write_f32(width)?;
        },
    }
    Ok(())
}
fn write_terminal_quad(f: &mut BinWriter) -> WriteResult {
    f.write_i16(-1)?;
    f.write_u16(0x4)?; // size
    Ok(())
}


fn read_instance(f: &mut BinReader, emitter: &impl Emitter, objects: &IndexMap<Sp<Ident>, Object>) -> ReadResult<Option<Instance>> {
    let object_id = f.read_u16()?;
    let unknown = f.read_u16()?;
    if object_id == 0xffff {
        return Ok(None);
    }
    let object = match objects.get_index(object_id as usize) {
        Some((ident, _)) => ident.clone(),
        None => return Err(emitter.emit(error!("object index too large! ({}, but there are only {} objects)", object_id, objects.len()))),
    };
    let pos = f.read_f32s_3()?;
    Ok(Some(Instance { object, unknown, pos }))
}

fn write_instance(f: &mut BinWriter, emitter: &dyn Emitter, inst: &Instance, objects: &IndexMap<Sp<Ident>, Object>) -> WriteResult {
    match objects.get_index_of(&inst.object) {
        Some(object_index) => f.write_u16(object_index as u16)?,
        None => return Err(emitter.as_sized().emit(error!(
            message("no object named {}", inst.object),
            primary(&inst.object, "not an object"),
        ))),
    }
    f.write_u16(inst.unknown)?;
    f.write_f32s(&inst.pos)?;
    Ok(())
}
fn write_terminal_instance(f: &mut BinWriter) -> WriteResult {
    for _ in 0..4 {
        f.write_i32(-1)?;
    }
    Ok(())
}

fn game_format(game: Game) -> Box<dyn FileFormat> {
    if Game::Th095 <= game {
        let instr_format = InstrFormat10 { game };
        Box::new(FileFormat10 { instr_format })
    } else {
        let has_strips = match game {
            Game::Th06 | Game::Th07 => false,
            Game::Th08 | Game::Th09 => true,
            _ => unreachable!(),
        };

        let instr_format = InstrFormat06 { game };
        Box::new(FileFormat06 { has_strips, instr_format })
    }
}

pub fn game_core_mapfile(game: Game) -> crate::Eclmap {
    super::core_mapfiles::std::core_signatures(game).to_mapfile(game)
}

// =============================================================================

/// STD format, EoSD to PoFV.
struct FileFormat06 {
    has_strips: bool,
    instr_format: InstrFormat06,
}
/// STD format, StB to present.
struct FileFormat10 {
    instr_format: InstrFormat10,
}

trait FileFormat {
    fn extra_from_meta<'m>(&self, meta: &mut meta::ParseObject<'m>) -> Result<StdExtra, FromMetaError<'m>>;
    fn extra_to_meta(&self, extra: &StdExtra, b: &mut meta::BuildObject);
    fn read_extra(&self, f: &mut BinReader, emitter: &dyn Emitter) -> ReadResult<StdExtra>;
    fn write_extra(&self, f: &mut BinWriter, emitter: &dyn Emitter, x: &StdExtra) -> WriteResult;
    fn instr_format(&self) -> &dyn InstrFormat;
    fn has_strips(&self) -> bool;
}

impl FileFormat for FileFormat06 {
    fn extra_from_meta<'m>(&self, m: &mut meta::ParseObject<'m>) -> Result<StdExtra, FromMetaError<'m>> {
        Ok(StdExtra::Th06 {
            stage_name: m.expect_field("stage_name")?,
            bgm: m.expect_field("bgm")?,
        })
    }

    fn extra_to_meta(&self, extra: &StdExtra, b: &mut meta::BuildObject) {
        match extra {
            StdExtra::Th10 { .. } => unreachable!(),
            StdExtra::Th06 { stage_name, bgm } => {
                b.field("stage_name", &stage_name.value);
                b.field("bgm", bgm);
            },
        }
    }

    fn read_extra(&self, f: &mut BinReader, emitter: &dyn Emitter) -> ReadResult<StdExtra> {
        let stage_name = read_string_128(f, emitter)?;
        let bgm_names = (0..4).map(|_| read_string_128(f, emitter)).collect::<Result<Vec<_>, _>>()?;
        let bgm_paths = (0..4).map(|_| read_string_128(f, emitter)).collect::<Result<Vec<_>, _>>()?;
        let mut bgms = bgm_names.into_iter().zip(bgm_paths).map(|(name, path)| Std06Bgm { name, path });
        Ok(StdExtra::Th06 {
            stage_name,
            bgm: [bgms.next().unwrap(), bgms.next().unwrap(), bgms.next().unwrap(), bgms.next().unwrap()],
        })
    }

    fn write_extra(&self, f: &mut BinWriter, emitter: &dyn Emitter, x: &StdExtra) -> WriteResult {
        match x {
            StdExtra::Th06 { stage_name, bgm } => {
                write_string_128(f, emitter, stage_name)?;
                let bgm_names = bgm.iter().map(|Std06Bgm { name, .. }| name);
                let bgm_paths = bgm.iter().map(|Std06Bgm { path, .. }| path);
                for s in bgm_names.chain(bgm_paths) {
                    write_string_128(f, emitter, s)?;
                }
            },
            StdExtra::Th10 { .. } => unreachable!(),
        };
        Ok(())
    }

    fn instr_format(&self) -> &dyn InstrFormat { &self.instr_format }
    fn has_strips(&self) -> bool { self.has_strips }
}

impl FileFormat for FileFormat10 {
    fn extra_from_meta<'m>(&self, m: &mut meta::ParseObject<'m>) -> Result<StdExtra, FromMetaError<'m>> {
        Ok(StdExtra::Th10 {
            anm_path: m.expect_field("anm_path")?,
        })
    }

    fn extra_to_meta(&self, extra: &StdExtra, b: &mut meta::BuildObject) {
        match extra {
            StdExtra::Th10 { anm_path } => { b.field("anm_path", &anm_path.value); },
            StdExtra::Th06 { .. } => unreachable!(),
        }
    }

    fn read_extra(&self, f: &mut BinReader, emitter: &dyn Emitter) -> ReadResult<StdExtra> {
        Ok(StdExtra::Th10 { anm_path: read_string_128(f, emitter)? })
    }

    fn write_extra(&self, f: &mut BinWriter, emitter: &dyn Emitter, x: &StdExtra) -> WriteResult {
        match x {
            StdExtra::Th10 { anm_path } => write_string_128(f, emitter, anm_path)?,
            StdExtra::Th06 { .. } => unreachable!(),
        };
        Ok(())
    }

    fn instr_format(&self) -> &dyn InstrFormat { &self.instr_format }
    fn has_strips(&self) -> bool { false }
}

pub struct InstrFormat06 { game: Game }
pub struct InstrFormat10 { game: Game }

impl InstrFormat for InstrFormat06 {
    fn intrinsic_opcode_pairs(&self) -> Vec<(llir::IntrinsicInstrKind, u16)> {
        if Game::Th07 <= self.game && self.game <= Game::Th09 {
            vec![
                (llir::IntrinsicInstrKind::Jmp, 4),
                (llir::IntrinsicInstrKind::InterruptLabel, 31),
            ]
        } else {
            vec![]  // lul
        }
    }

    fn instr_header_size(&self) -> usize { 8 }

    fn read_instr(&self, f: &mut BinReader, _: &dyn Emitter) -> ReadResult<ReadInstr> {
        let time = f.read_i32()?;
        let opcode = f.read_i16()?;
        let argsize = f.read_u16()?;
        if opcode == -1 {
            return Ok(ReadInstr::Terminal)
        }
        assert_eq!(argsize, 12);  // FIXME make error if < 12, warning if > 12

        let args_blob = f.read_byte_vec(12)?;
        Ok(ReadInstr::Instr(RawInstr { time, opcode: opcode as u16, param_mask: 0, args_blob }))
    }

    fn write_instr(&self, f: &mut BinWriter, _: &dyn Emitter, instr: &RawInstr) -> WriteResult {
        f.write_i32(instr.time)?;
        f.write_u16(instr.opcode)?;
        f.write_u16(12)?;  // this version writes argsize rather than instr size
        assert_eq!(instr.args_blob.len(), 12);
        f.write_all(&instr.args_blob)?;
        Ok(())
    }

    fn write_terminal_instr(&self, f: &mut BinWriter, _: &dyn Emitter) -> WriteResult {
        for _ in 0..5 {
            f.write_i32(-1)?;
        }
        Ok(())
    }

    fn encode_label(&self, offset: u64) -> u32 {
        assert_eq!(offset % 20, 0);
        (offset / 20) as u32
    }
    fn decode_label(&self, bits: u32) -> u64 {
        (bits * 20) as u64
    }
}

impl InstrFormat for InstrFormat10 {
    fn intrinsic_opcode_pairs(&self) -> Vec<(llir::IntrinsicInstrKind, u16)> {
        let mut out = vec![(llir::IntrinsicInstrKind::Jmp, 1)];

        // TH095 and TH10 are missing this
        if Game::Th11 <= self.game {
            out.push((llir::IntrinsicInstrKind::InterruptLabel, 16));
        }
        out
    }

    fn instr_header_size(&self) -> usize { 8 }

    fn read_instr(&self, f: &mut BinReader, _: &dyn Emitter) -> ReadResult<ReadInstr> {
        let time = f.read_i32()?;
        let opcode = f.read_i16()?;
        let size = f.read_u16()? as usize;
        if opcode == -1 {
            return Ok(ReadInstr::Terminal)
        }

        let args_blob = f.read_byte_vec(size - self.instr_header_size())?;
        Ok(ReadInstr::Instr(RawInstr { time, opcode: opcode as u16, param_mask: 0, args_blob }))
    }

    fn write_instr(&self, f: &mut BinWriter, _: &dyn Emitter, instr: &RawInstr) -> WriteResult {
        f.write_i32(instr.time)?;
        f.write_u16(instr.opcode)?;
        f.write_u16(self.instr_size(instr) as u16)?;
        f.write_all(&instr.args_blob)?;
        Ok(())
    }

    fn write_terminal_instr(&self, f: &mut BinWriter, _: &dyn Emitter) -> WriteResult {
        for _ in 0..5 {
            f.write_i32(-1)?;
        }
        Ok(())
    }
}
