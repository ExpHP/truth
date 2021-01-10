use std::fmt;
use std::io;
use std::num::NonZeroUsize;

use anyhow::Context;
use bstr::BString;
use enum_map::EnumMap;
use indexmap::IndexMap;

use crate::ast;
use crate::binary_io::{bail, BinRead, BinWrite, ReadResult, WriteResult};
use crate::error::{CompileError, GatherErrorIteratorExt, SimpleError};
use crate::game::Game;
use crate::ident::Ident;
use crate::llir::{self, Instr, InstrFormat, IntrinsicInstrKind};
use crate::meta::{self, FromMeta, FromMetaError, Meta, ToMeta};
use crate::pos::Sp;
use crate::type_system::{RegsAndInstrs, ScalarType, TypeSystem};
use crate::passes::DecompileKind;

// =============================================================================

/// Game-independent representation of an ANM file.
#[derive(Debug, Clone)]
pub struct AnmFile {
    pub entries: Vec<Entry>,
}

impl AnmFile {
    pub fn decompile_to_ast(&self, game: Game, ty_ctx: &TypeSystem, decompile_kind: DecompileKind) -> Result<ast::Script, SimpleError> {
        decompile(&game_format(game), self, &ty_ctx.regs_and_instrs, decompile_kind)
    }

    pub fn compile_from_ast(game: Game, ast: &ast::Script, ty_ctx: &mut TypeSystem) -> Result<Self, CompileError> {
        compile(&game_format(game), ast, ty_ctx)
    }

    pub fn merge(&mut self, other: &Self) -> Result<(), CompileError> {
        merge(self, other)
    }

    pub fn write_to_stream(&self, mut w: impl io::Write + io::Seek, game: Game) -> WriteResult {
        write_anm(&mut w, &game_format(game), self)
    }

    pub fn read_from_bytes(game: Game, bytes: &[u8]) -> ReadResult<Self> {
        read_anm(&game_format(game), bytes)
    }
}

#[derive(Debug, Clone)]
pub struct Entry {
    pub specs: EntrySpecs,
    pub texture: Option<Texture>,
    pub path: BString,
    pub path_2: Option<BString>,
    pub scripts: IndexMap<Sp<Ident>, Script>,
    pub sprites: IndexMap<Sp<Ident>, Sprite>,
}

#[derive(Debug, Clone)]
pub struct Script {
    pub id: i32,
    pub instrs: Vec<Instr>,
}

#[derive(Debug, Clone)]
pub struct EntrySpecs {
    pub width: u32,
    pub height: u32,
    pub format: u32,
    pub colorkey: u32, // Only in old format
    pub offset_x: u32,
    pub offset_y: u32,
    pub memory_priority: u32,
    pub has_data: bool,
    pub low_res_scale: bool,
}

impl Entry {
    fn make_meta(&self) -> meta::Fields {
        let EntrySpecs {
            width, height, format, colorkey, offset_x, offset_y,
            memory_priority, has_data, low_res_scale,
        } = &self.specs;

        Meta::make_object()
            .field("format", format)
            .field("width", width)
            .field("height", height)
            .field("colorkey", colorkey)
            .field("offset_x", offset_x)
            .field("offset_y", offset_y)
            .field("memory_priority", memory_priority)
            .field("low_res_scale", low_res_scale)
            .field("has_data", has_data)
            .field("path", &self.path)
            .with_mut(|b| if let Some(texture) = &self.texture {
                b.field("thtx_format", &texture.thtx.format);
                b.field("thtx_width", &texture.thtx.width);
                b.field("thtx_height", &texture.thtx.height);
            })
            .opt_field("path_2", self.path_2.as_ref())
            .field("sprites", &self.sprites)
            .build_fields()
    }

    fn from_fields(fields: &Sp<meta::Fields>) -> Result<Self, FromMetaError<'_>> {
        meta::ParseObject::scope(fields, |m| {
            let format = m.expect_field("format")?;
            let width = m.expect_field("width")?;
            let height = m.expect_field("height")?;
            let colorkey = m.expect_field("colorkey")?;
            let offset_x = m.expect_field("offset_x")?;
            let offset_y = m.expect_field("offset_y")?;
            let memory_priority = m.expect_field("memory_priority")?;
            let low_res_scale = m.expect_field("low_res_scale")?;
            let has_data = m.expect_field("has_data")?;
            let path = m.expect_field("path")?;
            let path_2 = m.get_field("path_2")?;
            let texture = None;
            m.allow_field("thtx_format")?;
            m.allow_field("thtx_width")?;
            m.allow_field("thtx_height")?;
            let sprites = m.expect_field("sprites")?;

            let specs = EntrySpecs {
                width, height, format, colorkey, offset_x, offset_y,
                memory_priority, has_data, low_res_scale,
            };
            let scripts = Default::default();
            Ok(Entry { specs, texture, path, path_2, scripts, sprites })
        })
    }
}

#[derive(Clone)]
pub struct Texture {
    pub thtx: ThtxHeader,
    pub data: Vec<u8>,
}

#[derive(Debug, Clone)]
pub struct ThtxHeader {
    pub format: u32,
    pub width: u32,
    pub height: u32,
}

impl fmt::Debug for Texture {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Texture")
            .field("thtx", &self.thtx)
            .field("data", &(..))
            .finish()
    }
}

#[derive(Debug, Clone)]
pub struct Sprite {
    pub id: u32,
    pub offset: [f32; 2],
    pub size: [f32; 2],
}

impl ToMeta for Sprite {
    fn to_meta(&self) -> Meta {
        let &Sprite { id, offset, size } = self;
        Meta::make_object()
            .field("id", &id)
            .field("x", &offset[0])
            .field("y", &offset[1])
            .field("w", &size[0])
            .field("h", &size[1])
            .build()
    }
}

impl FromMeta for Sprite {
    fn from_meta(meta: &Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
        meta.parse_object(|m| Ok(Sprite {
            id: m.expect_field("id")?,
            offset: [m.expect_field("x")?, m.expect_field("y")?],
            size: [m.expect_field("w")?, m.expect_field("h")?],
        }))
    }
}

// =============================================================================

fn decompile(format: &FileFormat, anm_file: &AnmFile, ty_ctx: &RegsAndInstrs, decompile_kind: DecompileKind) -> Result<ast::Script, SimpleError> {
    let instr_format = format.instr_format();

    let mut items = vec![];
    for entry in &anm_file.entries {
        items.push(sp!(ast::Item::Meta {
            keyword: sp!(ast::MetaKeyword::Entry),
            name: None,
            fields: sp!(entry.make_meta()),
        }));

        for (name, &Script { id, ref instrs }) in &entry.scripts {
            let code = llir::raise_instrs_to_sub_ast(instr_format, instrs, ty_ctx)?;

            items.push(sp!(ast::Item::AnmScript {
                number: Some(sp!(id)),
                name: name.clone(),
                code: ast::Block(code),
            }));
        }
    }
    let mut out = ast::Script { items, mapfiles: ty_ctx.mapfiles_to_ast() };
    crate::passes::postprocess_decompiled(&mut out, decompile_kind)?;
    Ok(out)
}

fn merge(dest_file: &mut AnmFile, src_file: &AnmFile) -> Result<(), CompileError> {
    // let dest = dest_file.entries.last().unwrap();
    // eprintln!("{:?}", dest.scripts.len());
    // eprintln!("{:?}", dest.scripts[dest.scripts.len()-2]);
    // let dest = src_file.entries.last().unwrap();
    // eprintln!("{:?}", dest.scripts.len());
    // eprintln!("{:?}", dest.scripts[dest.scripts.len()-2]);

    for (dest_entry, src_entry) in zip!(&mut dest_file.entries, &src_file.entries) {
        dest_entry.scripts = src_entry.scripts.clone();
    }
    if dest_file.entries.len() < src_file.entries.len() {
        dest_file.entries.extend(src_file.entries[src_file.entries.len()..].iter().cloned())
    }
    Ok(())
}

fn compile(format: &FileFormat, ast: &ast::Script, ty_ctx: &mut TypeSystem) -> Result<AnmFile, CompileError> {
    let instr_format = format.instr_format();

    let ast = {
        use ast::VisitMut;

        let gensym_ctx = crate::ident::GensymContext::new();

        let mut ast = ast.clone();

        let mut visitor = crate::passes::const_simplify::Visitor::new();
        visitor.visit_script(&mut ast);
        visitor.finish()?;

        ty_ctx.resolve_names(&mut ast)?;

        let mut visitor = crate::passes::compile_loop::Visitor::new(&gensym_ctx);
        visitor.visit_script(&mut ast);
        visitor.finish()?;

        ast
    };

    // group scripts by entry
    let mut groups = vec![];
    let mut cur_entry = None;
    let mut cur_group = vec![];
    for item in &ast.items {
        match &item.value {
            ast::Item::Meta { keyword: sp_pat!(ast::MetaKeyword::Entry), fields, .. } => {
                if let Some(prev_entry) = cur_entry.take() {
                    groups.push((prev_entry, cur_group));
                }
                cur_entry = Some(fields);
                cur_group = vec![];
            },
            &ast::Item::AnmScript { number, ref name, ref code } => {
                if cur_entry.is_none() { return Err(error!(
                    message("orphaned ANM script with no entry"),
                    primary(item, "orphaned script"),
                    note("at least one `entry` must come before scripts in an ANM file"),
                ))}
                cur_group.push((number, name, code));
            },
            _ => return Err(error!(
                message("feature not supported by format"),
                primary(item, "not supported by ANM files"),
            )),
        }
    }
    match cur_entry {
        None => return Err(error!("empty ANM file")),
        Some(cur_entry) => groups.push((cur_entry, cur_group)),  // last group
    }

    let mut next_auto_id = 0;
    let entries = groups.into_iter().map(|(entry_fields, ast_scripts)| {
        let mut entry = Entry::from_fields(entry_fields)?;
        for (given_number, name, code) in ast_scripts {
            let id = given_number.map(|sp| sp.value).unwrap_or(next_auto_id);
            next_auto_id = id + 1;

            match entry.scripts.entry(name.clone()) {
                indexmap::map::Entry::Vacant(e) => {
                    let instrs = llir::lower_sub_ast_to_instrs(instr_format, &code.0, ty_ctx)?;
                    e.insert(Script { id, instrs });
                },
                indexmap::map::Entry::Occupied(e) => {
                    let old = e.key();
                    return Err(error!{
                        message("duplicate script '{}'", name),
                        primary(name, "redefined here"),
                        secondary(old, "originally defined here"),
                    });
                },
            }
        }
        Ok(entry)
    }).collect_with_recovery()?;
    Ok(AnmFile { entries })
}

// =============================================================================

#[derive(Debug, Clone)]
struct EntryHeaderData {
    version: u32,
    num_sprites: u32,
    num_scripts: u32,
    width: u32,
    height: u32,
    format: u32,
    name_offset: usize,
    secondary_name_offset: Option<NonZeroUsize>, // EoSD only?
    colorkey: u32, // Only in old format
    offset_x: u32,
    offset_y: u32,
    memory_priority: u32,
    thtx_offset: Option<NonZeroUsize>,
    has_data: u32,
    low_res_scale: u32,
    next_offset: u32,
}

fn read_anm(format: &FileFormat, mut entry_bytes: &[u8]) -> ReadResult<AnmFile> {
    let instr_format = format.instr_format();

    let mut entries = vec![];
    let mut next_script_index = 0;
    let mut next_sprite_index = 0;
    loop {
        let mut f = entry_bytes;

        // 64 byte header regardless of version
        let header_data = format.read_header(&mut f)?;
        if header_data.has_data != header_data.has_data % 2 {
            fast_warning!("non-boolean value found for 'has_data': {}", header_data.has_data);
        }
        if header_data.low_res_scale != header_data.low_res_scale % 2 {
            fast_warning!("non-boolean value found for 'low_res_scale': {}", header_data.low_res_scale);
        }

        let sprite_offsets = (0..header_data.num_sprites).map(|_| f.read_u32()).collect::<ReadResult<Vec<_>>>()?;
        let script_ids_and_offsets = (0..header_data.num_scripts).map(|_| {
            Ok((f.read_i32()?, f.read_u32()? as usize))
        }).collect::<ReadResult<Vec<_>>>()?;
        // eprintln!("{:?}", header_data);
        // eprintln!("{:?}", sprite_offsets);
        // eprintln!("{:?}", script_ids_and_offsets);

        let path = (&entry_bytes[header_data.name_offset..]).read_cstring(16)?;
        let path_2 = {
            header_data.secondary_name_offset
                .map(|x| (&entry_bytes[x.get()..]).read_cstring(16)).transpose()?
        };

        let sprites = sprite_offsets.iter().map(|&offset| {
            let key = sp!(auto_sprite_name(next_sprite_index as u32));
            let value = read_sprite(&mut &entry_bytes[offset as usize..])?;
            next_sprite_index += 1;
            Ok((key, value))
        }).collect::<ReadResult<IndexMap<_, _>>>()?;

        // Blame StB
        let mut all_offsets = vec![header_data.name_offset];
        all_offsets.extend(header_data.thtx_offset.map(NonZeroUsize::get));
        all_offsets.extend(header_data.secondary_name_offset.map(NonZeroUsize::get));
        all_offsets.extend(sprite_offsets.iter().map(|&offset| offset as usize));
        all_offsets.extend(script_ids_and_offsets.iter().map(|&(_, offset)| offset as usize));

        let scripts = script_ids_and_offsets.iter().map(|&(id, offset)| {
            let key = sp!(auto_script_name(next_script_index));
            next_script_index += 1;

            let end_offset = all_offsets.iter().copied().filter(|&x| x > offset).min();

            let instrs = {
                llir::read_instrs(&mut &entry_bytes[offset..], instr_format, offset, end_offset)
                    .with_context(|| format!("while reading {}", key))?
            };
            Ok((key, Script { id, instrs }))
        }).collect::<ReadResult<IndexMap<_, _>>>()?;

        let expect_no_texture = header_data.has_data == 0 || path.starts_with(b"@");
        if expect_no_texture != header_data.thtx_offset.is_none() {
            bail!("inconsistency between thtx_offset and has_data/name");
        }

        let texture = match header_data.thtx_offset {
            None => None,
            Some(n) => Some(read_texture(&mut &entry_bytes[n.get()..])?),
        };
        let specs = EntrySpecs {
            width: header_data.width, height: header_data.height,
            format: header_data.format, colorkey: header_data.colorkey,
            offset_x: header_data.offset_x, offset_y: header_data.offset_y,
            memory_priority: header_data.memory_priority,
            has_data: header_data.has_data != 0,
            low_res_scale: header_data.low_res_scale != 0,
        };

        entries.push(Entry { texture, specs, path, path_2, sprites, scripts });

        if header_data.next_offset == 0 {
            break;
        }
        entry_bytes = &entry_bytes[header_data.next_offset as usize..];
    }
    Ok(AnmFile { entries })
}

fn auto_sprite_name(i: u32) -> Ident {
    format!("sprite{}", i).parse::<Ident>().unwrap()
}
fn auto_script_name(i: u32) -> Ident {
    format!("script{}", i).parse::<Ident>().unwrap()
}

fn write_anm(f: &mut dyn BinWrite, format: &FileFormat, file: &AnmFile) -> WriteResult {
    let mut last_entry_pos = None;
    for entry in &file.entries {
        let entry_pos = f.pos()?;
        if let Some(last_entry_pos) = last_entry_pos {
            f.seek_to(last_entry_pos + format.offset_to_next_offset())?;
            f.write_u32((entry_pos - last_entry_pos) as _)?;
            f.seek_to(entry_pos)?;
        }

        write_entry(f, &format, entry)?;

        last_entry_pos = Some(entry_pos);
    }
    Ok(())
}

fn write_entry(f: &mut dyn BinWrite, file_format: &FileFormat, entry: &Entry) -> WriteResult {
    let instr_format = file_format.instr_format();

    let entry_pos = f.pos()?;

    let EntrySpecs {
        width, height, format, colorkey, offset_x, offset_y, memory_priority,
        has_data, low_res_scale,
    } = entry.specs;

    file_format.write_header(f, &EntryHeaderData {
        width, height, format, colorkey, offset_x, offset_y, memory_priority,
        has_data: has_data as u32,
        low_res_scale: low_res_scale as u32,
        version: file_format.version as u32,
        num_sprites: entry.sprites.len() as u32,
        num_scripts: entry.scripts.len() as u32,
        // we will overwrite these later
        name_offset: 0, secondary_name_offset: None,
        next_offset: 0, thtx_offset: None,
    })?;

    let sprite_offsets_pos = f.pos()?;
    f.write_u32s(&vec![0; entry.sprites.len()])?;
    let script_headers_pos = f.pos()?;
    f.write_u32s(&vec![0; 2 * entry.scripts.len()])?;

    let path_offset = f.pos()? - entry_pos;
    f.write_cstring(&entry.path, 16)?;

    let mut path_2_offset = 0;
    if let Some(path_2) = &entry.path_2 {
        path_2_offset = f.pos()? - entry_pos;
        f.write_cstring(path_2, 16)?;
    };

    let sprite_offsets = entry.sprites.iter().map(|(_, sprite)| {
        let sprite_offset = f.pos()? - entry_pos;
        write_sprite(f, sprite)?;
        Ok(sprite_offset)
    }).collect::<WriteResult<Vec<_>>>()?;

    let script_ids_and_offsets = entry.scripts.iter().map(|(name, script)| {
        let script_offset = f.pos()? - entry_pos;
        llir::write_instrs(f, instr_format, &script.instrs)
            .with_context(|| format!("while writing script '{}'", name))?;

        Ok((script.id, script_offset))
    }).collect::<WriteResult<Vec<_>>>()?;

    let mut texture_offset = 0;
    if let Some(texture) = &entry.texture {
        texture_offset = f.pos()? - entry_pos;
        write_texture(f, texture)?;
    };

    let end_pos = f.pos()?;

    f.seek_to(entry_pos + file_format.offset_to_thtx_offset())?;
    f.write_u32(texture_offset as _)?;

    f.seek_to(entry_pos + file_format.offset_to_path_offset())?;
    f.write_u32(path_offset as _)?;

    if let Some(offset_to_path_2_offset) = file_format.offset_to_path_2_offset() {
        f.seek_to(entry_pos + offset_to_path_2_offset)?;
        f.write_u32(path_2_offset as _)?;
    }

    f.seek_to(sprite_offsets_pos)?;
    for sprite_offset in sprite_offsets {
        f.write_u32(sprite_offset as _)?;
    }

    f.seek_to(script_headers_pos)?;
    for (script_id, script_offset) in script_ids_and_offsets {
        f.write_u32(script_id as _)?;
        f.write_u32(script_offset as _)?;
    }

    f.seek_to(end_pos)?;
    Ok(())
}

fn read_sprite(f: &mut dyn BinRead) -> ReadResult<Sprite> {
    Ok(Sprite {
        id: f.read_u32()?,
        offset: f.read_f32s_2()?,
        size: f.read_f32s_2()?,
    })
}

fn write_sprite(f: &mut dyn BinWrite, sprite: &Sprite) -> WriteResult {
    f.write_u32(sprite.id as _)?;
    f.write_f32s(&sprite.offset)?;
    f.write_f32s(&sprite.size)
}

fn read_texture(f: &mut dyn BinRead) -> ReadResult<Texture> {
    f.expect_magic("THTX")?;

    let zero = f.read_u16()?;
    let format = f.read_u16()? as u32;
    let width = f.read_u16()? as u32;
    let height = f.read_u16()? as u32;
    let size = f.read_u32()?;
    if zero != 0 {
        fast_warning!("nonzero thtx_zero lost: {}", zero);
    }
    let thtx = ThtxHeader { format, width, height };

    let mut data = vec![0; size as usize];
    f.read_exact(&mut data)?;

    Ok(Texture { thtx, data })
}

fn write_texture(f: &mut dyn BinWrite, texture: &Texture) -> WriteResult {
    f.write_all(b"THTX")?;

    f.write_u16(0)?;
    f.write_u16(texture.thtx.format as _)?;
    f.write_u16(texture.thtx.width as _)?;
    f.write_u16(texture.thtx.height as _)?;
    f.write_u32(texture.data.len() as _)?;
    f.write_all(&texture.data)?;
    Ok(())
}

// =============================================================================

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Version { V0 = 0, V2 = 2, V3 = 3, V4 = 4, V7 = 7, V8 = 8 }
impl Version {
    fn from_game(game: Game) -> Self {
        use Game::*;
        match game {
            Th06 => Version::V0,
            Th07 => Version::V2,
            Th08 | Th09 => Version::V3,
            Th095 | Th10 | Alcostg => Version::V4,
            Th11 | Th12 | Th125 | Th128 => Version::V7,
            Th13 | Th14 | Th143 | Th15 | Th16 | Th165 | Th17 => Version::V8,
        }
    }

    fn is_old_header(self) -> bool { self < Version::V7 }
    fn has_vars(self) -> bool { self >= Version::V2 }
}

fn game_format(game: Game) -> FileFormat {
    let version = Version::from_game(game);
    let instr_format: Box<dyn InstrFormat> = match version.has_vars() {
        true => Box::new(InstrFormat07 { version }),
        false => Box::new(InstrFormat06),
    };
    FileFormat { version, instr_format }
}

/// Type responsible for dealing with version differences in the format.
struct FileFormat { version: Version, instr_format: Box<dyn InstrFormat> }
struct InstrFormat06;
struct InstrFormat07 { version: Version }

impl InstrFormat06 { const HEADER_SIZE: usize = 4; }
impl InstrFormat07 { const HEADER_SIZE: usize = 8; }

impl FileFormat {
    fn read_header(&self, f: &mut dyn BinRead) -> ReadResult<EntryHeaderData> {
        macro_rules! warn_if_nonzero {
            ($name:literal, $expr:expr) => {
                match $expr {
                    0 => {},
                    x => fast_warning!("nonzero {} will be lost (value: {})", $name, x),
                }
            };
        }

        if self.version.is_old_header() {
            // old format
            let num_sprites = f.read_u32()? as _;
            let num_scripts = f.read_u32()? as _;
            warn_if_nonzero!("rt_textureslot", f.read_u32()?);
            let width = f.read_u32()? as _;
            let height = f.read_u32()? as _;
            let format = f.read_u32()? as _;
            let colorkey = f.read_u32()? as _;
            let name_offset = f.read_u32()? as _;
            warn_if_nonzero!("unused_1", f.read_u32()?);
            let secondary_name_offset = NonZeroUsize::new(f.read_u32()? as _);
            let version = f.read_u32()? as _;
            let memory_priority = f.read_u32()? as _;
            let thtx_offset = NonZeroUsize::new(f.read_u32()? as _) as _;
            let has_data = f.read_u16()? as _;
            warn_if_nonzero!("unused_2", f.read_u16()?);
            let next_offset = f.read_u32()? as _;
            warn_if_nonzero!("unused_3", f.read_u32()?);

            Ok(EntryHeaderData {
                version, num_sprites, num_scripts,
                width, height, format, name_offset,
                next_offset, secondary_name_offset, colorkey,
                memory_priority, thtx_offset, has_data,
                offset_x: 0, offset_y: 0, low_res_scale: 0,
            })

        } else {
            // new format
            let version = f.read_u32()? as _;
            let num_sprites = f.read_u16()? as _;
            let num_scripts = f.read_u16()? as _;
            warn_if_nonzero!("rt_textureslot", f.read_u16()?);
            let width = f.read_u16()? as _;
            let height = f.read_u16()? as _;
            let format = f.read_u16()? as _;
            let name_offset = f.read_u32()? as _;
            let offset_x = f.read_u16()? as _;
            let offset_y = f.read_u16()? as _;
            let memory_priority = f.read_u32()? as _;
            let thtx_offset = NonZeroUsize::new(f.read_u32()? as _);
            let has_data = f.read_u16()? as _;
            let low_res_scale = f.read_u16()? as _;
            let next_offset = f.read_u32()? as _;

            for _ in 0..6 {  // header gets padded to 16 dwords
            warn_if_nonzero!("header padding", f.read_u32()?);
            }
            Ok(EntryHeaderData {
                version, num_sprites, num_scripts,
                width, height, format, name_offset,
                offset_x, offset_y, low_res_scale, next_offset,
                memory_priority, thtx_offset, has_data,
                secondary_name_offset: None,
                colorkey: 0,
            })
        }
    }

    fn write_header(&self, f: &mut dyn BinWrite, header: &EntryHeaderData) -> WriteResult {
        if self.version.is_old_header() {
            // old format
            f.write_u32(header.num_sprites as _)?;
            f.write_u32(header.num_scripts as _)?;
            f.write_u32(0)?;
            f.write_u32(header.width as _)?;
            f.write_u32(header.height as _)?;
            f.write_u32(header.format as _)?;
            f.write_u32(header.colorkey as _)?;
            f.write_u32(header.name_offset as _)?;
            f.write_u32(0)?;
            f.write_u32(header.secondary_name_offset.map(NonZeroUsize::get).unwrap_or(0) as _)?;
            f.write_u32(header.version)?;
            f.write_u32(header.memory_priority)?;
            f.write_u32(header.thtx_offset.map(NonZeroUsize::get).unwrap_or(0) as _)?;
            f.write_u16(header.has_data as _)?;
            f.write_u16(0)?;
            f.write_u32(header.next_offset)?;
            f.write_u32(0)?;

        } else {
            // new format
            f.write_u32(header.version as _)?;
            f.write_u16(header.num_sprites as _)?;
            f.write_u16(header.num_scripts as _)?;
            f.write_u16(0)?;
            f.write_u16(header.width as _)?;
            f.write_u16(header.height as _)?;
            f.write_u16(header.format as _)?;
            f.write_u32(header.name_offset as _)?;
            f.write_u16(header.offset_x as _)?;
            f.write_u16(header.offset_y as _)?;
            f.write_u32(header.memory_priority as _)?;
            f.write_u32(header.thtx_offset.map(NonZeroUsize::get).unwrap_or(0) as _)?;
            f.write_u16(header.has_data as _)?;
            f.write_u16(header.low_res_scale as _)?;
            f.write_u32(header.next_offset as _)?;
            f.write_u32s(&[0; 6])?;
        }
        Ok(())
    }

    /// Offset into entry of the `next_offset` field.
    fn offset_to_next_offset(&self) -> u64 {
        if self.version.is_old_header() { 0x38 } else { 0x24 }
    }

    /// Offset into entry of the `name_offset` field.
    fn offset_to_path_offset(&self) -> u64 {
        if self.version.is_old_header() { 0x1c } else { 0x10 }
    }

    /// Offset into entry of the `name_offset` field.
    fn offset_to_path_2_offset(&self) -> Option<u64> {
        if self.version.is_old_header() { Some(0x24) } else { None }
    }

    /// Offset into entry of the `thtx_offset` field.
    fn offset_to_thtx_offset(&self) -> u64 {
        if self.version.is_old_header() { 0x30 } else { 0x1c }
    }

    fn instr_format(&self) -> &dyn InstrFormat { &*self.instr_format }
}

impl InstrFormat for InstrFormat06 {
    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, u16)> {
        vec![
            (IntrinsicInstrKind::Jmp, 5),
            (IntrinsicInstrKind::InterruptLabel, 22),
        ]
    }

    fn read_instr(&self, f: &mut dyn BinRead) -> ReadResult<Option<Instr>> {
        let time = f.read_i16()? as i32;
        let opcode = f.read_i8()?;
        let argsize = f.read_u8()? as usize;
        if (time, opcode, argsize) == (0, 0, 0) {
            return Ok(None);
        }

        let args = llir::read_dword_args_upto_size(f, argsize, 0)?;
        Ok(Some(Instr { time, opcode: opcode as u16, args }))
    }

    fn write_instr(&self, f: &mut dyn BinWrite, instr: &Instr) -> WriteResult {
        f.write_i16(instr.time as _)?;
        f.write_u8(instr.opcode as _)?;
        f.write_u8((self.instr_size(instr) - Self::HEADER_SIZE) as _)?;
        for x in &instr.args {
            f.write_u32(x.expect_raw().bits)?;
        }
        Ok(())
    }

    fn jump_has_time_arg(&self) -> bool { false }

    fn is_th06_anm_terminating_instr(&self, opcode: u16) -> bool {
        // This is the check that TH06 ANM uses to know when to stop searching for interrupt labels.
        // Basically, the first `delete` or `static` marks the end of the script.
        opcode == 0 || opcode == 15
    }

    fn write_terminal_instr(&self, f: &mut dyn BinWrite) -> WriteResult {
        f.write_u32(0)
    }

    fn instr_size(&self, instr: &Instr) -> usize { Self::HEADER_SIZE + 4 * instr.args.len() }
}

impl InstrFormat for InstrFormat07 {
    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, u16)> {
        use IntrinsicInstrKind as I;
        use llir::TransOpKind as Tr;

        match self.version {
            Version::V0 => unreachable!(),
            Version::V2 | Version::V3 => {
                let mut out = vec![
                    (I::Jmp, 4),
                    (I::CountJmp, 5),
                    (I::InterruptLabel, 21),
                    (I::TransOp(Tr::Sin), 61),
                    (I::TransOp(Tr::Cos), 62),
                    (I::TransOp(Tr::Tan), 63),
                    (I::TransOp(Tr::Acos), 64),
                    (I::TransOp(Tr::Atan), 65),
                ];
                llir::register_assign_ops(&mut out, 37);
                llir::register_binary_ops(&mut out, 49);
                llir::register_cond_jumps(&mut out, 67);
                out
            },
            Version::V4 | Version::V7 => {
                let mut out = vec![
                    (I::Jmp, 4),
                    (I::CountJmp, 5),
                    (I::InterruptLabel, 64),
                    (I::TransOp(Tr::Sin), 42),
                    (I::TransOp(Tr::Cos), 43),
                    (I::TransOp(Tr::Tan), 44),
                    (I::TransOp(Tr::Acos), 45),
                    (I::TransOp(Tr::Atan), 46),
                ];
                llir::register_assign_ops(&mut out, 6);
                llir::register_binary_ops(&mut out, 18);
                llir::register_cond_jumps(&mut out, 28);
                out
            },
            Version::V8 => {
                let mut out = vec![
                    (I::Jmp, 200),
                    (I::CountJmp, 201),
                    (I::InterruptLabel, 5),
                    (I::TransOp(Tr::Sin), 124),
                    (I::TransOp(Tr::Cos), 125),
                    (I::TransOp(Tr::Tan), 126),
                    (I::TransOp(Tr::Acos), 127),
                    (I::TransOp(Tr::Atan), 128),
                ];
                llir::register_assign_ops(&mut out, 100);
                llir::register_binary_ops(&mut out, 112);
                llir::register_cond_jumps(&mut out, 202);
                out
            },
        }
    }

    fn general_use_regs(&self) -> EnumMap<ScalarType, Vec<i32>> {
        match self.version {
            Version::V0 => unreachable!(),
            Version::V2 | Version::V3 | Version::V4 | Version::V7 | Version::V8 => enum_map::enum_map!{
                ScalarType::Int => vec![10000, 10001, 10002, 10003, 10008, 10009],
                ScalarType::Float => vec![10004, 10005, 10006, 10007],
            },
        }
    }

    fn read_instr(&self, f: &mut dyn BinRead) -> ReadResult<Option<Instr>> {
        let opcode = f.read_i16()?;
        let size = f.read_u16()? as usize;
        if opcode == -1 {
            return Ok(None);
        }

        let time = f.read_i16()? as i32;
        let param_mask = f.read_u16()?;
        let args = llir::read_dword_args_upto_size(f, size - Self::HEADER_SIZE, param_mask)?;
        // eprintln!("opcode: {:04x}  size: {:04x}  time: {:04x}  param_mask: {:04x}  args: {:?}", opcode, size, time, param_mask, args);
        Ok(Some(Instr { time, opcode: opcode as u16, args }))
    }

    fn write_instr(&self, f: &mut dyn BinWrite, instr: &Instr) -> WriteResult {
        f.write_u16(instr.opcode)?;
        f.write_u16(self.instr_size(instr) as u16)?;
        f.write_i16(instr.time as i16)?;
        f.write_u16(instr.compute_param_mask()?)?;
        for x in &instr.args {
            f.write_u32(x.expect_raw().bits)?;
        }
        Ok(())
    }

    fn write_terminal_instr(&self, f: &mut dyn BinWrite) -> WriteResult {
        f.write_i16(-1)?;
        f.write_u16(0)?;
        f.write_u16(0)?;
        f.write_u16(0)
    }

    fn instr_size(&self, instr: &Instr) -> usize { Self::HEADER_SIZE + 4 * instr.args.len() }
}
