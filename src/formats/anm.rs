use std::fmt;
use std::io;
use std::num::NonZeroU64;

use anyhow::{Context, bail};
use enum_map::EnumMap;
use indexmap::{IndexSet, IndexMap};

use crate::ast;
use crate::binary_io::{BinRead, BinWrite, Encoded, ReadResult, WriteResult};
use crate::error::{CompileError, GatherErrorIteratorExt, SimpleError};
use crate::game::Game;
use crate::ident::Ident;
use crate::llir::{self, RawInstr, InstrFormat, IntrinsicInstrKind};
use crate::meta::{self, FromMeta, FromMetaError, Meta, ToMeta};
use crate::pos::Sp;
use crate::value::ScalarValue;
use crate::type_system::{ScalarType, TypeSystem};
use crate::passes::DecompileKind;
use crate::resolve::RegId;

// =============================================================================

/// Game-independent representation of an ANM file.
#[derive(Debug, Clone)]
pub struct AnmFile {
    pub entries: Vec<Entry>,
}

impl AnmFile {
    pub fn decompile_to_ast(&self, game: Game, ty_ctx: &TypeSystem, decompile_kind: DecompileKind) -> Result<ast::Script, SimpleError> {
        decompile(&game_format(game), self, ty_ctx, decompile_kind)
    }

    pub fn compile_from_ast(game: Game, ast: &ast::Script, ty_ctx: &mut TypeSystem) -> Result<Self, CompileError> {
        compile(&game_format(game), ast, ty_ctx)
    }

    /// Uses `other` as a source for any missing metadata from the entries, as well as for embedded images.
    ///
    /// For each entry in `self`, if there exists an entry in `other` with a matching `path`, then that entry
    /// will be used to fill in things that are missing. (e.g. metadata in the header, as well as the embedded
    /// image if `has_data: true`).
    /// **Scripts and sprites from `other` are entirely ignored.**
    ///
    /// If multiple entries have the same path, then the first one with that path in `other` applies to the first
    /// one with that path in `self`, and so on in matching order.  This is to facilitate recompilation of files
    /// like `ascii.anm`, which have multiple `"@R"` entries.
    pub fn apply_image_source(&mut self, other: Self) -> Result<(), CompileError> {
        apply_image_source(self, other)
    }

    pub fn write_to_stream(&self, mut w: impl io::Write + io::Seek, game: Game) -> Result<(), CompileError> {
        write_anm(&mut w, &game_format(game), self)
    }

    pub fn read_from_stream(mut r: impl io::Read + io::Seek, game: Game, with_images: bool) -> ReadResult<Self> {
        read_anm(&game_format(game), &mut r, with_images)
    }

    pub fn write_thecl_defs(&self, w: impl io::Write) -> WriteResult {
        write_thecl_defs(w, self)
    }
}

#[derive(Debug, Clone)]
pub struct Entry {
    pub specs: EntrySpecs,
    pub texture: Option<Texture>,
    pub path: Sp<String>,
    pub path_2: Option<Sp<String>>,
    pub scripts: IndexMap<Sp<Ident>, Script>,
    pub sprites: IndexMap<Sp<Ident>, Sprite>,
}

#[derive(Debug, Clone)]
pub struct Script {
    pub id: i32,
    pub instrs: Vec<RawInstr>,
}

#[derive(Debug, Clone)]
pub struct EntrySpecs {
    pub width: Option<u32>,
    pub height: Option<u32>,
    pub format: Option<u32>,
    pub colorkey: Option<u32>, // Only in old format
    pub offset_x: Option<u32>,
    pub offset_y: Option<u32>,
    pub memory_priority: Option<u32>,
    pub has_data: Option<bool>,
    pub low_res_scale: Option<bool>,
}

impl Entry {
    fn make_meta(&self) -> meta::Fields {
        let EntrySpecs {
            width, height, format, colorkey, offset_x, offset_y,
            memory_priority, has_data, low_res_scale,
        } = &self.specs;

        Meta::make_object()
            .field("path", &self.path.value)
            .opt_field("path_2", self.path_2.as_ref().map(|x| &x.value))
            .opt_field("has_data", has_data.as_ref())
            .opt_field("width", width.as_ref())
            .opt_field("height", height.as_ref())
            .opt_field("offset_x", offset_x.as_ref())
            .opt_field("offset_y", offset_y.as_ref())
            .opt_field("format", format.as_ref())
            .opt_field("colorkey", colorkey.as_ref())
            .opt_field("memory_priority", memory_priority.as_ref())
            .opt_field("low_res_scale", low_res_scale.as_ref())
            .with_mut(|b| if let Some(texture) = &self.texture {
                b.field("thtx_format", &texture.thtx.format);
                b.field("thtx_width", &texture.thtx.width);
                b.field("thtx_height", &texture.thtx.height);
            })
            .field("sprites", &self.sprites)
            .build_fields()
    }

    fn from_fields(fields: &Sp<meta::Fields>) -> Result<Self, FromMetaError<'_>> {
        meta::ParseObject::scope(fields, |m| {
            let format = m.get_field("format")?;
            let width = m.get_field("width")?;
            let height = m.get_field("height")?;
            let colorkey = m.get_field("colorkey")?;
            let offset_x = m.get_field("offset_x")?;
            let offset_y = m.get_field("offset_y")?;
            let memory_priority = m.get_field("memory_priority")?;
            let low_res_scale = m.get_field("low_res_scale")?;
            let has_data = m.get_field("has_data")?;
            let path = m.expect_field("path")?;
            let path_2 = m.get_field("path_2")?;
            let texture = None;
            m.allow_field("thtx_format")?;
            m.allow_field("thtx_width")?;
            m.allow_field("thtx_height")?;
            let sprites = m.get_field("sprites")?.unwrap_or_default();

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
    pub data: Option<Vec<u8>>,
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
            .field("data", &self.data.as_ref().map(|_| (..)))
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

fn decompile(
    format: &FileFormat,
    anm_file: &AnmFile,
    ty_ctx: &TypeSystem,
    decompile_kind: DecompileKind,
) -> Result<ast::Script, SimpleError> {
    let instr_format = format.instr_format();

    let mut items = vec![];
    let mut raiser = llir::Raiser::new();
    for entry in &anm_file.entries {
        items.push(sp!(ast::Item::Meta {
            keyword: sp!(ast::MetaKeyword::Entry),
            ident: None,
            fields: sp!(entry.make_meta()),
        }));

        for (name, &Script { id, ref instrs }) in &entry.scripts {
            let code = raiser.raise_instrs_to_sub_ast(instr_format, instrs, ty_ctx)?;

            items.push(sp!(ast::Item::AnmScript {
                number: Some(sp!(id)),
                ident: name.clone(),
                code: ast::Block(code),
                keyword: sp!(()),
            }));
        }
    }
    let mut out = ast::Script {
        items,
        mapfiles: ty_ctx.mapfiles_to_ast(),
        // NOTE: here, we *could* choose to populate this, causing a `#pragma image_source` line
        //       to automatically be added to the file.  However, the big reason we do this for
        //       mapfiles is to encourage people to check their mapfiles into VCS, and I do not
        //       want to encourage people checking in vanilla ANM files.
        image_sources: vec![],
    };
    crate::passes::postprocess_decompiled(&mut out, ty_ctx, decompile_kind)?;
    Ok(out)
}

fn apply_image_source(dest_file: &mut AnmFile, src_file: AnmFile) -> Result<(), CompileError> {
    let mut src_entries_by_path: IndexMap<_, Vec<_>> = IndexMap::new();
    for entry in src_file.entries {
        src_entries_by_path.entry(entry.path.clone()).or_default().push(entry);
    };
    for vec in src_entries_by_path.values_mut() {
        vec.reverse();  // so we can pop them in forwards order
    }

    for dest_entry in &mut dest_file.entries {
        if let Some(src_entry) = src_entries_by_path.get_mut(&dest_entry.path).and_then(|vec| vec.pop()) {
            update_entry_from_image_source(dest_entry, src_entry)?;
        }
    }
    Ok(())
}

fn update_entry_from_image_source(dest_file: &mut Entry, src_file: Entry) -> Result<(), CompileError> {
    let dest_specs = &mut dest_file.specs;

    // though it's tedious, we fully unpack this struct to that the compiler doesn't
    // let us forget to update this function when we add a new field.
    let EntrySpecs {
        width: src_width, height: src_height, format: src_format,
        colorkey: src_colorkey, offset_x: src_offset_x, offset_y: src_offset_y,
        memory_priority: src_memory_priority, has_data: src_has_data,
        low_res_scale: src_low_res_scale,
    } = src_file.specs;

    fn or_inplace<T>(dest: &mut Option<T>, src: Option<T>) {
        *dest = dest.take().or(src);
    }

    or_inplace(&mut dest_specs.width, src_width);
    or_inplace(&mut dest_specs.height, src_height);
    or_inplace(&mut dest_specs.format, src_format);
    or_inplace(&mut dest_specs.colorkey, src_colorkey);
    or_inplace(&mut dest_specs.offset_x, src_offset_x);
    or_inplace(&mut dest_specs.offset_y, src_offset_y);
    or_inplace(&mut dest_specs.memory_priority, src_memory_priority);
    or_inplace(&mut dest_specs.has_data, src_has_data);
    or_inplace(&mut dest_specs.low_res_scale, src_low_res_scale);

    if dest_specs.has_data != Some(false) {
        or_inplace(&mut dest_file.texture, src_file.texture);
    }

    Ok(())
}


fn compile(
    format: &FileFormat,
    ast: &ast::Script,
    ty_ctx: &mut TypeSystem,
) -> Result<AnmFile, CompileError> {
    let instr_format = format.instr_format();

    // group scripts by entry
    let mut groups = vec![];
    let mut cur_entry = None;
    let mut cur_group = vec![];
    let mut script_names = vec![];
    for item in &ast.items {
        match &item.value {
            ast::Item::Meta { keyword: sp_pat!(ast::MetaKeyword::Entry), fields, .. } => {
                if let Some(prev_entry) = cur_entry.take() {
                    groups.push((prev_entry, cur_group));
                }
                cur_entry = Some(Entry::from_fields(fields)?);
                cur_group = vec![];
            },
            &ast::Item::AnmScript { number, ref ident, ref code, .. } => {
                if cur_entry.is_none() { return Err(error!(
                    message("orphaned ANM script with no entry"),
                    primary(item, "orphaned script"),
                    note("at least one `entry` must come before scripts in an ANM file"),
                ))}
                cur_group.push((number, ident, code));
                script_names.push(ident);
            },
            _ => return Err(error!(
                message("feature not supported by format"),
                primary(item, "not supported by ANM files"),
            )),
        }
    }

    match cur_entry {
        None => return Err(error!("empty ANM script")),
        Some(cur_entry) => groups.push((cur_entry, cur_group)),  // last group
    }

    let sprite_ids = gather_sprite_ids(groups.iter().map(|(entry, _)| entry))?;

    // Create automatic 'const' items for all sprites and scripts
    for (index, script_name) in script_names.into_iter().enumerate() {
        let script_name = sp!(script_name.span => script_name.value.clone().into());
        ty_ctx.add_global_const_var(script_name, ScalarValue::Int(index as i32));
    }
    for (sprite_name, id) in sprite_ids {
        let sprite_name = sp!(sprite_name.span => sprite_name.value.clone().into());
        ty_ctx.add_global_const_var(sprite_name, ScalarValue::Int(id as i32));
    }

    let mut next_auto_id = 0;
    let entries = groups.into_iter().map(|(mut entry, ast_scripts)| {
        for (given_number, name, code) in ast_scripts {
            let id = given_number.map(|sp| sp.value).unwrap_or(next_auto_id);
            next_auto_id = id + 1;

            // FIXME: We should be running these passes on the whole file, not on each script.
            //        (running it on each script will prevent us from having `const` items & inline functions).
            //        However, currently it is done to individual scripts because const simplification
            //        requires script & sprite names, which require handling the Meta.
            //        (we'll need to rework our first pass over the script to just gather global names)
            let code = {
                let mut code = code.clone();

                crate::passes::resolve_names::run(&mut code, ty_ctx)?;
                crate::passes::type_check::run(&code, ty_ctx)?;
                crate::passes::const_simplify::run(&mut code, ty_ctx)?;
                crate::passes::desugar_blocks::run(&mut code, ty_ctx)?;
                code
            };

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

fn gather_sprite_ids<'a>(entries: impl IntoIterator<Item=&'a Entry>) -> Result<Vec<(Sp<Ident>, u32)>, CompileError> {
    // It is okay for two sprites to have the same name (this occurs in decompiled output),
    // but they must also have the same ID, or else the name becomes ambiguous as a const.
    let mut sprite_ids = IndexMap::new();
    for entry in entries {
        for (name, sprite) in &entry.sprites {
            match sprite_ids.entry(name.clone()) {
                indexmap::map::Entry::Vacant(e) => {
                    e.insert((name.span, sprite.id));
                },
                indexmap::map::Entry::Occupied(e) => {
                    let &(prev_span, prev_id) = e.get();
                    if prev_id != sprite.id {
                        return Err(error!(
                            message("name clash between sprites"),
                            primary(prev_span, "definition with ID {}", prev_id),
                            primary(name, "redefinition with ID {}", sprite.id),
                        ));
                    }
                },
            }
        }
    }
    Ok(sprite_ids.into_iter().map(|(ident, (_, id))| (ident, id)).collect())
}

fn write_thecl_defs(
    mut w: impl io::Write,
    anm: &AnmFile,
) -> Result<(), SimpleError> {
    let mut script_index = 0;
    for entry in &anm.entries {
        for name in entry.scripts.keys() {
            writeln!(&mut w, "global {} = {};", name, script_index)?;
            script_index += 1;
        }
    }
    Ok(())
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
    name_offset: u64,
    secondary_name_offset: Option<NonZeroU64>, // EoSD only?
    colorkey: u32, // Only in old format
    offset_x: u32,
    offset_y: u32,
    memory_priority: u32,
    thtx_offset: Option<NonZeroU64>,
    has_data: u32,
    low_res_scale: u32,
    next_offset: u64,
}

fn read_anm(format: &FileFormat, reader: &mut dyn BinRead, with_images: bool) -> ReadResult<AnmFile> {
    let instr_format = format.instr_format();

    let mut entries = vec![];
    let mut next_script_index = 0;
    loop {
        let entry_pos = reader.pos()?;

        // 64 byte header regardless of version
        let header_data = format.read_header(reader)?;
        if header_data.has_data != header_data.has_data % 2 {
            fast_warning!("non-boolean value found for 'has_data': {}", header_data.has_data);
        }
        if header_data.low_res_scale != header_data.low_res_scale % 2 {
            fast_warning!("non-boolean value found for 'low_res_scale': {}", header_data.low_res_scale);
        }

        let sprite_offsets = (0..header_data.num_sprites).map(|_| reader.read_u32()).collect::<ReadResult<Vec<_>>>()?;
        let script_ids_and_offsets = (0..header_data.num_scripts).map(|_| {
            Ok((reader.read_i32()?, reader.read_u32()? as u64))
        }).collect::<ReadResult<Vec<_>>>()?;
        // eprintln!("{:?}", header_data);
        // eprintln!("{:?}", sprite_offsets);
        // eprintln!("{:?}", script_ids_and_offsets);

        reader.seek_to(entry_pos + header_data.name_offset)?;
        let path = reader.read_cstring_blockwise(16)?.decode()?;
        let path_2 = match header_data.secondary_name_offset {
            None => None,
            Some(n) => {
                reader.seek_to(entry_pos + n.get())?;
                Some(reader.read_cstring_blockwise(16)?.decode()?)
            },
        };

        let mut sprites_seen_in_entry = IndexSet::new();
        let sprites = sprite_offsets.iter().map(|&offset| {
            reader.seek_to(entry_pos + offset as u64)?;
            let sprite = read_sprite(reader)?;

            // Note: Duplicate IDs do happen between different entries, so we don't check that.
            if !sprites_seen_in_entry.insert(sprite.id) {
                fast_warning!("sprite ID {} appeared twice in same entry; only one will be kept", sprite.id);
            }
            let key = sp!(auto_sprite_name(sprite.id as u32));

            Ok((key, sprite))
        }).collect::<ReadResult<IndexMap<_, _>>>()?;

        // We need to know all the possible offsets at which a script may end.
        // Why?  Blame StB.
        let mut all_offsets = vec![header_data.name_offset];
        all_offsets.extend(header_data.thtx_offset.map(NonZeroU64::get));
        all_offsets.extend(header_data.secondary_name_offset.map(NonZeroU64::get));
        all_offsets.extend(sprite_offsets.iter().map(|&offset| offset as u64));
        all_offsets.extend(script_ids_and_offsets.iter().map(|&(_, offset)| offset as u64));

        let scripts = script_ids_and_offsets.iter().map(|&(id, offset)| {
            let key = sp!(auto_script_name(next_script_index));
            next_script_index += 1;

            let end_offset = all_offsets.iter().copied().filter(|&x| x > offset).min();

            let instrs = {
                reader.seek_to(entry_pos + offset)?;
                llir::read_instrs(reader, instr_format, offset, end_offset)
                    .with_context(|| format!("while reading {}", key))?
            };
            Ok((key, Script { id, instrs }))
        }).collect::<ReadResult<IndexMap<_, _>>>()?;

        let expect_no_texture = header_data.has_data == 0 || path.starts_with("@");
        if expect_no_texture != header_data.thtx_offset.is_none() {
            bail!("inconsistency between thtx_offset and has_data/name");
        }

        let texture = match header_data.thtx_offset {
            None => None,
            Some(n) => {
                reader.seek_to(entry_pos + n.get())?;
                Some(read_texture(reader, with_images)?)
            },
        };
        let specs = EntrySpecs {
            width: Some(header_data.width), height: Some(header_data.height),
            format: Some(header_data.format), colorkey: Some(header_data.colorkey),
            offset_x: Some(header_data.offset_x), offset_y: Some(header_data.offset_y),
            memory_priority: Some(header_data.memory_priority),
            has_data: Some(header_data.has_data != 0),
            low_res_scale: Some(header_data.low_res_scale != 0),
        };

        entries.push(Entry {
            path: sp!(path),
            path_2: path_2.map(|x| sp!(x)),
            texture, specs, sprites, scripts
        });

        if header_data.next_offset == 0 {
            break;
        }
        reader.seek_to(entry_pos + header_data.next_offset)?;
    }
    Ok(AnmFile { entries })
}

pub fn auto_sprite_name(i: u32) -> Ident {
    format!("sprite{}", i).parse::<Ident>().unwrap()
}
pub fn auto_script_name(i: u32) -> Ident {
    format!("script{}", i).parse::<Ident>().unwrap()
}

fn write_anm(f: &mut dyn BinWrite, format: &FileFormat, file: &AnmFile) -> Result<(), CompileError> {
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

fn write_entry(f: &mut dyn BinWrite, file_format: &FileFormat, entry: &Entry) -> Result<(), CompileError> {
    let instr_format = file_format.instr_format();

    let entry_pos = f.pos()?;

    let EntrySpecs {
        width, height, format, colorkey, offset_x, offset_y, memory_priority,
        has_data, low_res_scale,
    } = entry.specs;

    fn missing(path: &str, problem: &str) -> CompileError {
        const SUGGESTION: &'static str = "(if this data is available in an existing anm file, try using `-i ANM_FILE`)";
        error!(message(
            "entry for '{}' {}\n       {}",
            path, problem, SUGGESTION,
        ))
    }

    macro_rules! expect {
        ($name:ident) => { match $name {
            Some(x) => x,
            None => {
                let problem = format!("is missing required field '{}'!", stringify!($name));
                return Err(missing(&entry.path, &problem));
            },
        }};
    }

    file_format.write_header(f, &EntryHeaderData {
        width: expect!(width),
        height: expect!(height),
        format: expect!(format),
        colorkey: expect!(colorkey),
        offset_x: expect!(offset_x),
        offset_y: expect!(offset_y),
        memory_priority: expect!(memory_priority),
        has_data: expect!(has_data) as u32,
        low_res_scale: expect!(low_res_scale) as u32,
        version: file_format.version as u32,
        num_sprites: entry.sprites.len() as u32,
        num_scripts: entry.scripts.len() as u32,
        // we will overwrite these later
        name_offset: 0, secondary_name_offset: None,
        next_offset: 0, thtx_offset: None,
    })?;
    let has_data = expect!(has_data);

    let sprite_offsets_pos = f.pos()?;
    f.write_u32s(&vec![0; entry.sprites.len()])?;
    let script_headers_pos = f.pos()?;
    f.write_u32s(&vec![0; 2 * entry.scripts.len()])?;

    let path_offset = f.pos()? - entry_pos;
    f.write_cstring(&Encoded::encode(&entry.path)?, 16)?;

    let mut path_2_offset = 0;
    if let Some(path_2) = &entry.path_2 {
        path_2_offset = f.pos()? - entry_pos;
        f.write_cstring(&Encoded::encode(path_2)?, 16)?;
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
    if has_data {
        match &entry.texture {
            None => {
                let problem = format!("has 'has_data: true', but there's no bitmap data available!");
                return Err(missing(&entry.path, &problem));
            },
            Some(texture) => {
                texture_offset = f.pos()? - entry_pos;
                write_texture(f, texture)?;
            }
        }
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

#[inline(never)]
fn read_texture(f: &mut dyn BinRead, with_images: bool) -> ReadResult<Texture> {
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

    if with_images {
        let mut data = vec![0; size as usize];
        f.read_exact(&mut data)?;
        Ok(Texture { thtx, data: Some(data) })
    } else {
        Ok(Texture { thtx, data: None })
    }
}

#[inline(never)]
fn write_texture(f: &mut dyn BinWrite, texture: &Texture) -> WriteResult {
    f.write_all(b"THTX")?;

    f.write_u16(0)?;
    f.write_u16(texture.thtx.format as _)?;
    f.write_u16(texture.thtx.width as _)?;
    f.write_u16(texture.thtx.height as _)?;

    let data = texture.data.as_ref().expect("(bug!) trying to write images but did not read them!");
    f.write_u32(data.len() as _)?;
    f.write_all(data)?;
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
        true => Box::new(InstrFormat07 { version, game }),
        false => Box::new(InstrFormat06),
    };
    FileFormat { version, instr_format }
}

pub fn game_core_mapfile(game: Game) -> String {
    match Version::from_game(game) {
        Version::V0 => include_str!("../../map/core/v0.anmm").to_string(),
        Version::V2 => include_str!("../../map/core/v2.anmm").to_string(),
        Version::V3 => include_str!("../../map/core/v3.anmm").to_string(),
        Version::V4 |
        Version::V7 => include_str!("../../map/core/v4.anmm").to_string(),
        Version::V8 => include_str!("../../map/core/v8.anmm").to_string(),
    }
}

/// Type responsible for dealing with version differences in the format.
struct FileFormat { version: Version, instr_format: Box<dyn InstrFormat> }
struct InstrFormat06;
struct InstrFormat07 { version: Version, game: Game }

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
            let secondary_name_offset = NonZeroU64::new(f.read_u32()? as _);
            let version = f.read_u32()? as _;
            let memory_priority = f.read_u32()? as _;
            let thtx_offset = NonZeroU64::new(f.read_u32()? as _) as _;
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
            let thtx_offset = NonZeroU64::new(f.read_u32()? as _);
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
            f.write_u32(header.secondary_name_offset.map(NonZeroU64::get).unwrap_or(0) as _)?;
            f.write_u32(header.version)?;
            f.write_u32(header.memory_priority)?;
            f.write_u32(header.thtx_offset.map(NonZeroU64::get).unwrap_or(0) as _)?;
            f.write_u16(header.has_data as _)?;
            f.write_u16(0)?;
            f.write_u32(header.next_offset as _)?;
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
            f.write_u32(header.thtx_offset.map(NonZeroU64::get).unwrap_or(0) as _)?;
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

    fn instr_header_size(&self) -> usize { 4 }

    fn read_instr(&self, f: &mut dyn BinRead) -> ReadResult<Option<RawInstr>> {
        let time = f.read_i16()? as i32;
        let opcode = f.read_i8()?;
        let argsize = f.read_u8()? as usize;
        if (time, opcode, argsize) == (0, 0, 0) {
            return Ok(None);
        }

        let args_blob = f.read_byte_vec(argsize)?;
        Ok(Some(RawInstr { time, opcode: opcode as u16, param_mask: 0, args_blob }))
    }

    fn write_instr(&self, f: &mut dyn BinWrite, instr: &RawInstr) -> WriteResult {
        f.write_i16(instr.time as _)?;
        f.write_u8(instr.opcode as _)?;
        f.write_u8(instr.args_blob.len() as _)?;
        f.write_all(&instr.args_blob)?;
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
}

impl InstrFormat for InstrFormat07 {
    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, u16)> {
        use IntrinsicInstrKind as I;

        match self.version {
            Version::V0 => unreachable!(),
            Version::V2 | Version::V3 => {
                let mut out = vec![
                    (I::Jmp, 4),
                    (I::CountJmp, 5),
                    (I::InterruptLabel, 21),
                    (I::Unop(token![sin], ScalarType::Float), 61),
                    (I::Unop(token![cos], ScalarType::Float), 62),
                    // (I::Unop(Un::Tan, ScalarType::Float), 63),
                    // (I::Unop(Un::Acos, ScalarType::Float), 64),
                    // (I::Unop(Un::Atan, ScalarType::Float), 65),
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
                    (I::Unop(token![sin], ScalarType::Float), 42),
                    (I::Unop(token![cos], ScalarType::Float), 43),
                    // (I::Unop(Un::Tan, ScalarType::Float), 44),
                    // (I::Unop(Un::Acos, ScalarType::Float), 45),
                    // (I::Unop(Un::Atan, ScalarType::Float), 46),
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
                    (I::Unop(token![sin], ScalarType::Float), 124),
                    (I::Unop(token![cos], ScalarType::Float), 125),
                    // (I::Unop(Un::Tan, ScalarType::Float), 126),
                    // (I::Unop(Un::Acos, ScalarType::Float), 127),
                    // (I::Unop(Un::Atan, ScalarType::Float), 128),
                ];
                llir::register_assign_ops(&mut out, 100);
                llir::register_binary_ops(&mut out, 112);
                llir::register_cond_jumps(&mut out, 202);
                out
            },
        }
    }

    fn general_use_regs(&self) -> EnumMap<ScalarType, Vec<RegId>> {
        use RegId as R;

        match self.version {
            Version::V0 => unreachable!(),
            Version::V2 | Version::V3 | Version::V4 | Version::V7 | Version::V8 => enum_map::enum_map!{
                ScalarType::Int => vec![R(10000), R(10001), R(10002), R(10003), R(10008), R(10009)],
                ScalarType::Float => vec![R(10004), R(10005), R(10006), R(10007)],
                ScalarType::String => vec![],
            },
        }
    }

    fn instr_header_size(&self) -> usize { 8 }

    fn read_instr(&self, f: &mut dyn BinRead) -> ReadResult<Option<RawInstr>> {
        let opcode = f.read_i16()?;
        let size = f.read_u16()? as usize;
        if opcode == -1 {
            return Ok(None);
        }

        let time = f.read_i16()? as i32;
        let param_mask = f.read_u16()?;
        let args_blob = f.read_byte_vec(size - self.instr_header_size())?;
        // eprintln!("opcode: {:04x}  size: {:04x}  time: {:04x}  param_mask: {:04x}  args: {:?}", opcode, size, time, param_mask, args);
        Ok(Some(RawInstr { time, opcode: opcode as u16, param_mask, args_blob }))
    }

    fn write_instr(&self, f: &mut dyn BinWrite, instr: &RawInstr) -> WriteResult {
        f.write_u16(instr.opcode)?;
        f.write_u16(self.instr_size(instr) as u16)?;
        f.write_i16(instr.time as i16)?;
        f.write_u16(instr.param_mask as u16)?;
        f.write_all(&instr.args_blob)?;
        Ok(())
    }

    fn write_terminal_instr(&self, f: &mut dyn BinWrite) -> WriteResult {
        f.write_i16(-1)?;
        f.write_u16(0)?;
        f.write_u16(0)?;
        f.write_u16(0)
    }

    fn instr_disables_scratch_regs(&self, opcode: u16) -> bool {
        // copyParentVars
        Game::Th14 <= self.game && opcode == 509
    }
}
