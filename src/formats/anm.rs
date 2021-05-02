use std::fmt;
use std::io;
use std::num::NonZeroU64;
use std::path::Path;

use enum_map::EnumMap;
use indexmap::{IndexSet, IndexMap};

use crate::ast;
use crate::io::{BinRead, BinWrite, BinReader, BinWriter, Encoded, ReadResult, WriteResult, DEFAULT_ENCODING, Fs};
use crate::diagnostic::{Emitter};
use crate::error::{GatherErrorIteratorExt, ErrorReported};
use crate::game::Game;
use crate::ident::{Ident, ResIdent};
use crate::llir::{self, ReadInstr, RawInstr, InstrFormat, IntrinsicInstrKind};
use crate::meta::{self, FromMeta, FromMetaError, Meta, ToMeta};
use crate::pos::{Sp, Span};
use crate::value::{ScalarType};
use crate::context::CompilerContext;
use crate::passes::DecompileKind;
use crate::resolve::RegId;

// =============================================================================

/// Game-independent representation of an ANM file.
#[derive(Debug, Clone)]
pub struct AnmFile {
    pub entries: Vec<Entry>,
    /// Filename of a read binary file, for display purposes only.
    binary_filename: Option<String>,
}

impl AnmFile {
    pub fn decompile_to_ast(&self, game: Game, ctx: &mut CompilerContext, decompile_kind: DecompileKind) -> Result<ast::ScriptFile, ErrorReported> {
        let emitter = ctx.emitter.while_decompiling(self.binary_filename.as_deref());
        decompile(self, &emitter, &game_format(game), ctx, decompile_kind)
    }

    pub fn compile_from_ast(game: Game, ast: &ast::ScriptFile, ctx: &mut CompilerContext) -> Result<Self, ErrorReported> {
        compile(&game_format(game), ast, ctx)
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
    pub fn apply_image_source(&mut self, other: Self) -> Result<(), ErrorReported> {
        apply_image_source(self, other)
    }

    pub fn write_to_stream(&self, w: &mut BinWriter, game: Game) -> WriteResult {
        let emitter = w.emitter();
        write_anm(w, &emitter, &game_format(game), self)
    }

    pub fn load_directory_as_image_source(fs: &Fs, path: &Path) -> ReadResult<Self> {
        read_directory_as_image_source(fs, path)
    }

    pub fn read_from_stream(r: &mut BinReader, game: Game, with_images: bool) -> ReadResult<Self> {
        let emitter = r.emitter();
        read_anm(r, &emitter, &game_format(game), with_images)
    }

    pub fn generate_thecl_defs(&self) -> Result<String, ErrorReported> {
        let mut bytes = vec![];
        write_thecl_defs(&mut bytes, self).expect("io::Error writing to Vec<u8>?!");
        Ok(String::from_utf8(bytes).expect("write_thecl_defs wrote non-utf8?!"))
    }
}

#[derive(Debug, Clone)]
pub struct Entry {
    pub specs: EntrySpecs,
    pub texture: Option<Texture>,
    // FIXME: Should hold PathBuf especially since we do equality comparisons on it
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

#[derive(Debug, Clone, Default)]
pub struct EntrySpecs {
    // NOTE: While most file type objects contain plain values (using things like 'field_default'
    // to handle defaults in meta conversions), this has to contain Options for the sake of the
    // "merging" of entries that occurs when --image-source is used.
    //
    // It makes this type really annoying to work with.  But that's life.
    pub buf_width: Option<Sp<u32>>,
    pub buf_height: Option<Sp<u32>>,
    pub buf_format: Option<Sp<u32>>,
    pub img_width: Option<Sp<u32>>,
    pub img_height: Option<Sp<u32>>,
    pub img_format: Option<Sp<u32>>,
    pub colorkey: Option<u32>, // Only in old format
    pub offset_x: Option<u32>,
    pub offset_y: Option<u32>,
    pub memory_priority: Option<u32>,
    pub has_data: Option<bool>,
    pub low_res_scale: Option<bool>,
}

impl EntrySpecs {
    // (this takes Game instead of FileFormat so it can be public for integration tests)
    pub fn fill_defaults(&self, game: Game) -> EntrySpecs {
        let file_format = game_format(game);

        let img_format = Some(self.img_format.unwrap_or(sp!(DEFAULT_FORMAT)));
        EntrySpecs {
            img_width: self.img_width,
            img_height: self.img_height,
            buf_width: self.buf_width.or(self.img_width.map(|x| x.sp_map(u32::next_power_of_two))),
            buf_height: self.buf_height.or(self.img_height.map(|x| x.sp_map(u32::next_power_of_two))),
            img_format,
            buf_format: self.buf_format.or(img_format),
            offset_x: Some(self.offset_x.unwrap_or(0)),
            offset_y: Some(self.offset_y.unwrap_or(0)),
            colorkey: Some(self.colorkey.unwrap_or(0)),
            memory_priority: Some(self.memory_priority.unwrap_or(file_format.default_memory_priority())),
            low_res_scale: Some(self.low_res_scale.unwrap_or(DEFAULT_LOW_RES_SCALE)),
            has_data: Some(self.has_data.unwrap_or(DEFAULT_HAS_DATA)),
        }
    }

    pub fn suppress_defaults(&self, game: Game) -> EntrySpecs {
        let file_format = game_format(game);

        EntrySpecs {
            img_width: self.img_width,
            img_height: self.img_height,
            // don't suppress buf_width and buf_height.  By always showing them in decompiled files, we increase the
            // likelihood of a user noticing that there's something important about powers of 2 in image dimensions,
            // possibly helping them to figure out why their non-power-of-2 PNG file looks bad when scrolled.
            buf_width: self.buf_width,
            buf_height: self.buf_height,

            img_format: self.img_format.filter(|&x| x != DEFAULT_FORMAT),
            buf_format: self.buf_format.filter(|&x| x != self.img_format.unwrap_or(sp!(DEFAULT_FORMAT))),
            offset_x: self.offset_x.filter(|&x| x != 0),
            offset_y: self.offset_y.filter(|&x| x != 0),
            colorkey: self.colorkey.filter(|&x| x != 0),
            memory_priority: self.memory_priority.filter(|&x| x != file_format.default_memory_priority()),
            low_res_scale: self.low_res_scale.filter(|&x| x != DEFAULT_LOW_RES_SCALE),
            has_data: self.has_data.filter(|&x| x != DEFAULT_HAS_DATA),
        }
    }
}

const DEFAULT_FORMAT: u32 = 1;
const DEFAULT_LOW_RES_SCALE: bool = false;
const DEFAULT_HAS_DATA: bool = true;

impl Entry {
    fn make_meta(&self, file_format: &FileFormat) -> meta::Fields {
        let mut specs = self.specs.clone();

        // derive properties of the runtime buffer based on the image
        if let (Some(buf_width), Some(img_width)) = (specs.buf_width, specs.img_width) {
            if buf_width == img_width.next_power_of_two() {
                specs.buf_width = None;
            }
        }

        if let (Some(buf_height), Some(img_height)) = (specs.buf_height, specs.img_height) {
            if buf_height == img_height.next_power_of_two() {
                specs.buf_height = None;
            }
        }

        if let (Some(buf_format), Some(img_format)) = (specs.buf_format, specs.img_format) {
            if buf_format == img_format {
                specs.buf_format = None;
            }
        }

        let EntrySpecs {
            buf_width, buf_height, buf_format, colorkey, offset_x, offset_y,
            img_width, img_height, img_format, memory_priority, has_data, low_res_scale,
        } = &specs.suppress_defaults(file_format.game);

        Meta::make_object()
            .field("path", &self.path.value)
            .field_opt("path_2", self.path_2.as_ref().map(|x| &x.value))
            .field_opt("has_data", has_data.as_ref())
            .field_opt("buf_width", buf_width.as_ref().map(|x| x.value))
            .field_opt("buf_height", buf_height.as_ref().map(|x| x.value))
            .field_opt("buf_format", buf_format.as_ref().map(|x| x.value))
            .field_opt("offset_x", offset_x.as_ref())
            .field_opt("offset_y", offset_y.as_ref())
            .field_opt("colorkey", colorkey.as_ref().map(|&value| ast::Expr::LitInt { value: value as i32, radix: ast::IntRadix::Hex }))
            .field_opt("memory_priority", memory_priority.as_ref())
            .field_opt("low_res_scale", low_res_scale.as_ref())
            .field_opt("img_width", img_width.as_ref().map(|x| x.value))
            .field_opt("img_height", img_height.as_ref().map(|x| x.value))
            .field_opt("img_format", img_format.as_ref().map(|x| x.value))
            .field("sprites", &self.sprites)
            .build_fields()
    }

    fn from_fields<'a>(fields: &'a Sp<meta::Fields>, emitter: &impl Emitter) -> Result<Self, FromMetaError<'a>> {
        meta::ParseObject::scope(fields, |m| {
            let deprecated_format = m.get_field_and_key("format")?;
            let deprecated_width = m.get_field_and_key("width")?;
            let deprecated_height = m.get_field_and_key("height")?;
            let mut buf_format = m.get_field::<Sp<u32>>("buf_format")?;
            let mut buf_width = m.get_field::<Sp<u32>>("buf_width")?;
            let mut buf_height = m.get_field::<Sp<u32>>("buf_height")?;
            for (deprecated_key_value, value) in vec![
                (deprecated_format, &mut buf_format),
                (deprecated_width, &mut buf_width),
                (deprecated_height, &mut buf_height),
            ] {
                static ONCE: std::sync::Once = std::sync::Once::new();

                if let Some((deprecated_key, deprecated_value)) = deprecated_key_value {
                    ONCE.call_once(|| emitter.emit(warning!(
                        message("\
                            deprecation warning: 'format', 'width', and 'height' have been \
                            renamed to 'buf_format', 'buf_width', and 'buf_height'.  The old \
                            names will be removed in a future version.\
                        "),
                        primary(deprecated_key, "deprecated key"),
                    )).ignore());

                    value.get_or_insert(deprecated_value);
                }
            }

            let deprecated_img_format = m.get_field_and_key("thtx_format")?;
            let deprecated_img_width = m.get_field_and_key("thtx_width")?;
            let deprecated_img_height = m.get_field_and_key("thtx_height")?;
            let mut img_format = m.get_field::<Sp<u32>>("img_format")?;
            let mut img_width = m.get_field::<Sp<u32>>("img_width")?;
            let mut img_height = m.get_field::<Sp<u32>>("img_height")?;
            for (deprecated_key_value, value) in vec![
                (deprecated_img_format, &mut img_format),
                (deprecated_img_width, &mut img_width),
                (deprecated_img_height, &mut img_height),
            ] {
                static ONCE: std::sync::Once = std::sync::Once::new();

                if let Some((deprecated_key, deprecated_value)) = deprecated_key_value {
                    ONCE.call_once(|| emitter.emit(warning!(
                        message("\
                            deprecation warning: 'thtx_format', 'thtx_width', and 'thtx_height' have \
                            been renamed to 'img_format', 'img_width', and 'img_height'.  The old \
                            names will be removed in a future version.\
                        "),
                        primary(deprecated_key, "deprecated key"),
                    )).ignore());

                    value.get_or_insert(deprecated_value);
                }
            }

            for (field, buf_value, img_value) in vec![
                ("buf_height", buf_height, img_height),
                ("buf_width", buf_width, img_height),
            ] {
                if let Some(buf_value) = buf_value {
                    if !buf_value.value.is_power_of_two() {
                        emitter.emit(warning!(
                            message("buf_{} = {} should be a power of two", field, buf_value),
                            primary(buf_value, "not a power of two")
                        )).ignore();
                    }
                    if let Some(img_value) = img_value {
                        if buf_value < img_value {
                            emitter.emit(warning!(
                                message("buf_{} = {} is not large enough for img_{} = {}", field, buf_value, field, img_value),
                                secondary(img_value, "image dimension defined here"),
                                primary(buf_value, "buffer too small for image"),
                            )).ignore();
                        }
                    }
                }
            }

            let colorkey = m.get_field("colorkey")?;
            let offset_x = m.get_field("offset_x")?;
            let offset_y = m.get_field("offset_y")?;
            let memory_priority = m.get_field("memory_priority")?;
            let low_res_scale = m.get_field("low_res_scale")?;
            let has_data = m.get_field("has_data")?;
            let path = m.expect_field("path")?;
            let path_2 = m.get_field("path_2")?;
            let texture = None;
            let sprites = m.get_field("sprites")?.unwrap_or_default();

            let specs = EntrySpecs {
                buf_width, buf_height, buf_format,
                img_width, img_height, img_format,
                colorkey, offset_x, offset_y,
                memory_priority, has_data, low_res_scale,
            };
            let scripts = Default::default();
            Ok(Entry { specs, texture, path, path_2, scripts, sprites })
        })
    }
}

#[derive(Clone)]
pub struct Texture {
    /// Raw pixel data, to be interpreted according to [`EntrySpecs::img_width`], [`EntrySpecs::img_height`],
    /// and [`EntrySpecs::img_format`].
    ///
    /// (they are stored separately because, when using `has_data: false`, we may copy those attributes from
    ///  an image source without copying the pixel data, so that they can be used to generate defaults for
    /// `buf_{width,height,format}`)
    pub data: Vec<u8>,
}

impl fmt::Debug for Texture {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Texture(_)")
    }
}

#[derive(Debug, Clone)]
pub struct ThtxHeader {
    pub format: u32,
    pub width: u32,
    pub height: u32,
}

#[derive(Debug, Clone)]
pub struct Sprite {
    pub id: Option<u32>,
    pub offset: [f32; 2],
    pub size: [f32; 2],
}

impl ToMeta for Sprite {
    fn to_meta(&self) -> Meta {
        let &Sprite { id, offset, size } = self;
        Meta::make_object()
            .field("x", &offset[0])
            .field("y", &offset[1])
            .field("w", &size[0])
            .field("h", &size[1])
            .field_opt("id", id.as_ref())
            .build()
    }
}

impl FromMeta<'_> for Sprite {
    fn from_meta(meta: &Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
        meta.parse_object(|m| Ok(Sprite {
            id: m.get_field("id")?,
            offset: [m.expect_field("x")?, m.expect_field("y")?],
            size: [m.expect_field("w")?, m.expect_field("h")?],
        }))
    }
}

// =============================================================================

fn decompile(
    anm_file: &AnmFile,
    emitter: &impl Emitter,
    format: &FileFormat,
    ctx: &mut CompilerContext,
    decompile_kind: DecompileKind,
) -> Result<ast::ScriptFile, ErrorReported> {
    let instr_format = format.instr_format();

    let mut items = vec![];
    let mut raiser = llir::Raiser::new(&ctx.emitter);
    for entry in &anm_file.entries {
        items.push(sp!(ast::Item::Meta {
            keyword: sp!(ast::MetaKeyword::Entry),
            fields: sp!(entry.make_meta(format)),
        }));

        entry.scripts.iter().map(|(name, &Script { id, ref instrs })| {
            let code = emitter.chain_with(|f| write!(f, "in script{}", id), |emitter| {
                raiser.raise_instrs_to_sub_ast(emitter, instr_format, instrs, &ctx.defs)
            })?;

            items.push(sp!(ast::Item::AnmScript {
                number: Some(sp!(id)),
                ident: name.clone(),
                code: ast::Block(code),
                keyword: sp!(()),
            }));
            Ok(())
        }).collect_with_recovery()?;
    }
    let mut out = ast::ScriptFile {
        items,
        mapfiles: ctx.mapfiles_to_ast(),
        // NOTE: here, we *could* choose to populate this, causing a `#pragma image_source` line
        //       to automatically be added to the file.  However, the big reason we do this for
        //       mapfiles is to encourage people to check their mapfiles into VCS, and I do not
        //       want to encourage people checking in vanilla ANM files.
        image_sources: vec![],
    };
    crate::passes::postprocess_decompiled(&mut out, ctx, decompile_kind)?;
    Ok(out)
}

fn apply_image_source(dest_file: &mut AnmFile, src_file: AnmFile) -> Result<(), ErrorReported> {
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

fn update_entry_from_image_source(dest_file: &mut Entry, src_file: Entry) -> Result<(), ErrorReported> {
    let dest_specs = &mut dest_file.specs;

    // though it's tedious, we fully unpack this struct to that the compiler doesn't
    // let us forget to update this function when we add a new field.
    let EntrySpecs {
        img_width: src_img_width, img_height: src_img_height, img_format: src_img_format,
        buf_width: src_buf_width, buf_height: src_buf_height, buf_format: src_buf_format,
        colorkey: src_colorkey, offset_x: src_offset_x, offset_y: src_offset_y,
        memory_priority: src_memory_priority, has_data: src_has_data,
        low_res_scale: src_low_res_scale,
    } = src_file.specs;

    fn or_inplace<T>(dest: &mut Option<T>, src: Option<T>) {
        *dest = dest.take().or(src);
    }

    or_inplace(&mut dest_specs.img_width, src_img_width);
    or_inplace(&mut dest_specs.img_height, src_img_height);
    or_inplace(&mut dest_specs.img_format, src_img_format);
    or_inplace(&mut dest_specs.buf_width, src_buf_width);
    or_inplace(&mut dest_specs.buf_height, src_buf_height);
    or_inplace(&mut dest_specs.buf_format, src_buf_format);
    or_inplace(&mut dest_specs.colorkey, src_colorkey);
    or_inplace(&mut dest_specs.offset_x, src_offset_x);
    or_inplace(&mut dest_specs.offset_y, src_offset_y);
    or_inplace(&mut dest_specs.memory_priority, src_memory_priority);
    or_inplace(&mut dest_specs.has_data, src_has_data);
    or_inplace(&mut dest_specs.low_res_scale, src_low_res_scale);

    if dest_specs.has_data.unwrap_or(DEFAULT_HAS_DATA) {
        or_inplace(&mut dest_file.texture, src_file.texture);
    }

    Ok(())
}

// NOTE: basically, to take full advantage of the existing infrastructure for ANM image sources,
// we implement directory image sources by "parsing" a directory into a fake ANM file object.
//
// I'm not sure if this is the best solution, as it could potentially open a large number of image
// files that might not even be related to our ANM file... (thankfully at this time, we only
// open them to read metadata.)             - Exp
fn read_directory_as_image_source(fs: &Fs, root: &Path) -> ReadResult<AnmFile> {
    let walk = {
        walkdir::WalkDir::new(root)
            .follow_links(true)
            .into_iter()
            .map(|result| result.map_err(|e| fs.emitter.emit(error!("{}", e))))
    };

    let mut anm_entries = vec![];
    for file_entry in walk {
        let file_entry = file_entry?;
        if !file_entry.file_type().is_file() {
            continue;
        }

        let path = file_entry.path();
        match path.extension() {
            None => continue,
            Some(ext) => if ext.to_string_lossy().to_ascii_lowercase() == "png" {
                let reader = fs.open(path)?.into_inner();
                let (metadata, _) = png::Decoder::new(reader).read_info().map_err(|e| fs.emitter.emit(error!("{}: {}", path.display(), e)))?;

                let path_string = {
                    match file_entry.path().strip_prefix(root).expect("bad walkdir prefix?!").to_string_lossy() {
                        std::borrow::Cow::Borrowed(s) => s.to_owned(),
                        std::borrow::Cow::Owned(lossy) => {
                            fs.emitter.emit(warning!("ignoring bad filename '{}'", lossy)).ignore();
                            continue;
                        },
                    }
                };

                anm_entries.push(Entry {
                    specs: EntrySpecs {
                        img_width: Some(sp!(metadata.width)),
                        img_height: Some(sp!(metadata.height)),
                        ..Default::default()
                    },
                    path: sp!(path_string.replace("\\", "/")), // FIXME: should hold PathBuf to eliminate sensitivity to path separator...
                    // we don't want to read pixel data, especially since we don't know if we'll even use it
                    texture: None,
                    path_2: None,
                    scripts: Default::default(),
                    sprites: Default::default(),
                })
            },
        }
    }
    Ok(AnmFile { entries: anm_entries, binary_filename: None })
}

// =============================================================================

fn compile(
    format: &FileFormat,
    ast: &ast::ScriptFile,
    ctx: &mut CompilerContext,
) -> Result<AnmFile, ErrorReported> {
    let instr_format = format.instr_format();

    let mut ast = ast.clone();
    crate::passes::resolve_names::assign_res_ids(&mut ast, ctx)?;

    let mut extra_type_checks = vec![];

    // an early pass to define global constants for sprite and script names
    let script_ids = gather_script_ids(&ast, ctx)?;
    for (index, &(ref script_name, _)) in script_ids.values().enumerate() {
        let const_value: Sp<ast::Expr> = sp!(script_name.span => (index as i32).into());
        ctx.define_auto_const_var(script_name.clone(), ScalarType::Int, const_value);
    }
    let sprite_ids = gather_sprite_id_exprs(&ast, ctx, &mut extra_type_checks)?;
    for (sprite_name, id_expr) in sprite_ids {
        ctx.define_auto_const_var(sprite_name, ScalarType::Int, id_expr);
    }

    // preprocess
    let ast = {
        let mut ast = ast;
        crate::passes::resolve_names::run(&ast, ctx)?;
        crate::passes::type_check::run(&ast, ctx)?;
        crate::passes::type_check::extra_checks(&extra_type_checks, ctx)?;
        crate::passes::evaluate_const_vars::run(ctx)?;
        crate::passes::const_simplify::run(&mut ast, ctx)?;
        crate::passes::desugar_blocks::run(&mut ast, ctx)?;
        ast
    };

    // group scripts by entry
    let mut groups = vec![];
    let mut cur_entry = None::<Entry>;
    let mut cur_group = vec![];
    let mut script_names = vec![];
    for item in &ast.items {
        match &item.value {
            ast::Item::Meta { keyword: sp_pat!(ast::MetaKeyword::Entry), fields, .. } => {
                if let Some(prev_entry) = cur_entry.take() {
                    groups.push((prev_entry, cur_group));
                }
                cur_entry = Some(Entry::from_fields(fields, ctx.emitter).map_err(|e| ctx.emitter.emit(e))?);
                cur_group = vec![];
            },
            &ast::Item::AnmScript { number: _, ref ident, ref code, .. } => {
                if cur_entry.is_none() { return Err(ctx.emitter.emit(error!(
                    message("orphaned ANM script with no entry"),
                    primary(item, "orphaned script"),
                    note("at least one `entry` must come before scripts in an ANM file"),
                )))}
                cur_group.push((ident, code));
                script_names.push(ident);
            },
            ast::Item::ConstVar { .. } => {},
            _ => return Err(ctx.emitter.emit(error!(
                message("feature not supported by format"),
                primary(item, "not supported by ANM files"),
            ))),
        }
    }

    match cur_entry {
        None => return Err(ctx.emitter.emit(error!("empty ANM script"))),
        Some(cur_entry) => groups.push((cur_entry, cur_group)),  // last group
    }

    let entries = groups.into_iter().map(|(mut entry, ast_scripts)| {
        for (name, code) in ast_scripts {
            let (_, sp_pat![id]) = script_ids[&name.value];
            let instrs = llir::lower_sub_ast_to_instrs(instr_format, &code.0, ctx)?;

            entry.scripts.insert(sp!(name.span => name.value.clone()), Script { id, instrs });
        }
        Ok::<_, ErrorReported>(entry)
    }).collect_with_recovery()?;
    Ok(AnmFile { entries, binary_filename: None })
}

fn write_thecl_defs(
    mut w: impl io::Write,
    anm: &AnmFile,
) -> Result<(), io::Error> {
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

// (this returns a Vec instead of a Map because there may be multiple sprites with the same Ident)
fn gather_sprite_id_exprs(
    ast: &ast::ScriptFile,
    ctx: &mut CompilerContext,
    extra_type_checks: &mut Vec<crate::passes::type_check::ShallowTypeCheck>,
) -> Result<Vec<(Sp<ResIdent>, Sp<ast::Expr>)>, ErrorReported> {
    let all_entries = ast.items.iter().filter_map(|item| match &item.value {
        ast::Item::Meta { keyword: sp_pat!(ast::MetaKeyword::Entry), fields, .. } => Some(fields),
        _ => None,
    });

    let mut auto_sprites = sequential_int_exprs(sp!(0.into()));
    let mut out = vec![];
    for entry_fields in all_entries {
        type ProtoSprites<'a> = IndexMap<Sp<Ident>, ProtoSprite<'a>>;

        let sprites = meta::ParseObject::new(entry_fields).expect_field::<ProtoSprites>("sprites");
        let sprites = sprites.map_err(|e| ctx.emitter.emit(e))?;
        for (ident, sprite) in sprites {
            if let Some(id_expr) = sprite.id_expr.cloned() {
                // currently nothing else can really type-check this before const evaluation, so add a deferred check
                extra_type_checks.push(crate::passes::type_check::ShallowTypeCheck {
                    expr: id_expr.clone(),
                    ty: ScalarType::Int.into(),
                    cause: None,
                });
                // restart numbering from the new id
                auto_sprites = sequential_int_exprs(id_expr);
            };

            let sprite_id_span = sprite.id_expr.as_ref().map(|x| x.span).unwrap_or(ident.span);

            let sprite_id = sp!(sprite_id_span => auto_sprites.next().unwrap());

            // since these are just meta keys we have to synthesize new ResIds
            let res_ident = ident.clone().sp_map(|ident| ctx.resolutions.attach_fresh_res(ident));
            out.push((res_ident, sprite_id));
        }
    }

    Ok(out)
}

// for an expr `<e>`, produces `<e> + 0`, `<e> + 1`, `<e> + 2`...
fn sequential_int_exprs(e: Sp<ast::Expr>) -> impl Iterator<Item=ast::Expr> {
    (0..).map(move |i| {
        let addend: ast::Expr = i.into();
        rec_sp!(Span::NULL => expr_binop!(#(e.clone()) + #addend)).value
    })
}

/// A type that's parsed from the Meta in an early pass just to gather sprite names.
#[derive(Debug, Clone)]
pub struct ProtoSprite<'a> {
    /// const simplification has not yet been performed so we can at best extract an Expr
    pub id_expr: Option<&'a Sp<ast::Expr>>,
}

impl<'m> FromMeta<'m> for ProtoSprite<'m> {
    fn from_meta(meta: &'m Sp<Meta>) -> Result<Self, FromMetaError<'m>> {
        meta.parse_object(|m| {
            let id_expr = m.get_field("id")?;
            m.allow_unrecognized_fields()?;
            Ok(ProtoSprite { id_expr })
        })
    }
}

fn gather_script_ids(ast: &ast::ScriptFile, ctx: &mut CompilerContext) -> Result<IndexMap<Ident, (Sp<ResIdent>, Sp<i32>)>, ErrorReported> {
    let mut next_auto_script = 0;
    let mut script_ids = IndexMap::new();
    for item in &ast.items {
        match &item.value {
            &ast::Item::AnmScript { number, ref ident, .. } => {
                let script_id = number.unwrap_or(sp!(ident.span => next_auto_script));
                next_auto_script = script_id.value + 1;

                // give a better error on redefinitions than the generic "ambiguous auto const" message
                match script_ids.entry(ident.value.clone()) {
                    indexmap::map::Entry::Vacant(e) => {
                        let res_ident = ident.clone().sp_map(|name| ctx.resolutions.attach_fresh_res(name.clone()));
                        e.insert((res_ident, script_id));
                    },
                    indexmap::map::Entry::Occupied(e) => {
                        let (prev_ident, _) = e.get();
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

fn read_anm(
    reader: &mut BinReader,
    emitter: &impl Emitter,
    format: &FileFormat,
    with_images: bool,
) -> ReadResult<AnmFile> {
    let mut entries = vec![];
    let mut next_script_index = 0;
    loop {
        let (entry, control_flow) = read_entry(reader, emitter, format, with_images, &mut next_script_index)?;
        entries.push(entry);
        match control_flow {
            ControlFlow::Continue => {},
            ControlFlow::Stop => break,
        }
    }

    let binary_filename = Some(reader.display_filename().to_string());
    let mut anm = AnmFile { entries, binary_filename };
    strip_unnecessary_sprite_ids(&mut anm);
    Ok(anm)
}

fn read_entry(
    reader: &mut BinReader,
    emitter: &impl Emitter,
    format: &FileFormat,
    with_images: bool,
    next_script_index: &mut u32,
) -> ReadResult<(Entry, ControlFlow)> {
    let instr_format = format.instr_format();

    let entry_pos = reader.pos()?;

    // 64 byte header regardless of version
    let header_data = emitter.chain_with(|f| write!(f, "in header"), |emitter| {
        let header_data = format.read_header(reader, emitter)?;
        if header_data.has_data != header_data.has_data % 2 {
            emitter.emit(warning!("non-boolean value found for 'has_data': {}", header_data.has_data)).ignore();
        }
        if header_data.low_res_scale != header_data.low_res_scale % 2 {
            emitter.emit(warning!("non-boolean value found for 'low_res_scale': {}", header_data.low_res_scale)).ignore();
        }
        Ok(header_data)
    })?;

    let sprite_offsets = (0..header_data.num_sprites).map(|_| reader.read_u32()).collect::<ReadResult<Vec<_>>>()?;
    let script_ids_and_offsets = (0..header_data.num_scripts).map(|_| {
        Ok((reader.read_i32()?, reader.read_u32()? as u64))
    }).collect::<ReadResult<Vec<_>>>()?;
    // eprintln!("{:?}", header_data);
    // eprintln!("{:?}", sprite_offsets);
    // eprintln!("{:?}", script_ids_and_offsets);

    reader.seek_to(entry_pos + header_data.name_offset)?;
    let path = reader.read_cstring_blockwise(16)?.decode(DEFAULT_ENCODING).map_err(|e| emitter.emit(e))?;
    let path_2 = match header_data.secondary_name_offset {
        None => None,
        Some(n) => {
            reader.seek_to(entry_pos + n.get())?;
            Some(reader.read_cstring_blockwise(16)?.decode(DEFAULT_ENCODING).map_err(|e| emitter.emit(e))?)
        },
    };

    let mut sprites_seen_in_entry = IndexSet::new();
    let sprites = sprite_offsets.iter().map(|&offset| {
        reader.seek_to(entry_pos + offset as u64)?;
        let sprite = read_sprite(reader)?;
        let sprite_id = sprite.id.expect("(bug!) sprite read from binary must always have id");

        // Note: Duplicate IDs do happen between different entries, so we don't check that.
        if !sprites_seen_in_entry.insert(sprite_id) {
            emitter.emit(warning!("sprite ID {} appeared twice in same entry; only one will be kept", sprite_id)).ignore();
        }
        let key = sp!(auto_sprite_name(sprite_id as u32));

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
        let script_index = *next_script_index;
        let key = sp!(auto_script_name(script_index));
        *next_script_index += 1;

        let end_offset = all_offsets.iter().copied().filter(|&x| x > offset).min();

        let instrs = {
            reader.seek_to(entry_pos + offset)?;
            emitter.chain_with(|f| write!(f, "script {}", script_index), |emitter| {
                llir::read_instrs(reader, emitter, instr_format, offset, end_offset)
            })?
        };
        Ok((key, Script { id, instrs }))
    }).collect::<ReadResult<IndexMap<_, _>>>()?;

    let expect_no_texture = header_data.has_data == 0 || path.starts_with("@");
    if expect_no_texture != header_data.thtx_offset.is_none() {
        return Err(emitter.emit(error!("inconsistency between thtx_offset and has_data/name")));
    }

    let (tex_info, texture) = match header_data.thtx_offset {
        None => (None, None),
        Some(n) => {
            reader.seek_to(entry_pos + n.get())?;
            let (tex_info, maybe_texture) = read_texture(reader, emitter, with_images)?;
            (Some(tex_info), maybe_texture)
        },
    };
    let specs = EntrySpecs {
        buf_width: Some(sp!(header_data.width)),
        buf_height: Some(sp!(header_data.height)),
        buf_format: Some(sp!(header_data.format)),
        img_width: tex_info.as_ref().map(|x| sp!(x.width)),
        img_height: tex_info.as_ref().map(|x| sp!(x.height)),
        img_format: tex_info.as_ref().map(|x| sp!(x.format)),
        colorkey: Some(header_data.colorkey),
        offset_x: Some(header_data.offset_x), offset_y: Some(header_data.offset_y),
        memory_priority: Some(header_data.memory_priority),
        has_data: Some(header_data.has_data != 0),
        low_res_scale: Some(header_data.low_res_scale != 0),
    };

    let entry = Entry {
        path: sp!(path),
        path_2: path_2.map(|x| sp!(x)),
        texture, specs, sprites, scripts
    };

    reader.seek_to(entry_pos + header_data.next_offset)?;
    match header_data.next_offset {
        0 => Ok((entry, ControlFlow::Stop)),
        _ => Ok((entry, ControlFlow::Continue)),
    }
}

enum ControlFlow { Stop, Continue }

fn strip_unnecessary_sprite_ids(anm: &mut AnmFile) {
    let mut next_auto_sprite_id = 0;
    for entry in &mut anm.entries {
        for sprite in entry.sprites.values_mut() {
            let actual_id = sprite.id.unwrap_or(next_auto_sprite_id);
            if actual_id == next_auto_sprite_id {
                sprite.id = None;
            }
            next_auto_sprite_id = actual_id + 1;
        }
    }
}

pub fn auto_sprite_name(i: u32) -> Ident {
    format!("sprite{}", i).parse::<Ident>().unwrap()
}
pub fn auto_script_name(i: u32) -> Ident {
    format!("script{}", i).parse::<Ident>().unwrap()
}

fn write_anm(
    w: &mut BinWriter,
    emitter: &impl Emitter,
    format: &FileFormat,
    file: &AnmFile,
) -> WriteResult {
    let mut last_entry_pos = None;
    let mut next_auto_sprite_id = 0;
    for (entry_index, entry) in file.entries.iter().enumerate() {
        let entry_pos = w.pos()?;
        if let Some(last_entry_pos) = last_entry_pos {
            w.seek_to(last_entry_pos + format.offset_to_next_offset())?;
            w.write_u32((entry_pos - last_entry_pos) as _)?;
            w.seek_to(entry_pos)?;
        }

        emitter.chain_with(|f| write!(f, "in entry {} (for '{}')", entry_index, entry.path), |emitter| {
            write_entry(w, emitter, &format, entry, &mut next_auto_sprite_id)
        })?;

        last_entry_pos = Some(entry_pos);
    }
    Ok(())
}

fn write_entry(
    w: &mut BinWriter,
    emitter: &impl Emitter,
    file_format: &FileFormat,
    entry: &Entry,
    // automatic numbering state that needs to persist from one entry to the next
    next_auto_sprite_id: &mut u32,
) -> Result<(), ErrorReported> {
    let instr_format = file_format.instr_format();

    let entry_pos = w.pos()?;

    let EntrySpecs {
        buf_width, buf_height, buf_format,
        img_width, img_height, img_format,
        colorkey, offset_x, offset_y, memory_priority,
        has_data, low_res_scale,
    } = entry.specs.fill_defaults(file_format.game);

    fn missing(emitter: &impl Emitter, problem: &str, note_2: Option<&str>) -> ErrorReported {
        let mut diag = error!("{}", problem);
        diag.note(format!("if this data is available in an existing anm file, try using '-i ANM_FILE'"));
        if let Some(note) = note_2 {
            diag.note(note.to_string());
        }

        emitter.emit(diag)
    }

    let colorkey = colorkey.expect("has default");
    let offset_x = offset_x.expect("has default");
    let offset_y = offset_y.expect("has default");
    let memory_priority = memory_priority.expect("has default");
    let has_data = has_data.expect("has default");
    let low_res_scale = low_res_scale.expect("has default");
    let img_format = img_format.expect("has default");
    let buf_format = buf_format.expect("has default");

    macro_rules! expect {
        ($name:ident) => {
            $name.ok_or_else(|| {
                let problem = format!("missing required field '{}'!", stringify!($name));
                missing(emitter, &problem, None)
            })?
        };
    }

    file_format.write_header(w, &EntryHeaderData {
        width: expect!(buf_width).value,
        height: expect!(buf_height).value,
        format: buf_format.value,
        colorkey,
        offset_x,
        offset_y,
        memory_priority,
        low_res_scale: low_res_scale as u32,
        has_data: has_data as u32,
        version: file_format.version as u32,
        num_sprites: entry.sprites.len() as u32,
        num_scripts: entry.scripts.len() as u32,
        // we will overwrite these later
        name_offset: 0, secondary_name_offset: None,
        next_offset: 0, thtx_offset: None,
    })?;

    let sprite_offsets_pos = w.pos()?;
    w.write_u32s(&vec![0; entry.sprites.len()])?;
    let script_headers_pos = w.pos()?;
    w.write_u32s(&vec![0; 2 * entry.scripts.len()])?;

    let path_offset = w.pos()? - entry_pos;
    w.write_cstring(&Encoded::encode(&entry.path, DEFAULT_ENCODING).map_err(|e| emitter.emit(e))?, 16)?;

    let mut path_2_offset = 0;
    if let Some(path_2) = &entry.path_2 {
        path_2_offset = w.pos()? - entry_pos;
        w.write_cstring(&Encoded::encode(path_2, DEFAULT_ENCODING).map_err(|e| emitter.emit(e))?, 16)?;
    };

    let sprite_offsets = entry.sprites.iter().map(|(_, sprite)| {
        let sprite_offset = w.pos()? - entry_pos;

        let sprite_id = sprite.id.unwrap_or(*next_auto_sprite_id);
        *next_auto_sprite_id = sprite_id + 1;

        write_sprite(w, sprite_id, sprite)?;
        Ok(sprite_offset)
    }).collect::<WriteResult<Vec<_>>>()?;

    let script_ids_and_offsets = entry.scripts.iter().map(|(name, script)| {
        let script_offset = w.pos()? - entry_pos;
        emitter.chain_with(|f| write!(f, "in script {} (id {})", name, script.id), |emitter| {
            llir::write_instrs(w, emitter, instr_format, &script.instrs)
        })?;

        Ok((script.id, script_offset))
    }).collect::<WriteResult<Vec<_>>>()?;

    let mut texture_offset = 0;
    if has_data {
        match &entry.texture {
            None => {
                let problem = "no bitmap data available!";
                let note_2 = "alternatively, use 'has_data: false' to compile without an image";
                return Err(missing(emitter, problem, Some(note_2)));
            },
            Some(texture) => {
                let info = ThtxHeader {
                    width: img_width.expect("have texture but somehow missing img_width?!").value,
                    height: img_height.expect("have texture but somehow missing img_height?!").value,
                    format: img_format.value,
                };
                texture_offset = w.pos()? - entry_pos;
                write_texture(w, &info, texture)?;
            },
        }
    };

    let end_pos = w.pos()?;

    w.seek_to(entry_pos + file_format.offset_to_thtx_offset())?;
    w.write_u32(texture_offset as _)?;

    w.seek_to(entry_pos + file_format.offset_to_path_offset())?;
    w.write_u32(path_offset as _)?;

    if let Some(offset_to_path_2_offset) = file_format.offset_to_path_2_offset() {
        w.seek_to(entry_pos + offset_to_path_2_offset)?;
        w.write_u32(path_2_offset as _)?;
    }

    w.seek_to(sprite_offsets_pos)?;
    for sprite_offset in sprite_offsets {
        w.write_u32(sprite_offset as _)?;
    }

    w.seek_to(script_headers_pos)?;
    for (script_id, script_offset) in script_ids_and_offsets {
        w.write_u32(script_id as _)?;
        w.write_u32(script_offset as _)?;
    }

    w.seek_to(end_pos)?;
    Ok(())
}

fn read_sprite(f: &mut BinReader) -> ReadResult<Sprite> {
    Ok(Sprite {
        id: Some(f.read_u32()?),
        offset: f.read_f32s_2()?,
        size: f.read_f32s_2()?,
    })
}

fn write_sprite(
    f: &mut BinWriter,
    sprite_id: u32,  // we ignore sprite.id because that can be None
    sprite: &Sprite,
) -> WriteResult {
    f.write_u32(sprite_id)?;
    f.write_f32s(&sprite.offset)?;
    f.write_f32s(&sprite.size)
}

#[inline(never)]
fn read_texture(f: &mut BinReader, emitter: &impl Emitter, with_images: bool) -> ReadResult<(ThtxHeader, Option<Texture>)> {
    f.expect_magic(emitter, "THTX")?;

    let zero = f.read_u16()?;
    let format = f.read_u16()? as u32;
    let width = f.read_u16()? as u32;
    let height = f.read_u16()? as u32;
    let size = f.read_u32()?;
    if zero != 0 {
        emitter.emit(warning!("nonzero thtx_zero lost: {}", zero)).ignore();
    }
    let thtx = ThtxHeader { format, width, height };

    if with_images {
        let mut data = vec![0; size as usize];
        f.read_exact(&mut data)?;
        Ok((thtx, Some(Texture { data })))
    } else {
        Ok((thtx, None))
    }
}

#[inline(never)]
fn write_texture(f: &mut BinWriter, info: &ThtxHeader, texture: &Texture) -> WriteResult {
    f.write_all(b"THTX")?;

    f.write_u16(0)?;
    f.write_u16(info.format as _)?;
    f.write_u16(info.width as _)?;
    f.write_u16(info.height as _)?;

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
        true => Box::new(InstrFormat07 { version, game }),
        false => Box::new(InstrFormat06),
    };
    FileFormat { version, game, instr_format }
}

pub fn game_core_mapfile(game: Game) -> crate::Eclmap {
    super::core_mapfiles::anm::core_signatures(game).to_mapfile(game)
}

/// Type responsible for dealing with version differences in the format.
struct FileFormat {
    version: Version,
    game: Game,
    instr_format: Box<dyn InstrFormat>,
}
struct InstrFormat06;
struct InstrFormat07 { version: Version, game: Game }

impl FileFormat {
    fn read_header(&self, f: &mut BinReader, emitter: &dyn Emitter) -> ReadResult<EntryHeaderData> {
        let emitter = emitter.as_sized();

        macro_rules! warn_if_nonzero {
            ($name:literal, $expr:expr) => {
                match $expr {
                    0 => {},
                    x => emitter.emit(warning!("nonzero {} will be lost (value: {})", $name, x)).ignore(),
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

    fn write_header(&self, f: &mut BinWriter, header: &EntryHeaderData) -> WriteResult {
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

    fn default_memory_priority(&self) -> u32 {
        match self.version {
            Version::V0 => 0,
            _ => 10,
        }
    }
}

impl InstrFormat for InstrFormat06 {
    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, u16)> {
        vec![
            (IntrinsicInstrKind::Jmp, 5),
            (IntrinsicInstrKind::InterruptLabel, 22),
        ]
    }

    fn instr_header_size(&self) -> usize { 4 }

    fn read_instr(&self, f: &mut BinReader, _: &dyn Emitter) -> ReadResult<ReadInstr> {
        let time = match f.read_i16_or_eof() {
            Ok(Some(time)) => time as i32,
            Ok(None) => return Ok(ReadInstr::EndOfFile),
            Err(e) => return Err(e),
        };

        let opcode = f.read_i8()?;
        let argsize = f.read_u8()? as usize;
        let args_blob = f.read_byte_vec(argsize)?;
        let instr = RawInstr { time, opcode: opcode as u16, param_mask: 0, args_blob };

        if (time, opcode, argsize) == (0, 0, 0) {
            Ok(ReadInstr::MaybeTerminal(instr))
        } else {
            Ok(ReadInstr::Instr(instr))
        }
    }

    fn write_instr(&self, f: &mut BinWriter, _: &dyn Emitter, instr: &RawInstr) -> WriteResult {
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

    fn write_terminal_instr(&self, f: &mut BinWriter, _: &dyn Emitter) -> WriteResult {
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

    fn read_instr(&self, f: &mut BinReader, _: &dyn Emitter) -> ReadResult<ReadInstr> {
        let opcode = f.read_i16()?;
        let size = f.read_u16()? as usize;
        if opcode == -1 {
            return Ok(ReadInstr::Terminal);
        }

        let time = f.read_i16()? as i32;
        let param_mask = f.read_u16()?;
        let args_blob = f.read_byte_vec(size - self.instr_header_size())?;
        // eprintln!("opcode: {:04x}  size: {:04x}  time: {:04x}  param_mask: {:04x}  args: {:?}", opcode, size, time, param_mask, args);
        Ok(ReadInstr::Instr(RawInstr { time, opcode: opcode as u16, param_mask, args_blob }))
    }

    fn write_instr(&self, f: &mut BinWriter, _: &dyn Emitter, instr: &RawInstr) -> WriteResult {
        f.write_u16(instr.opcode)?;
        f.write_u16(self.instr_size(instr) as u16)?;
        f.write_i16(instr.time as i16)?;
        f.write_u16(instr.param_mask as u16)?;
        f.write_all(&instr.args_blob)?;
        Ok(())
    }

    fn write_terminal_instr(&self, f: &mut BinWriter, _: &dyn Emitter) -> WriteResult {
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
