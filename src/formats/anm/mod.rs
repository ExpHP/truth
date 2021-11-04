use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

use enum_map::EnumMap;
use indexmap::{IndexMap};

use crate::raw;
use crate::ast;
use crate::ast::meta::{self, FromMeta, FromMetaError, Meta, ToMeta};
use crate::io::{BinReader, BinWriter, ReadResult, WriteResult, Fs};
use crate::diagnostic::{Diagnostic, Emitter};
use crate::error::{GatherErrorIteratorExt, ErrorReported, ErrorFlag};
use crate::game::{Game, LanguageKey};
use crate::ident::{Ident, ResIdent};
use crate::image::ColorFormat;
use crate::llir::{self, RawInstr, InstrFormat, LanguageHooks, IntrinsicInstrKind, DecompileOptions, HowBadIsIt};
use crate::pos::{Sp, Span};
use crate::value::{ScalarValue, ScalarType};
use crate::context::CompilerContext;
use crate::resolve::RegId;

mod read_write;

// =============================================================================

/// Game-independent representation of an ANM file.
#[derive(Debug, Clone)]
pub struct AnmFile {
    pub entries: Vec<Entry>,
    /// Filename of a read binary file, for display purposes only.
    binary_filename: Option<String>,
}

impl AnmFile {
    pub fn decompile_to_ast(&self, game: Game, ctx: &mut CompilerContext, decompile_options: &DecompileOptions) -> Result<ast::ScriptFile, ErrorReported> {
        let emitter = ctx.emitter.while_decompiling(self.binary_filename.as_deref());
        decompile(self, &emitter, game, &*game_hooks(game), ctx, decompile_options)
    }

    pub fn compile_from_ast(game: Game, ast: &ast::ScriptFile, ctx: &mut CompilerContext) -> Result<Self, ErrorReported> {
        compile(&*game_hooks(game), ast, ctx)
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
    pub fn apply_image_source(&mut self, src: ImageSource, fs: &Fs<'_>) -> Result<(), ErrorReported> {
        match src {
            ImageSource::Anm(other) => apply_anm_image_source(self, other).map_err(|d| fs.emitter.emit(d)),
            ImageSource::Directory(path) => apply_directory_image_source(fs, self, &path),
        }
    }

    pub fn extract_images(&self, dest: &Path, fs: &Fs<'_>) -> WriteResult {
        extract(fs, self, dest)
    }

    pub fn write_to_stream(&self, w: &mut BinWriter, game: Game) -> WriteResult {
        let emitter = w.emitter();
        read_write::write_anm(w, &emitter, game, self)
    }

    pub fn read_from_stream(r: &mut BinReader, game: Game, with_images: bool) -> ReadResult<Self> {
        let emitter = r.emitter();
        read_write::read_anm(r, &emitter, game, with_images)
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

    /// Dimensions of an embedded image.  These are the values that will be written to the THTX section.
    ///
    /// It is possible for these to be `Some(_)` even if there is no embedded image, in particular
    /// after metadata is copied from an image source for a `has_data: false` entry.
    pub img_width: Option<Sp<u32>>,
    pub img_height: Option<Sp<u32>>,
    /// Color format of an embedded image.  This is the value that will be written to the THTX section.
    ///
    /// The number MAY correspond to a recognized [`ColorFormat`], but does not have to.
    pub img_format: Option<Sp<u32>>,

    /// When `true`, a THTX section with an embedded image will be stored.
    pub has_data: Option<HasData>,

    /// Dimensions of the buffer created at runtime for Direct3D.
    ///
    /// These should always be powers of 2.
    pub rt_width: Option<Sp<u32>>,
    pub rt_height: Option<Sp<u32>>,
    /// Color format of the buffer created by the game at runtime for Direct3D.
    pub rt_format: Option<Sp<u32>>,
    /// A transparent color for old games.
    pub colorkey: Option<u32>, // Only in old format

    /// A field of ANM entries that appears to represent the offset into the original image file
    /// on ZUN's PC from which the embedded image was extracted.
    ///
    /// Not sure if it has any meaning at runtime in-game. (FIXME)
    ///
    /// For reasons that have been lost to the sands of time, when thanm extracts an image that sets
    /// this field, it produces a PNG that is padded on the left and top so that the extracted data
    /// begins at this pixel offset. thcrap also uses this offset when hot-swapping image files,
    /// since it is designed to work with thanm.
    ///
    /// Since we want to be compatible with thcrap, we have to do this as well...
    pub offset_x: Option<u32>,
    pub offset_y: Option<u32>,
    /// :shrug:
    pub memory_priority: Option<u32>,

    /// A field of an entry that tells the game to scale down certain hi-res textures on lower resolutions,
    /// e.g. the border around the game.  (not used for things like `ascii.anm` which have dedicated files
    /// for each resolution)
    pub low_res_scale: Option<bool>,
}

impl EntrySpecs {
    fn default_memory_priority(&self, version: Version) -> u32 {
        match version {
            Version::V0 => 0,
            _ => 10,
        }
    }

    pub fn fill_defaults(&self, game: Game) -> EntrySpecs {
        let version = Version::from_game(game);

        let img_format = Some(self.img_format.unwrap_or(sp!(DEFAULT_FORMAT)));
        EntrySpecs {
            img_width: self.img_width,
            img_height: self.img_height,
            rt_width: self.rt_width.or(self.img_width.map(|x| x.sp_map(u32::next_power_of_two))),
            rt_height: self.rt_height.or(self.img_height.map(|x| x.sp_map(u32::next_power_of_two))),
            img_format,
            rt_format: self.rt_format.or(img_format),
            offset_x: Some(self.offset_x.unwrap_or(0)),
            offset_y: Some(self.offset_y.unwrap_or(0)),
            colorkey: Some(self.colorkey.unwrap_or(0)),
            memory_priority: Some(self.memory_priority.unwrap_or(self.default_memory_priority(version))),
            low_res_scale: Some(self.low_res_scale.unwrap_or(DEFAULT_LOW_RES_SCALE)),
            has_data: Some(self.has_data.unwrap_or(DEFAULT_HAS_DATA)),
        }
    }

    pub fn suppress_defaults(&self, game: Game) -> EntrySpecs {
        let version = Version::from_game(game);

        EntrySpecs {
            img_width: self.img_width,
            img_height: self.img_height,
            // don't suppress rt_width and rt_height.  By always showing them in decompiled files, we increase the
            // likelihood of a user noticing that there's something important about powers of 2 in image dimensions,
            // possibly helping them to figure out why their non-power-of-2 PNG file looks bad when scrolled.
            rt_width: self.rt_width,
            rt_height: self.rt_height,

            img_format: self.img_format.filter(|&x| x != DEFAULT_FORMAT),
            rt_format: self.rt_format.filter(|&x| x != self.img_format.unwrap_or(sp!(DEFAULT_FORMAT))),
            offset_x: self.offset_x.filter(|&x| x != 0),
            offset_y: self.offset_y.filter(|&x| x != 0),
            colorkey: self.colorkey.filter(|&x| x != 0),
            memory_priority: self.memory_priority.filter(|&x| x != self.default_memory_priority(version)),
            low_res_scale: self.low_res_scale.filter(|&x| x != DEFAULT_LOW_RES_SCALE),
            has_data: self.has_data.filter(|&x| x != DEFAULT_HAS_DATA),
        }
    }
}

const DEFAULT_FORMAT: u32 = 1;
const DEFAULT_LOW_RES_SCALE: bool = false;
const DEFAULT_HAS_DATA: HasData = HasData::True;

impl Entry {
    fn make_meta(&self, game: Game) -> meta::Fields {
        let mut specs = self.specs.clone();

        // derive properties of the runtime buffer based on the image
        if let (Some(rt_width), Some(img_width)) = (specs.rt_width, specs.img_width) {
            if rt_width == img_width.next_power_of_two() {
                specs.rt_width = None;
            }
        }

        if let (Some(rt_height), Some(img_height)) = (specs.rt_height, specs.img_height) {
            if rt_height == img_height.next_power_of_two() {
                specs.rt_height = None;
            }
        }

        if let (Some(rt_format), Some(img_format)) = (specs.rt_format, specs.img_format) {
            if rt_format == img_format {
                specs.rt_format = None;
            }
        }

        let EntrySpecs {
            rt_width, rt_height, rt_format, colorkey, offset_x, offset_y,
            img_width, img_height, img_format, memory_priority, has_data, low_res_scale,
        } = &specs.suppress_defaults(game);

        Meta::make_object()
            .field("path", &self.path.value)
            .field_opt("path_2", self.path_2.as_ref().map(|x| &x.value))
            .field_opt("has_data", has_data.as_ref())
            .field_opt("img_width", img_width.as_ref().map(|x| x.value))
            .field_opt("img_height", img_height.as_ref().map(|x| x.value))
            .field_opt("img_format", img_format.as_ref().map(|x| format_to_meta(x.value)))
            .field_opt("offset_x", offset_x.as_ref())
            .field_opt("offset_y", offset_y.as_ref())
            .field_opt("colorkey", colorkey.as_ref().map(|&value| ast::Expr::LitInt { value: value as i32, radix: ast::IntRadix::Hex }))
            .field_opt("rt_width", rt_width.as_ref().map(|x| x.value))
            .field_opt("rt_height", rt_height.as_ref().map(|x| x.value))
            .field_opt("rt_format", rt_format.as_ref().map(|x| format_to_meta(x.value)))
            .field_opt("memory_priority", memory_priority.as_ref())
            .field_opt("low_res_scale", low_res_scale.as_ref())
            .field("sprites", &self.sprites)
            .build_fields()
    }

    fn from_fields<'a>(fields: &'a Sp<meta::Fields>, emitter: &impl Emitter) -> Result<Self, FromMetaError<'a>> {
        meta::ParseObject::scope(fields, |m| {
            let deprecated_format = m.get_field_and_key("format")?;
            let deprecated_width = m.get_field_and_key("width")?;
            let deprecated_height = m.get_field_and_key("height")?;
            let mut rt_format = m.get_field::<Sp<u32>>("rt_format")?;
            let mut rt_width = m.get_field::<Sp<u32>>("rt_width")?;
            let mut rt_height = m.get_field::<Sp<u32>>("rt_height")?;
            for (deprecated_key_value, value) in vec![
                (deprecated_format, &mut rt_format),
                (deprecated_width, &mut rt_width),
                (deprecated_height, &mut rt_height),
            ] {
                static ONCE: std::sync::Once = std::sync::Once::new();

                if let Some((deprecated_key, deprecated_value)) = deprecated_key_value {
                    ONCE.call_once(|| emitter.emit(warning!(
                        message("\
                            deprecation warning: 'format', 'width', and 'height' have been \
                            renamed to 'rt_format', 'rt_width', and 'rt_height'.  The old \
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

            let colorkey = m.get_field("colorkey")?;
            let offset_x = m.get_field("offset_x")?;
            let offset_y = m.get_field("offset_y")?;
            let memory_priority = m.get_field("memory_priority")?;
            let low_res_scale = m.get_field("low_res_scale")?;
            let has_data = m.get_field("has_data")?;
            let path: Sp<String> = m.expect_field("path")?;
            let path_2 = m.get_field("path_2")?;
            let texture = None;
            let sprites = m.get_field("sprites")?.unwrap_or_default();

            for (field, rt_value) in vec![
                ("height", rt_height),
                ("width", rt_width),
            ] {
                if let Some(rt_value) = rt_value {
                    if !rt_value.value.is_power_of_two() && !path.starts_with("@") {
                        emitter.emit(warning!(
                            message("rt_{} = {} should be a power of two", field, rt_value),
                            primary(rt_value, "not a power of two")
                        )).ignore();
                    }
                }
            }

            let specs = EntrySpecs {
                rt_width, rt_height, rt_format,
                img_width, img_height, img_format,
                colorkey, offset_x, offset_y,
                memory_priority, has_data, low_res_scale,
            };
            let scripts = Default::default();
            Ok(Entry { specs, texture, path, path_2, scripts, sprites })
        })
    }
}

fn format_to_meta(format_num: u32) -> Meta {
    for known_format in ColorFormat::get_all() {
        if format_num == known_format as u32 {
            let ident = ResIdent::new_null(known_format.const_name().parse::<Ident>().unwrap());
            return Meta::Scalar(sp!(ast::Expr::Var(sp!(ast::Var {
                name: ast::VarName::new_non_reg(ident),
                ty_sigil: None,
            }))));
        }
    }
    format_num.to_meta()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum HasData {
    /// Store no pixel data.
    False,
    /// Store pixel data copied from an image file.
    True,
    /// Generate and store dummy pixel data to be hot-swapped by thcrap.
    Dummy,
}

impl From<bool> for HasData {
    fn from(b: bool) -> Self { match b {
        true => HasData::True,
        false => HasData::False,
    }}
}

impl<'a> FromMeta<'a> for HasData {
    fn from_meta(meta: &'a Sp<Meta>) -> Result<Self, FromMetaError<'a>> {
        match meta.parse()? {
            ScalarValue::Int(0) => Ok(HasData::False),
            ScalarValue::Int(_) => Ok(HasData::True),
            ScalarValue::String(s) if s == "dummy" => Ok(HasData::Dummy),
            _ => Err(FromMetaError::expected("a boolean or the string \"dummy\"", meta)),
        }
    }
}

impl ToMeta for HasData {
    fn to_meta(&self) -> Meta {
        match self {
            HasData::False => false.to_meta(),
            HasData::True => true.to_meta(),
            HasData::Dummy => "dummy".to_meta(),
        }
    }
}

/// An embedded image (or at least metadata about an image) in an ANM entry.
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
    game: Game,
    hooks: &dyn LanguageHooks,
    ctx: &mut CompilerContext,
    decompile_options: &DecompileOptions,
) -> Result<ast::ScriptFile, ErrorReported> {
    let mut items = vec![];
    let mut raiser = llir::Raiser::new(hooks, &ctx.emitter, &ctx.defs, decompile_options)?;
    for entry in &anm_file.entries {
        items.push(sp!(ast::Item::Meta {
            keyword: sp!(ast::MetaKeyword::Entry),
            fields: sp!(entry.make_meta(game)),
        }));

        entry.scripts.iter().map(|(name, &Script { id, ref instrs })| {
            let code = emitter.chain_with(|f| write!(f, "in script{}", id), |emitter| {
                raiser.raise_instrs_to_sub_ast(emitter, instrs, &ctx.defs, &ctx.unused_node_ids)
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
    crate::passes::postprocess_decompiled(&mut out, ctx, decompile_options)?;
    Ok(out)
}

pub fn auto_sprite_name(i: u32) -> Ident {
    format!("sprite{}", i).parse::<Ident>().unwrap()
}
pub fn auto_script_name(i: u32) -> Ident {
    format!("script{}", i).parse::<Ident>().unwrap()
}

// =============================================================================

#[derive(Debug, Clone)]
pub enum ImageSource {
    Anm(AnmFile),
    Directory(PathBuf),
}

fn apply_anm_image_source(dest_file: &mut AnmFile, src_file: AnmFile) -> Result<(), Diagnostic> {
    let mut src_entries_by_path: IndexMap<_, Vec<_>> = IndexMap::new();
    for entry in src_file.entries {
        src_entries_by_path.entry(entry.path.clone()).or_default().push(entry);
    };
    for vec in src_entries_by_path.values_mut() {
        vec.reverse();  // so we can pop them in forwards order
    }

    for dest_entry in &mut dest_file.entries {
        if let Some(src_entry) = src_entries_by_path.get_mut(&dest_entry.path).and_then(|vec| vec.pop()) {
            update_entry_from_anm_image_source(dest_entry, src_entry)?;
        }
    }
    Ok(())
}

fn update_entry_from_anm_image_source(dest_file: &mut Entry, mut src_file: Entry) -> Result<(), Diagnostic> {
    let dest_specs = &mut dest_file.specs;

    // though it's tedious, we fully unpack this struct to that the compiler doesn't
    // let us forget to update this function when we add a new field.
    let EntrySpecs {
        img_width: src_img_width, img_height: src_img_height, img_format: src_img_format,
        rt_width: src_rt_width, rt_height: src_rt_height, rt_format: src_rt_format,
        colorkey: src_colorkey, offset_x: src_offset_x, offset_y: src_offset_y,
        memory_priority: src_memory_priority, has_data: src_has_data,
        low_res_scale: src_low_res_scale,
    } = src_file.specs;

    or_inplace(&mut dest_specs.img_width, src_img_width);
    or_inplace(&mut dest_specs.img_height, src_img_height);
    or_inplace(&mut dest_specs.img_format, src_img_format);
    or_inplace(&mut dest_specs.rt_width, src_rt_width);
    or_inplace(&mut dest_specs.rt_height, src_rt_height);
    or_inplace(&mut dest_specs.rt_format, src_rt_format);
    or_inplace(&mut dest_specs.colorkey, src_colorkey);
    or_inplace(&mut dest_specs.offset_x, src_offset_x);
    or_inplace(&mut dest_specs.offset_y, src_offset_y);
    or_inplace(&mut dest_specs.memory_priority, src_memory_priority);
    or_inplace(&mut dest_specs.low_res_scale, src_low_res_scale);
    or_inplace(&mut dest_specs.has_data, src_has_data);

    for (dest_dim, src_dim) in vec![
        (dest_specs.img_width, src_img_width),
        (dest_specs.img_height, src_img_height),
    ] {
        if src_dim.is_some() && dest_dim != src_dim {
            // (we can safely unwrap all of these options because at least one src_dim is Some,
            //  which implies both of them are, which also implies that the dest_dims are Some)
            return Err(error!(
                "mismatch in embedded image size for '{}': expected {}x{}, got {}x{}",
                dest_file.path,
                dest_specs.img_width.unwrap(), dest_specs.img_height.unwrap(),
                src_img_width.unwrap(), src_img_height.unwrap(),
            ));
        }
    }

    // Importing a pixel buffer from an ANM file.  (offset has no effect here)
    if dest_specs.has_data.unwrap_or(DEFAULT_HAS_DATA) == HasData::True {
        if let (None, Some(src_texture)) = (&dest_file.texture, src_file.texture.take()) {
            dest_specs.has_data = Some(HasData::True);

            let src_format_num = src_file.specs.img_format.expect("image source has pixel data but no format!?");
            let dest_format_num = dest_file.specs.img_format.expect("option was or-ed with Some so can't be None");
            if src_format_num == dest_format_num {
                dest_file.texture = Some(src_texture.clone());
            } else {
                let dest_cformat = ColorFormat::from_format_num(dest_format_num.value).ok_or_else(|| error!(
                    message("cannot transcode into unknown color format {}", dest_format_num),
                    primary(dest_format_num, "unknown color format"),
                ))?;
                let src_cformat = ColorFormat::from_format_num(src_format_num.value).ok_or_else(|| error!(
                    // this value has no span so produce a slightly different error
                    "cannot transcode from unknown color format {} (for image '{}')",
                    src_format_num, dest_file.path,
                ))?;

                let argb = src_cformat.transcode_to_argb_8888(&src_texture.data);
                let dest_data = dest_cformat.transcode_from_argb_8888(&argb);
                dest_file.texture = Some(Texture { data: dest_data });
            } // if src_format_num == dest_format_num
        } // if let ...
    } // if dest_specs.has_data....

    Ok(())
}

fn apply_directory_image_source(
    fs: &Fs,
    dest: &mut AnmFile,
    src_directory: &Path,
) -> Result<(), ErrorReported> {
    for entry in dest.entries.iter_mut() {
        update_entry_from_directory_source(fs, entry, src_directory)?;
    }
    Ok(())
}

fn update_entry_from_directory_source(
    fs: &Fs,
    dest_entry: &mut Entry,
    src_directory: &Path,
) -> Result<(), ErrorReported> {
    use image::{GenericImage, GenericImageView};

    let ref emitter = fs.emitter;
    let ref img_path = src_directory.join(&dest_entry.path.value);
    if !img_path.is_file() {  // race condition but not a big deal
        return Ok(());
    }

    let (src_image, src_dimensions): (Option<image::DynamicImage>, _);
    match dest_entry.specs.has_data.unwrap_or(DEFAULT_HAS_DATA) {
        HasData::True => {
            let image = image::open(img_path).map_err(|e| emitter.emit(error!(
                message("{}: {}", fs.display_path(img_path), e)
            )))?;
            src_dimensions = image.dimensions();
            src_image = Some(image);
        },
        HasData::Dummy | HasData::False => {
            let dims = image::image_dimensions(img_path).map_err(|e| emitter.emit(error!(
                message("{}: {}", fs.display_path(img_path), e)
            )))?;
            src_image = None;
            src_dimensions = dims;
        },
    }

    // these must be well-defined for us to continue, so fill in defaults early
    let dest_format = *dest_entry.specs.img_format.get_or_insert(sp!(DEFAULT_FORMAT));
    let offsets = (
        *dest_entry.specs.offset_x.get_or_insert(0),
        *dest_entry.specs.offset_y.get_or_insert(0),
    );

    // set missing dest dimensions
    for (dest_dim, src_dim, offset) in vec![
        (&mut dest_entry.specs.img_width, src_dimensions.0, offsets.0),
        (&mut dest_entry.specs.img_height, src_dimensions.1, offsets.1),
    ] {
        if dest_dim.is_none() {
            if src_dim >= offset {
                *dest_dim = Some(sp!(src_dim - offset));
            } else {
                return Err(emitter.emit(error!(
                    "{}: image too small ({}x{}) for an offset of ({}, {})",
                    fs.display_path(img_path),
                    src_dimensions.0, src_dimensions.1,
                    offsets.0, offsets.1,
                )))
            }
        }
    }

    // all dest dimensions are set now, but pre-existing ones might not match the image
    let dest_dimensions = (
        dest_entry.specs.img_width.unwrap().value,
        dest_entry.specs.img_height.unwrap().value,
    );
    let expected_src_dimensions = (dest_dimensions.0 + offsets.0, dest_dimensions.1 + offsets.1);
    if src_dimensions != expected_src_dimensions {
        return Err(emitter.emit(error!(
            "{}: wrong image dimensions (expected {}x{}, got {}x{})",
            fs.display_path(img_path),
            expected_src_dimensions.0, expected_src_dimensions.1,
            src_dimensions.0, src_dimensions.1,
        )))
    }

    // if we read an image, load it into the right format
    if dest_entry.texture.is_none() && src_image.is_some() {
        let dest_cformat = ColorFormat::from_format_num(dest_format.value).ok_or_else(|| emitter.emit(error!(
            message("cannot transcode into unknown color format {}", dest_format),
            primary(dest_format, "unknown color format"),
        )))?;

        let src_data_argb = {
            src_image.unwrap().into_bgra8()
                .sub_image(offsets.0, offsets.1, dest_dimensions.0, dest_dimensions.1)
                .to_image().into_raw()
        };

        let dest_data = dest_cformat.transcode_from_argb_8888(&src_data_argb);
        dest_entry.texture = Some(Texture { data: dest_data });
    }

    Ok(())
}

fn or_inplace<T>(dest: &mut Option<T>, src: Option<T>) {
    *dest = dest.take().or(src);
}

// =============================================================================

fn extract(
    fs: &Fs<'_>,
    anm: &AnmFile,
    out_path: &Path,
) -> Result<(), ErrorReported> {
    // call this now to make sure ancestors of out_path don't get implicitly created when
    // we use create_dir_all later
    fs.ensure_dir(out_path)?;

    let canonical_out_path = fs.canonicalize(out_path).map_err(|e| fs.emitter.emit(e))?;

    anm.entries.iter().map(|entry| {
        if entry.texture.is_none() {
            return Ok(());
        }

        // tarbomb protection
        let full_path = canonical_out_path.join(&entry.path);
        let full_path = canonicalize_part_of_path_that_exists(full_path.as_ref()).map_err(|e| {
            fs.emitter.emit(error!("while resolving '{}': {}", fs.display_path(&full_path), e))
        })?;
        let display_path = fs.display_path(&full_path);
        if full_path.strip_prefix(&canonical_out_path).is_err() {
            return Err(fs.emitter.emit(error!(
                message("skipping '{}': outside of destination directory", display_path),
            )));
        }

        if let Some(parent) = full_path.parent() {
            fs.create_dir_all(&parent)?;
        }

        let image = produce_image_from_entry(entry).map_err(|s| {
            fs.emitter.emit(error!("skipping '{}': {}", display_path, s))
        })?;

        image.save(full_path).map_err(|e| {
            fs.emitter.emit(error!("while writing '{}': {}", display_path, e))
        })?;

        println!("exported '{}'", display_path);
        Ok(())
    }).collect_with_recovery()
}

// based on cargo's normalize_path
pub fn canonicalize_part_of_path_that_exists(path: &Path) -> Result<PathBuf, std::io::Error> {
    let mut components = path.components().peekable();
    let mut ret = if let Some(c @ std::path::Component::Prefix(..)) = components.peek().cloned() {
        components.next();
        PathBuf::from(c.as_os_str())
    } else {
        PathBuf::new()
    };

    for component in components {
        match component {
            std::path::Component::Prefix(..) => unreachable!(),
            std::path::Component::RootDir => {
                ret.push(component.as_os_str());
                ret = ret.canonicalize()?;
            }
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => { ret.pop(); }
            std::path::Component::Normal(c) => {
                ret.push(c);
                if let Ok(dest) = ret.read_link() {
                    ret = dest.canonicalize()?;
                }
            }
        }
    }
    Ok(ret)
}

type BgraImage<V=Vec<u8>> = image::ImageBuffer<image::Bgra<u8>, V>;

fn produce_image_from_entry(entry: &Entry) -> Result<image::RgbaImage, String> {
    use image::{GenericImage, buffer::ConvertBuffer};

    let texture = entry.texture.as_ref().expect("produce_image_from_entry called without texture!");
    let content_width = entry.specs.img_width.expect("has data but no width?!").value;
    let content_height = entry.specs.img_height.expect("has data but no height?!").value;
    let format = entry.specs.img_format.expect("defaults were filled...").value;
    let cformat = ColorFormat::from_format_num(format).ok_or_else(|| {
        format!("cannot transcode from unknown color format {}", format)
    })?;

    let content_argb = cformat.transcode_to_argb_8888(&texture.data);
    let content = BgraImage::from_raw(content_width, content_height, &content_argb[..]).expect("size error?!");

    let offset_x = entry.specs.offset_x.unwrap_or(0);
    let offset_y = entry.specs.offset_y.unwrap_or(0);
    let output_width = content_width + offset_x;
    let output_height = content_height + offset_y;
    let output_init_argb = vec![0xFF; 4 * output_width as usize * output_height as usize];
    let mut output = BgraImage::from_raw(output_width, output_height, output_init_argb).expect("size error?!");

    output.sub_image(offset_x, offset_y, content_width, content_height)
        .copy_from(&content, 0, 0)
        .expect("region should definitely be large enough");

    Ok(output.convert())
}

// =============================================================================

fn compile(
    hooks: &dyn LanguageHooks,
    ast: &ast::ScriptFile,
    ctx: &mut CompilerContext,
) -> Result<AnmFile, ErrorReported> {
    let mut ast = ast.clone();
    crate::passes::resolution::assign_languages(&mut ast, hooks.language(), ctx)?;

    define_color_format_consts(ctx);

    // an early pass to define global constants for sprite and script names
    let mut extra_type_checks = vec![];
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
        crate::passes::resolution::resolve_names(&ast, ctx)?;
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

    let mut errors = ErrorFlag::new();
    let mut lowerer = llir::Lowerer::new(hooks);
    let mut entries = vec![];
    groups.into_iter().map(|(mut entry, ast_scripts)| {
        for (name, code) in ast_scripts {
            let (_, sp_pat![id]) = script_ids[&name.value];
            let instrs = lowerer.lower_sub(&code.0, ctx)?;

            entry.scripts.insert(sp!(name.span => name.value.clone()), Script { id, instrs });
        }
        entries.push(entry);
        Ok::<_, ErrorReported>(())
    }).collect_with_recovery().unwrap_or_else(|e| errors.set(e));

    lowerer.finish(ctx).unwrap_or_else(|e| errors.set(e));
    errors.into_result(())?;

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

/// Define `FORMAT_ARGB_8888` and etc.
fn define_color_format_consts(
    ctx: &mut CompilerContext,
) {
    for format in ColorFormat::get_all() {
        let ident = format.const_name().parse::<Ident>().unwrap();
        let ident = ctx.resolutions.attach_fresh_res(ident);
        ctx.define_auto_const_var(sp!(ident), ScalarType::Int, sp!((format as u32 as i32).into()));
    }
}

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
            Th13 | Th14 | Th143 | Th15 | Th16 | Th165 | Th17 | Th18 => Version::V8,
        }
    }

    fn is_old_header(self) -> bool { self < Version::V7 }
}

fn game_hooks(game: Game) -> Box<dyn LanguageHooks> {
    let version = Version::from_game(game);
    let instr_format = read_write::get_instr_format(version);
    match version {
        Version::V0 => Box::new(AnmHooks06 { instr_format }),
        _ => Box::new(AnmHooks07 { version, game, instr_format }),
    }
}

struct AnmHooks06 { instr_format: Box<dyn InstrFormat> }
struct AnmHooks07 { version: Version, game: Game, instr_format: Box<dyn InstrFormat> }

impl LanguageHooks for AnmHooks06 {
    fn language(&self) -> LanguageKey { LanguageKey::Anm }

    fn has_registers(&self) -> bool { false }

    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, raw::Opcode)> {
        vec![
            (IntrinsicInstrKind::Jmp, 5),
            (IntrinsicInstrKind::InterruptLabel, 22),
        ]
    }

    fn is_th06_anm_terminating_instr(&self, opcode: raw::Opcode) -> bool {
        // This is the check that TH06 ANM uses to know when to stop searching for interrupt labels.
        // Basically, the first `delete` or `static` marks the end of the script.
        opcode == 0 || opcode == 15
    }

    fn instr_format(&self) -> &dyn InstrFormat { &*self.instr_format }
}

impl LanguageHooks for AnmHooks07 {
    fn language(&self) -> LanguageKey { LanguageKey::Anm }

    fn has_registers(&self) -> bool { true }

    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, raw::Opcode)> {
        use IntrinsicInstrKind as I;

        match self.version {
            Version::V0 => unreachable!(),
            Version::V2 | Version::V3 => {
                let mut out = vec![
                    (I::Jmp, 4),
                    (I::CountJmp, 5),
                    (I::InterruptLabel, 21),
                    (I::UnOp(token![sin], ScalarType::Float), 61),
                    (I::UnOp(token![cos], ScalarType::Float), 62),
                    // (I::UnOp(Un::Tan, ScalarType::Float), 63),
                    // (I::UnOp(Un::Acos, ScalarType::Float), 64),
                    // (I::UnOp(Un::Atan, ScalarType::Float), 65),
                ];
                I::register_assign_ops(&mut out, 37);
                I::register_binary_ops(&mut out, 49);
                I::register_cond_jumps(&mut out, 67);
                out
            },
            Version::V4 | Version::V7 => {
                let mut out = vec![
                    (I::Jmp, 4),
                    (I::CountJmp, 5),
                    (I::InterruptLabel, 64),
                    (I::UnOp(token![sin], ScalarType::Float), 42),
                    (I::UnOp(token![cos], ScalarType::Float), 43),
                    // (I::UnOp(Un::Tan, ScalarType::Float), 44),
                    // (I::UnOp(Un::Acos, ScalarType::Float), 45),
                    // (I::UnOp(Un::Atan, ScalarType::Float), 46),
                ];
                I::register_assign_ops(&mut out, 6);
                I::register_binary_ops(&mut out, 18);
                I::register_cond_jumps(&mut out, 28);
                out
            },
            Version::V8 => {
                let mut out = vec![
                    (I::Jmp, 200),
                    (I::CountJmp, 201),
                    (I::InterruptLabel, 5),
                    (I::UnOp(token![sin], ScalarType::Float), 124),
                    (I::UnOp(token![cos], ScalarType::Float), 125),
                    // (I::UnOp(Un::Tan, ScalarType::Float), 126),
                    // (I::UnOp(Un::Acos, ScalarType::Float), 127),
                    // (I::UnOp(Un::Atan, ScalarType::Float), 128),
                ];
                I::register_assign_ops(&mut out, 100);
                I::register_binary_ops(&mut out, 112);
                I::register_cond_jumps(&mut out, 202);
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

    fn instr_disables_scratch_regs(&self, opcode: u16) -> Option<HowBadIsIt> {
        // copyParentVars
        (Game::Th14 <= self.game && opcode == 509)
            .then(|| HowBadIsIt::OhItsJustThisOneFunction)
    }

    fn instr_format(&self) -> &dyn InstrFormat { &*self.instr_format }
}
