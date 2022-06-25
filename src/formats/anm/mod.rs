use std::fmt;
use std::io;
use std::path::{Path, PathBuf};
use std::rc::Rc;

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
use crate::llir::{self, RawInstr, InstrFormat, LanguageHooks, DecompileOptions, HowBadIsIt};
use crate::pos::{Sp, Span};
use crate::value::{ScalarValue, ScalarType};
use crate::context::CompilerContext;
use crate::context::defs::auto_enum_names;
use crate::resolve::RegId;
use crate::debug_info;

mod read_write;
mod image_io;

use soft_option::SoftOption;
mod soft_option;

// =============================================================================

/// Game-independent representation of an ANM file.
#[derive(Debug, Clone)]
pub struct AnmFile {
    pub entries: Vec<Entry>,
    /// Filename of a read binary file, for display purposes only.
    binary_filename: Option<String>,
}

/// Type used to represent ANM files while truanm is doing most of its work.
///
/// This has to contain Options and etc. for the sake of the "merging" of entries that
/// occurs when `--image-source` is used.
#[derive(Debug, Clone)]
pub struct WorkingAnmFile {
    entries: Vec<WorkingEntry>,
    /// Filename of a read binary file, for display purposes only.
    binary_filename: Option<String>,
}

impl AnmFile {
    pub fn decompile_to_ast(&self, game: Game, ctx: &mut CompilerContext, decompile_options: &DecompileOptions) -> Result<ast::ScriptFile, ErrorReported> {
        let emitter = ctx.emitter.while_decompiling(self.binary_filename.as_deref());
        decompile(self, &emitter, game, &*game_hooks(game), ctx, decompile_options)
    }
}

impl WorkingAnmFile {
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
            ImageSource::Directory(path) => image_io::apply_directory_image_source(fs, self, &path),
        }
    }
}

impl AnmFile {
    pub fn extract_images(&self, dest: &Path, fs: &Fs<'_>) -> WriteResult {
        image_io::extract(fs, self, dest)
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

impl WorkingAnmFile {
    /// Finish working on the ANM file, filling in defaults and transcoding image buffer data
    /// as necessary.
    pub fn finalize(self, fs: &Fs, game: Game, emitter: &impl Emitter) -> Result<AnmFile, ErrorReported> {
        Ok(AnmFile {
            entries: {
                self.entries.into_iter()
                    .map(|entry| finalize_entry(fs, entry, game, emitter))
                    .collect::<Result<_, _>>()?
            },
            binary_filename: self.binary_filename,
        })
    }
}

// impl AnmFile {
//     /// Take a recently read [`AnmFile`] and turn it into anFinish working on the ANM file, filling in defaults and transcoding image buffer data
//     /// as necessary.
//     pub fn make_working(self, fs: &Fs, game: Game, emitter: &impl Emitter) -> Result<AnmFile, ErrorReported> {
//         Ok(AnmFile {
//             entries: {
//                 self.entries.into_iter()
//                     .map(|entry| finalize_entry(fs, entry, game, emitter))
//                     .collect::<Result<_, _>>()?
//             },
//             binary_filename: self.binary_filename,
//         })
//     }
// }

#[derive(Debug, Clone)]
pub struct Entry {
    pub specs: EntrySpecs,
    /// Data bytes for an embedded bitmap.  Its exact format is specified by [`Self::texture_metadata`].
    texture_data: Option<TextureData>,
    /// Represents a `THTX` section in the file, which holds an embedded bitmap.
    ///
    /// Sometimes this can be `Some` even if [`Self::texture_data`] is `None`. (e.g. during decompilation,
    /// truth does not read the embedded data bytes from THTX sections, but still reads the header in order
    /// to generate `img_width:` and friends)
    texture_metadata: Option<TextureMetadata>,
    // FIXME: Should hold PathBuf especially since we do equality comparisons on it
    pub path: Sp<String>,
    pub path_2: Option<Sp<String>>,
    pub scripts: IndexMap<Sp<Ident>, Script>,
    pub sprites: IndexMap<Sp<Ident>, Sprite>,
}

// Some methods to abstract away internal details from integration tests.
impl Entry {
    /// For an ANM file read from disk, indicates the value of the raw `has_data` field.
    pub fn has_thtx_section(&self) -> bool {
        // uses texture_metadata instead of texture_data to be correct even when image data was skipped during load
        self.texture_metadata.is_some()
    }

    /// Data bytes from the THTX section, if one was present and the data was not skipped during reading.
    pub fn img_data(&self) -> Option<&[u8]> { self.texture_data.as_ref().map(|d| &d.data[..]) }

    /// Width from the THTX section. (this is `Some` if and only if [`Self::has_thtx_section`] returns `true`)
    pub fn img_width(&self) -> Option<u32> { self.texture_metadata.as_ref().map(|m| m.width) }
    /// Height from the THTX section. (this is `Some` if and only if [`Self::has_thtx_section`] returns `true`)
    pub fn img_height(&self) -> Option<u32> { self.texture_metadata.as_ref().map(|m| m.height) }
    /// Format from the THTX section. (this is `Some` if and only if [`Self::has_thtx_section`] returns `true`)
    pub fn img_format(&self) -> Option<u32> { self.texture_metadata.as_ref().map(|m| m.format) }
}

/// Type used to represent entries while truanm is doing most of its work.
///
/// This has to contain Options and etc. for the sake of the "merging" of entries that
/// occurs when `--image-source` is used.
#[derive(Debug, Clone)]
struct WorkingEntry {
    specs: WorkingEntrySpecs,

    /// Holds the most recently loaded texture for this entry.
    ///
    /// For explicitly-provided image dimensions, `img_width` may differ from this texture's `width` and etc.,
    /// and that should generate an error near the end of compilation.  (and a difference in `img_format`
    /// should lead to transcoding).
    loaded_texture: Option<TextureFromSource>,

    path: Sp<String>,
    path_2: Option<Sp<String>>,
    scripts: IndexMap<Sp<Ident>, Script>,
    sprites: IndexMap<Sp<Ident>, Sprite>,
}

#[derive(Debug, Clone)]
pub struct Script {
    pub id: i32,
    pub instrs: Vec<RawInstr>,
}

#[derive(Debug, Clone)]
enum TextureFromSource {
    FromAnmFile {
        texture: TextureData,
        metadata: TextureMetadata,
        anm_path: PathBuf,
    },
    FromImage {
        image_path: PathBuf,
    },
}

#[derive(Debug, Clone)]
pub struct EntrySpecs {
    /// Dimensions of the buffer created at runtime for Direct3D.
    ///
    /// These should always be powers of 2.
    pub rt_width: u32,
    pub rt_height: u32,
    /// Color format of the buffer created by the game at runtime for Direct3D.
    pub rt_format: u32,
    /// A transparent color for old games.
    pub colorkey: u32, // Only in old format

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
    pub offset_x: u32,
    pub offset_y: u32,
    /// :shrug:
    pub memory_priority: u32,

    /// A field of an entry that tells the game to scale down certain hi-res textures on lower resolutions,
    /// e.g. the border around the game.  (not used for things like `ascii.anm` which have dedicated files
    /// for each resolution)
    pub low_res_scale: bool,
}

#[derive(Debug, Clone, Default)]
struct WorkingEntrySpecs {
    /// Note it is possible for the width and height to have values even if there is no embedded image,
    /// since they may come from the script, or be taken from an image source when the script (or
    /// an ANM file image source) has `has_data: false`.
    img_width: SoftOption<u32>,
    img_height: SoftOption<u32>,
    img_format: SoftOption<u32>,
    has_data: SoftOption<HasData>,
    rt_width: SoftOption<u32>,
    rt_height: SoftOption<u32>,
    rt_format: SoftOption<u32>,
    colorkey: SoftOption<u32>,
    offset_x: SoftOption<u32>,
    offset_y: SoftOption<u32>,
    memory_priority: SoftOption<u32>,
    low_res_scale: SoftOption<bool>,
}

fn default_memory_priority(version: Version) -> u32 {
    match version {
        Version::V0 => 0,
        _ => 10,
    }
}

/// Finishes work on an entry during compilation.
fn finalize_entry(fs: &Fs, entry: WorkingEntry, game: Game, emitter: &impl Emitter) -> Result<Entry, ErrorReported> {
    let version = Version::from_game(game);

    // Fill in defaults to simplify reasoning.
    let mut specs = entry.specs.clone();
    specs.img_format.set_soft_if_missing(DEFAULT_COLOR_FORMAT as u32);
    specs.rt_format.set_soft_if_missing(specs.img_format.into_option().expect("was just set"));
    specs.offset_x.set_soft_if_missing(0);
    specs.offset_y.set_soft_if_missing(0);
    specs.colorkey.set_soft_if_missing(0);
    specs.memory_priority.set_soft_if_missing(default_memory_priority(version));
    specs.low_res_scale.set_soft_if_missing(DEFAULT_LOW_RES_SCALE);
    specs.has_data.set_soft_if_missing(DEFAULT_HAS_DATA);

    // Do this now.  For missing images that are also missing metadata,
    // this tends to produce the nicest error message.
    let texture_data = finalize_entry_texture(fs, &mut specs, &entry.path, entry.loaded_texture.as_ref())?;

    // More defaults
    if let Some(img_width) = specs.img_width.into_option() {
        specs.rt_width.set_soft_if_missing(u32::next_power_of_two(img_width));
    }
    if let Some(img_height) = specs.img_height.into_option() {
        specs.rt_height.set_soft_if_missing(u32::next_power_of_two(img_height));
    }

    // Now check that rt_width and rt_height were filled.
    for (rt_field, rt_name, img_name) in vec![
        (specs.rt_width, "rt_width", "img_width"),
        (specs.rt_height, "rt_height", "img_height"),
    ] {
        if rt_field.is_missing() {
            // It's only possible to get here if there's an explicit 'has_data: false'.
            // Otherwise, we would've gotten earlier error for missing image or image dimensions.
            //
            // (even an ANM image source with 'has_data: false' can't bring us here; we would've copied
            //  rt_width from the ANM file)
            let has_data_span = match specs.has_data {
                SoftOption::Explicit(sp) => sp.span,
                _ => unreachable!(),
            };

            return Err(emitter.emit(error!(
                message("missing required field '{rt_name}'!"),
                primary(has_data_span, "requires setting '{rt_name}'"),
                note("you can also set '{img_name}' to infer '{rt_name}' as the next power of 2"),
            )));
        }
    }

    Ok(Entry {
        specs: EntrySpecs{
            rt_format: specs.rt_format.into_option().expect("was filled by default"),
            rt_width: specs.rt_width.into_option().expect("we just checked that this was set!"),
            rt_height: specs.rt_height.into_option().expect("we just checked that this was set!"),
            offset_x: specs.offset_x.into_option().expect("was filled by default"),
            offset_y: specs.offset_y.into_option().expect("was filled by default"),
            colorkey: specs.colorkey.into_option().expect("was filled by default"),
            memory_priority: specs.memory_priority.into_option().expect("was filled by default"),
            low_res_scale: specs.low_res_scale.into_option().expect("was filled by default"),
        },
        texture_metadata: texture_data.as_ref().map(|_| TextureMetadata {
            width: specs.img_width.into_option().expect("was filled by default"),
            height: specs.img_height.into_option().expect("was filled by default"),
            format: specs.img_format.into_option().expect("was filled by default"),
        }),
        texture_data,
        path: entry.path,
        path_2: entry.path_2,
        scripts: entry.scripts,
        sprites: entry.sprites,
    })
}

fn finalize_entry_texture(fs: &Fs, specs: &mut WorkingEntrySpecs, entry_path: &str, loaded_texture: Option<&TextureFromSource>) -> Result<Option<TextureData>, ErrorReported> {
    let emitter = fs.emitter;

    let mut texture_data = None;
    if let Some(loaded_texture) = loaded_texture {
        texture_data = finalize_texture_from_loaded(fs, specs, entry_path, loaded_texture)?;
    }

    match specs.has_data.into_option().expect("should be filled by default already") {
        HasData::True => match texture_data {
            Some(texture_data) => Ok(Some(texture_data)),
            None => Err(emitter.emit(error!(
                message("no bitmap data available for '{}'", entry_path),
                note("you can use '-i ANM_FILE' or '-i path/to/patchdir' to import images"),
                note("alternatively, use 'has_data: false' to compile with no image, or 'has_data: \"dummy\"' to generate a magenta placeholder"),
            ))),
        },
        HasData::False => Ok(None),
        HasData::Dummy => {
            let has_data_span = match specs.has_data {
                SoftOption::Explicit(sp) => sp.span,
                _ => unreachable!("'dummy' can only be explicit"),
            };
            Ok(Some(generate_texture_dummy_data(fs.emitter, specs, entry_path, has_data_span)?))
        },
    }
}

fn finalize_texture_from_loaded(
    fs: &Fs,
    specs: &mut WorkingEntrySpecs,
    entry_path: &str,
    loaded_texture: &TextureFromSource,
) -> Result<Option<TextureData>, ErrorReported> {
    let (src_texture, src_metadata, loaded_source_path);
    match loaded_texture {
        TextureFromSource::FromAnmFile { texture, metadata, anm_path } => {
            src_texture = Some(texture.clone());
            src_metadata = metadata.clone();
            loaded_source_path = anm_path;
        },
        TextureFromSource::FromImage { image_path } => {
            (src_texture, src_metadata) = self::image_io::load_img_file_for_entry(fs, specs, image_path)?;
            loaded_source_path = image_path;
        },
    }

    if let Some(src_texture) = src_texture {
        validate_and_transcode_texture_for_entry(fs.emitter, specs, entry_path, &src_texture, &src_metadata, loaded_source_path)
            .map(Some)
    } else {
        Ok(None)
    }
}

fn validate_and_transcode_texture_for_entry(
    emitter: &impl Emitter,
    specs: &WorkingEntrySpecs,
    entry_path: &str,
    src_data: &TextureData,
    src_metadata: &TextureMetadata,
    loaded_source_path: &Path,  // .ANM or .PNG path
) -> Result<TextureData, ErrorReported> {
    validate_explicit_img_dimensions(emitter, &specs, entry_path, &src_metadata, loaded_source_path)?;

    let src_format = src_metadata.format;
    let dest_format = specs.img_format.into_option().unwrap();
    let dest_data = if dest_format == src_format {
        // cheaply clone, and allow unrecognized format numbers
        Rc::clone(&src_data.data)
    } else {
        // transcode.
        let src_cformat = ColorFormat::from_format_num(src_format).ok_or_else(|| emitter.emit(error!(
            message("cannot transcode from unknown color format {src_format} (for image '{entry_path}')"),
            // FIXME: we can't have these labels, in case somebody gets a nonsense format from an ANM image source
            //        and then loads an image file from another image source. (dest_format will have no span)
            // primary(dest_format, "transcoding due to this explicit format"),
            note("color format {src_format} appears in '{}'", loaded_source_path.display()),
        )))?;
        let dest_cformat = ColorFormat::from_format_num(dest_format).ok_or_else(|| emitter.emit(error!(
            message("cannot transcode into unknown color format {dest_format} (for image '{entry_path}')"),
            // primary(dest_format, "unknown color format"),
        )))?;

        let data_argb = src_cformat.transcode_to_argb_8888(&src_data.data);
        dest_cformat.transcode_from_argb_8888(&data_argb)
    };

    Ok(dest_data.into())
}

// If a user provided explicit img dimensions in the script AND loaded an image from a source, it is possible
// that these dimensions could disagree with the image that was imported.  Here we check for this.
fn validate_explicit_img_dimensions(
    emitter: &impl Emitter,
    specs: &WorkingEntrySpecs,
    entry_path: &str,
    src_metadata: &TextureMetadata,
    loaded_source_path: &Path,
) -> Result<(), ErrorReported> {
    if specs.has_data.into_option() == Some(HasData::Dummy) {
        // in this case we want to allow the user to arbitrarily override the dimensions from sources
        // without generating any error, since we won't actually be using the loaded texture data
        return Ok(());
    }

    let mut bad_spans = vec![];
    for &(user_dim, texture_dim) in &[
        (specs.img_width, src_metadata.width),
        (specs.img_height, src_metadata.height),
    ] {
        // (we can safely unwrap these options because a texture was loaded, so any missing dimensions
        //  in the script file will have been filled from the texture)
        if let Some(user_dim_value) = user_dim.into_option() {
            if user_dim_value != texture_dim {
                let user_dim_span = match user_dim {
                    SoftOption::Explicit(sp) => sp.span,
                    _ => unreachable!("conflicts are only possible with explicit user dimensions..."),
                };
                bad_spans.push(user_dim_span);
            }
        }
    }

    if !bad_spans.is_empty() {
        let mut diag = error!(
                message(
                    "provided dimensions for '{}' do not match image source: {}x{} in script, {}x{} in image source",
                    entry_path,
                    specs.img_width.into_option().unwrap(),
                    specs.img_height.into_option().unwrap(),
                    src_metadata.width, src_metadata.height,
                ),
                note("image was loaded from '{}'", loaded_source_path.display()),
                note("you can remove these explicit dimensions to infer them from the image source"),
                note("you can add another image source to override this image"),
                note("you can use `has_image: \"dummy\"` to ignore the image in the source and generate dummy data"),
            );
        for span in bad_spans {
            diag.primary(span, format!(""));
        }
        return Err(emitter.emit(diag));
    }

    Ok(())
}

fn generate_texture_dummy_data(
    emitter: &impl Emitter,
    specs: &WorkingEntrySpecs,
    entry_path: &str,
    has_data_span: Span,
) -> Result<TextureData, ErrorReported> {
    for &(dim, name) in &[
        (specs.img_width, "img_width"),
        (specs.img_height, "img_height"),
    ] {
        if dim.into_option().is_none() {
            return Err(emitter.emit(error!(
                message("missing required field '{name}' (for image '{entry_path}')"),
                primary(has_data_span, "requires setting '{name}''"),
                note("you can use '-i ANM_FILE' or '-i path/to/patchdir' to copy the image dimensions from an image source"),
            )));
        }
    }
    let width = specs.img_width.into_option().expect("just checked above!");
    let height = specs.img_height.into_option().expect("just checked above!");
    let format_num = specs.img_format.into_option().expect("should be defaulted");
    let format = ColorFormat::from_format_num(format_num).ok_or_else(|| emitter.emit(error!(
        message("unknown color format {format_num} (for image '{entry_path}')"),
        // FIXME: can't have this label because somebody could put 'has_data: "dummy"' and then import
        //        an ANM file that uses a weird color format number.
        // primary(format, "unknown color format"),
        note(
            "has_data: \"dummy\" requires one of the following formats: {}",
            ColorFormat::get_all().into_iter().map(|format| format.const_name())
                .collect::<Vec<_>>().join(", "),
        ),
    )))?;

    let data = format.dummy_fill_color_bytes().repeat((width * height) as usize);
    Ok(data.into())
}


const DEFAULT_COLOR_FORMAT: ColorFormat = ColorFormat::Argb8888;
const DEFAULT_LOW_RES_SCALE: bool = false;
const DEFAULT_HAS_DATA: HasData = HasData::True;

impl Entry {
    fn make_meta(&self, game: Game) -> meta::Fields {
        let version = Version::from_game(game);

        // img_* fields are only present if a texture was present
        let (mut img_format, mut opt_img_width, mut opt_img_height) = (DEFAULT_COLOR_FORMAT as u32, None, None);
        if let Some(texture_metadata) = &self.texture_metadata {
            img_format = texture_metadata.format;
            opt_img_width = Some(texture_metadata.width);
            opt_img_height = Some(texture_metadata.height);
        }
        let has_data = HasData::from(self.texture_metadata.is_some());

        // these are always here
        let EntrySpecs {
            rt_width, rt_height, rt_format, colorkey,
            offset_x, offset_y, memory_priority, low_res_scale,
        } = self.specs;

        // suppress defaults
        let (mut opt_rt_width, mut opt_rt_height) = (Some(rt_width), Some(rt_height));
        for (opt_rt_dim, opt_img_dim) in vec![
            (&mut opt_rt_width, opt_img_width),
            (&mut opt_rt_height, opt_img_height),
        ] {
            if let Some(img_dim) = opt_img_dim {
                *opt_rt_dim = opt_rt_dim.filter(|&x| x != u32::next_power_of_two(img_dim));
            }
        }

        Meta::make_object()
            .field("path", &self.path.value)
            .field_opt("path_2", self.path_2.as_ref().map(|x| &x.value))
            .field_opt("has_data", Some(has_data).filter(|&x| x != DEFAULT_HAS_DATA))
            .field_opt("img_width", opt_img_width)
            .field_opt("img_height", opt_img_height)
            .field_opt("img_format", Some(img_format).filter(|&x| x != DEFAULT_COLOR_FORMAT as u32).map(format_to_meta))
            .field_opt("offset_x", Some(offset_x).filter(|&x| x != 0))
            .field_opt("offset_y", Some(offset_y).filter(|&x| x != 0))
            .field_opt("colorkey", Some(colorkey).filter(|&x| x != 0).map(colorkey_to_meta))
            .field_opt("rt_width", opt_rt_width)
            .field_opt("rt_height", opt_rt_height)
            .field_opt("rt_format", Some(rt_format).filter(|&x| x != img_format).map(format_to_meta))
            .field_opt("memory_priority", Some(memory_priority).filter(|&x| x != default_memory_priority(version)))
            .field_opt("low_res_scale", Some(low_res_scale).filter(|&x| x != DEFAULT_LOW_RES_SCALE))
            .field("sprites", &self.sprites)
            .build_fields()
    }
}

impl WorkingEntry {
    fn from_fields<'a>(fields: &'a Sp<meta::Fields>, emitter: &impl Emitter) -> Result<Self, FromMetaError<'a>> {
        meta::ParseObject::scope(fields, |m| {
            fn make_explicit<T>(opt: Option<Sp<T>>) -> SoftOption<T> {
                match opt {
                    None => SoftOption::Missing,
                    Some(x) => SoftOption::Explicit(x),
                }
            }

            let deprecated_format = m.get_field_and_key::<Sp<u32>>("format")?;
            let deprecated_width = m.get_field_and_key::<Sp<u32>>("width")?;
            let deprecated_height = m.get_field_and_key::<Sp<u32>>("height")?;
            let mut rt_format = make_explicit(m.get_field::<Sp<u32>>("rt_format")?);
            let mut rt_width = make_explicit(m.get_field::<Sp<u32>>("rt_width")?);
            let mut rt_height = make_explicit(m.get_field::<Sp<u32>>("rt_height")?);
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

                    if value.is_missing() {
                        *value = SoftOption::Explicit(deprecated_value);
                    }
                }
            }

            let deprecated_img_format = m.get_field_and_key("thtx_format")?;
            let deprecated_img_width = m.get_field_and_key("thtx_width")?;
            let deprecated_img_height = m.get_field_and_key("thtx_height")?;
            let mut img_format = make_explicit(m.get_field::<Sp<u32>>("img_format")?);
            let mut img_width = make_explicit(m.get_field::<Sp<u32>>("img_width")?);
            let mut img_height = make_explicit(m.get_field::<Sp<u32>>("img_height")?);
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

                    if value.is_missing() {
                        *value = SoftOption::Explicit(deprecated_value);
                    }
                }
            }

            let colorkey = make_explicit(m.get_field("colorkey")?);
            let offset_x = make_explicit(m.get_field("offset_x")?);
            let offset_y = make_explicit(m.get_field("offset_y")?);
            let memory_priority = make_explicit(m.get_field("memory_priority")?);
            let low_res_scale = make_explicit(m.get_field("low_res_scale")?);
            let has_data = make_explicit(m.get_field("has_data")?);
            let path: Sp<String> = m.expect_field("path")?;
            let path_2 = m.get_field("path_2")?;
            let sprites = m.get_field("sprites")?.unwrap_or_default();

            for (field, rt_value) in vec![
                ("height", rt_height),
                ("width", rt_width),
            ] {
                if let SoftOption::Explicit(rt_value) = rt_value {
                    if !rt_value.value.is_power_of_two() && !path.starts_with("@") {
                        emitter.emit(warning!(
                            message("rt_{} = {} should be a power of two", field, rt_value),
                            primary(rt_value, "not a power of two"),
                        )).ignore();
                    }
                }
            }

            let specs = WorkingEntrySpecs {
                rt_width, rt_height, rt_format,
                img_width, img_height, img_format,
                colorkey, offset_x, offset_y,
                memory_priority, has_data, low_res_scale,
            };
            let loaded_texture = None;
            let scripts = Default::default();
            Ok(WorkingEntry { specs, path, path_2, scripts, sprites, loaded_texture })
        })
    }
}

fn format_to_meta(format_num: u32) -> Meta {
    for known_format in ColorFormat::get_all() {
        if format_num == known_format as u32 {
            let ident = ResIdent::new_null(Ident::new_system(known_format.const_name()).unwrap());
            return Meta::Scalar(sp!(ast::Expr::Var(sp!(ast::Var {
                name: ast::VarName::new_non_reg(ident),
                ty_sigil: None,
            }))));
        }
    }
    format_num.to_meta()
}

fn colorkey_to_meta(colorkey: u32) -> impl ToMeta {
    ast::Expr::LitInt { value: colorkey as i32, radix: ast::IntRadix::Hex }
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

/// An embedded image in an ANM entry.
#[derive(Debug, Clone)]
pub struct Texture {
    pub data: TextureData,
    pub meta: TextureMetadata,
}

/// Wrapper around raw texture data bytes to suppress their `Debug` impl.
#[derive(Clone)]
pub struct TextureData {
    /// Raw pixel data, to be interpreted according to [`TextureMetadata`].
    pub data: Rc<Vec<u8>>,
}

impl<T: Into<Rc<Vec<u8>>>> From<T> for TextureData {
    fn from(x: T) -> Self { TextureData { data: x.into() } }
}

/// Metadata describing how to interpret [`TextureData`].
///
/// This is on a separate struct because, in some cases (especially with `has_data: false` or
/// `has_data: "generate"`, or during decompilation), texture metadata may be read from an image
/// source without its corresponding data.
#[derive(Debug, Clone)]
pub struct TextureMetadata {
    pub width: u32,
    pub height: u32,
    pub format: u32,
}

impl fmt::Debug for TextureData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TextureData(_)")
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

    let num_scripts: usize = anm_file.entries.iter().map(|entry| entry.scripts.len()).sum();
    for i in 0..num_scripts {
        ctx.define_enum_const_fresh(auto_script_name(i as _), i as _, auto_enum_names::anm_script());
    }
    for i in all_sprite_ids(anm_file.entries.iter().map(|entry| &entry.sprites)) {
        ctx.define_enum_const_fresh(auto_sprite_name(i as _), i as _, auto_enum_names::anm_sprite());
    }

    let const_proof = crate::passes::evaluate_const_vars::run(ctx)?;
    let mut raiser = llir::Raiser::new(hooks, ctx.emitter, ctx, decompile_options, const_proof)?;

    for entry in &anm_file.entries {
        items.push(sp!(ast::Item::Meta(ast::ItemMeta {
            keyword: sp!(ast::MetaKeyword::Entry),
            fields: sp!(entry.make_meta(game)),
        })));

        entry.scripts.iter().map(|(name, &Script { id, ref instrs })| {
            let code = emitter.chain_with(|f| write!(f, "in script{}", id), |emitter| {
                raiser.raise_instrs_to_sub_ast(emitter, instrs, ctx)
            })?;

            items.push(sp!(ast::Item::Script(ast::ItemScript {
                number: Some(sp!(id)),
                ident: name.clone(),
                code: ast::Block(code),
                keyword: sp!(()),
            })));
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

fn auto_sprite_name(i: u32) -> Ident { ident!("sprite{i}") }
fn auto_script_name(i: u32) -> Ident { ident!("script{i}") }

// =============================================================================

#[derive(Debug, Clone)]
pub enum ImageSource {
    Anm(AnmFile),
    Directory(PathBuf),
}

fn apply_anm_image_source(dest_file: &mut WorkingAnmFile, src_file: AnmFile) -> Result<(), Diagnostic> {
    let mut src_entries_by_path: IndexMap<_, Vec<_>> = IndexMap::new();
    for entry in src_file.entries {
        src_entries_by_path.entry(entry.path.clone()).or_default().push(entry);
    };
    for vec in src_entries_by_path.values_mut() {
        vec.reverse();  // so we can pop them in forwards order
    }

    for dest_entry in &mut dest_file.entries {
        if let Some(src_entry) = src_entries_by_path.get_mut(&dest_entry.path).and_then(|vec| vec.pop()) {
            update_entry_from_anm_image_source(dest_entry, src_entry, src_file.binary_filename.as_deref().unwrap_or("<ANM file>"))?;
        }
    }
    Ok(())
}

fn update_entry_from_anm_image_source(dest_file: &mut WorkingEntry, src_file: Entry, anm_file_path: &str) -> Result<(), Diagnostic> {
    // though it's tedious, we fully unpack the Specs struct so that the compiler doesn't
    // let us forget to update this function when we add a new field.
    let Entry { specs: src_specs, texture_data: src_texture_data, texture_metadata: src_texture_metadata, .. } = src_file;
    let EntrySpecs {
        rt_width: src_rt_width, rt_height: src_rt_height, rt_format: src_rt_format,
        colorkey: src_colorkey, offset_x: src_offset_x, offset_y: src_offset_y,
        memory_priority: src_memory_priority,
        low_res_scale: src_low_res_scale,
    } = src_specs;

    dest_file.specs.has_data.set_soft(HasData::from(src_texture_data.is_some()));
    if let Some(src_texture_metadata) = &src_texture_metadata {
        dest_file.specs.img_width.set_soft(src_texture_metadata.width as u32);
        dest_file.specs.img_height.set_soft(src_texture_metadata.height as u32);
        dest_file.specs.img_format.set_soft(src_texture_metadata.format);
    }
    if let (Some(src_texture_data), Some(src_texture_metadata)) = (src_texture_data, src_texture_metadata) {
        dest_file.loaded_texture = Some(TextureFromSource::FromAnmFile {
            texture: src_texture_data,
            metadata: src_texture_metadata,
            anm_path: anm_file_path.into(),
        });
    }
    dest_file.specs.rt_width.set_soft(src_rt_width);
    dest_file.specs.rt_height.set_soft(src_rt_height);
    dest_file.specs.rt_format.set_soft(src_rt_format);
    dest_file.specs.colorkey.set_soft(src_colorkey);
    dest_file.specs.offset_x.set_soft(src_offset_x);
    dest_file.specs.offset_y.set_soft(src_offset_y);
    dest_file.specs.memory_priority.set_soft(src_memory_priority);
    dest_file.specs.low_res_scale.set_soft(src_low_res_scale);

    Ok(())
}

// =============================================================================

fn compile(
    hooks: &dyn LanguageHooks,
    ast: &ast::ScriptFile,
    ctx: &mut CompilerContext,
) -> Result<WorkingAnmFile, ErrorReported> {
    let mut ast = ast.clone();
    crate::passes::resolution::assign_languages(&mut ast, hooks.language(), ctx)?;

    define_color_format_consts(ctx);

    // an early pass to define global constants for sprite and script names
    let mut extra_type_checks = vec![];
    let script_ids = gather_script_ids(&ast, ctx)?;
    for (index, &(ref script_name, _)) in script_ids.values().enumerate() {
        let const_value: Sp<ast::Expr> = sp!(script_name.span => (index as i32).into());
        ctx.define_enum_const(script_name.clone(), const_value, sp!(auto_enum_names::anm_script()));
    }
    let sprite_ids = gather_sprite_id_exprs(&ast, ctx, &mut extra_type_checks)?;
    for (sprite_name, id_expr) in sprite_ids {
        ctx.define_enum_const(sprite_name, id_expr, sp!(auto_enum_names::anm_sprite()));
    }

    // preprocess
    let ast = {
        let mut ast = ast;
        crate::passes::resolution::resolve_names(&ast, ctx)?;
        crate::passes::type_check::run(&ast, ctx)?;
        crate::passes::type_check::extra_checks(&extra_type_checks, ctx)?;
        crate::passes::validate_difficulty::forbid_difficulty(&ast, ctx)?;
        crate::passes::evaluate_const_vars::run(ctx)?;
        crate::passes::const_simplify::run(&mut ast, ctx)?;
        crate::passes::desugar_blocks::run(&mut ast, ctx, hooks.language())?;
        ast
    };

    // group scripts by entry
    let mut groups = vec![];
    let mut cur_entry = None::<WorkingEntry>;
    let mut cur_group = vec![];
    let mut script_names = vec![];
    for item in &ast.items {
        match &item.value {
            ast::Item::Meta(ast::ItemMeta { keyword: sp_pat!(ast::MetaKeyword::Entry), fields, .. }) => {
                if let Some(prev_entry) = cur_entry.take() {
                    groups.push((prev_entry, cur_group));
                }
                cur_entry = Some(WorkingEntry::from_fields(fields, ctx.emitter).map_err(|e| ctx.emitter.emit(e))?);
                cur_group = vec![];
            },
            &ast::Item::Script(ast::ItemScript { number: _, ref ident, ref code, .. }) => {
                if cur_entry.is_none() { return Err(ctx.emitter.emit(error!(
                    message("orphaned ANM script with no entry"),
                    primary(item, "orphaned script"),
                    note("at least one `entry` must come before scripts in an ANM file"),
                )))}
                cur_group.push((ident, code));
                script_names.push(ident);
            },
            ast::Item::ConstVar(ast::ItemConstVar { .. }) => {},
            ast::Item::Pragma(ast::ItemPragma { .. }) => unreachable!("removed beforehand"),
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
            let script_index = script_ids.get_index_of(&name.value).unwrap();
            let (_, sp_pat![id]) = script_ids[script_index];

            let def_id = None;
            let do_debug_info = true;
            let (instrs, lowering_info) = lowerer.lower_sub(&code.0, def_id, ctx, do_debug_info)?;

            if do_debug_info {
                let lowering_info = lowering_info.unwrap();
                let export_info = debug_info::ScriptExportInfo {
                    exported_as: debug_info::ScriptType::AnmScript { index: script_index },
                    name: Some(name.to_string()),
                    name_span: name.span.into(),
                };
                ctx.script_debug_info.push(debug_info::Script { export_info, lowering_info });
            }

            entry.scripts.insert(sp!(name.span => name.value.clone()), Script { id, instrs });
        }
        entries.push(entry);
        Ok::<_, ErrorReported>(())
    }).collect_with_recovery().unwrap_or_else(|e| errors.set(e));

    lowerer.finish(ctx).unwrap_or_else(|e| errors.set(e));
    errors.into_result(())?;

    Ok(WorkingAnmFile { entries, binary_filename: None })
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
        let ident = Ident::new_system(format.const_name()).unwrap();
        let value = format as u32 as i32;
        ctx.define_enum_const_fresh(ident, value, auto_enum_names::color_format());
    }
}

// (this returns a Vec instead of a Map because there may be multiple sprites with the same Ident)
fn gather_sprite_id_exprs(
    ast: &ast::ScriptFile,
    ctx: &mut CompilerContext,
    extra_type_checks: &mut Vec<crate::passes::type_check::ShallowTypeCheck>,
) -> Result<Vec<(Sp<ResIdent>, Sp<ast::Expr>)>, ErrorReported> {
    let all_entries = ast.items.iter().filter_map(|item| match &item.value {
        ast::Item::Meta(ast::ItemMeta { keyword: sp_pat!(ast::MetaKeyword::Entry), fields, .. }) => Some(fields),
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
            &ast::Item::Script(ast::ItemScript { number, ref ident, .. }) => {
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

fn strip_unnecessary_sprite_ids<'a>(entry_sprites: impl IntoIterator<Item=&'a mut IndexMap<Sp<Ident>, Sprite>>) {
    let mut next_auto_sprite_id = 0;
    for sprites in entry_sprites {
        for sprite in sprites.values_mut() {
            let actual_id = sprite.id.unwrap_or(next_auto_sprite_id);
            if actual_id == next_auto_sprite_id {
                sprite.id = None;
            }
            next_auto_sprite_id = actual_id + 1;
        }
    }
}

fn all_sprite_ids<'a>(entry_sprites: impl IntoIterator<Item=&'a IndexMap<Sp<Ident>, Sprite>>) -> Vec<u32> {
    let mut out = vec![];
    let mut next_auto_sprite_id = 0;
    for sprites in entry_sprites {
        for sprite in sprites.values() {
            let actual_id = sprite.id.unwrap_or(next_auto_sprite_id);
            next_auto_sprite_id = actual_id + 1;
            out.push(actual_id);
        }
    }
    out
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
