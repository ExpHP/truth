use std::path::{Path, PathBuf};

use image::{GenericImage, GenericImageView};

use super::{
    AnmFile, Entry, HasData, TextureData, TextureMetadata, TextureFromSource,
    WorkingAnmFile, WorkingEntry, WorkingEntrySpecs,
};

use crate::io::{Fs};
use crate::pos::Sp;
use crate::diagnostic::Emitter;
use crate::error::{ErrorReported};
use crate::image::{ColorFormat};
use crate::util::get_groups_by;

pub fn apply_directory_image_source(
    fs: &Fs,
    dest: &mut WorkingAnmFile,
    src_directory: &Path,
) -> Result<(), ErrorReported> {
    for entry in dest.entries.iter_mut() {
        update_entry_from_directory_source(fs, entry, src_directory)?;
    }
    Ok(())
}

fn update_entry_from_directory_source(
    _fs: &Fs,
    dest_entry: &mut WorkingEntry,
    src_directory: &Path,
) -> Result<(), ErrorReported> {
    let image_path = src_directory.join(&dest_entry.path.value);
    if !image_path.is_file() {
        return Ok(());
    }

    // (there is, of course, a fairly big race condition where the file could be deleted before this
    //  path is used;  however, we don't want to use it yet, because another directory source might
    //  replace it, and we don't want to generate errors about invalid dimensions in files we don't use)
    dest_entry.loaded_texture = Some(TextureFromSource::FromImage {
        image_path,
    });
    Ok(())
}

pub(in crate::formats::anm) fn load_img_file_for_entry(
    fs: &Fs,
    specs: &mut WorkingEntrySpecs,
    entry_path: &Sp<String>,
    img_path: &PathBuf,
) -> Result<(Option<TextureData>, TextureMetadata), ErrorReported> {
    let emitter = fs.emitter;

    let (src_image, src_dims): (Option<image::DynamicImage>, _);
    match specs.has_data.into_option().expect("defaults should be filled!") {
        HasData::True => {
            let image = image::open(img_path).map_err(|e| emitter.emit(error!(
                message("{}: {}", fs.display_path(img_path), e)
            )))?;
            src_dims = image.dimensions();
            src_image = Some(image);
        },
        HasData::Dummy | HasData::False => {
            // even though there is no need to load the entire image, we may still want its dimensions
            let dims = image::image_dimensions(img_path).map_err(|e| emitter.emit(error!(
                message("{}: {}", fs.display_path(img_path), e)
            )))?;
            src_image = None;
            src_dims = dims;
        },
    }

    maybe_infer_img_dims_from_image_file(fs.emitter, specs, src_dims)?;

    // these should now all be set
    let dest_dims = (specs.img_width.into_option().unwrap(), specs.img_height.into_option().unwrap());
    let offsets = (specs.offset_x.into_option().unwrap(), specs.offset_y.into_option().unwrap());
    if dest_dims.0 + offsets.0 > src_dims.0 || dest_dims.1 + offsets.1 > src_dims.1 {
        use core::fmt::Write;

        let mut message = String::new();
        write!(message, "image file '{}' too small ({}x{})", fs.display_path(img_path), src_dims.0, src_dims.1).unwrap();
        write!(message, " to extract a texture of size {}x{}", dest_dims.0, dest_dims.1).unwrap();
        if offsets != (0, 0) {
            write!(message, " at offset ({}, {})", offsets.0, offsets.1).unwrap();
        }
        return Err(emitter.emit(error!(
            message("{message}"),
            primary(entry_path, "image too small"),
        )));
    }

    // When no offset was ever provided, lint against mismatched `img_` dimensions versus the image file.
    // (i.e. require an offset to be present if we are going to read only a subregion)
    if specs.has_data.into_option() != Some(HasData::Dummy) {
        let first_bad_dim_info = vec![
            ("width", "offset_x", specs.offset_x, dest_dims.0, src_dims.0),
            ("height", "offset_y", specs.offset_y, dest_dims.1, src_dims.1),
        ].into_iter().find(|(_, _, offset, dest_dim, src_dim)| {
            !(offset.is_from_image_source() || offset.is_explicit()) && dest_dim != src_dim
        });

        if let Some((dim_name, offset_name, _, dest_dim, src_dim)) = first_bad_dim_info {
            // NOTE: This is only a warning and not an error, because when decompiling, we are unable
            //       to determine with 100% accuracy all entries that only contain a subregion of an image file,
            //       thus some explicit offsets and dimensions may be missing.
            return Err(emitter.emit(warning!(
                message(
                    "image file '{}' has larger {dim_name} than expected (expected {dest_dim}, got {src_dim})",
                    fs.display_path(img_path),
                ),
                primary(entry_path, "image too large"),
                note(
                    "if you meant to read only a portion of the image file, please specify the offset of the pixels \
                    to begin reading from, e.g. `{offset_name}: 0,`"
                ),
            )));
        }
    }

    // if 'has_data: true`, read the texture
    let texture_data: Option<TextureData> = src_image.map(|src_image| {
        // obtain ARGB bytes
        let src_data_argb = {
            src_image.into_bgra8()
                .sub_image(offsets.0, offsets.1, dest_dims.0, dest_dims.1)
                .to_image().into_raw()
        };
        src_data_argb.into()
    });
    let texture_metadata = TextureMetadata {
        width: dest_dims.0,
        height: dest_dims.1,
        format: ColorFormat::Argb8888 as u32,
    };
    Ok((texture_data, texture_metadata))
}

fn maybe_infer_img_dims_from_image_file(
    emitter: &impl Emitter,
    specs: &mut WorkingEntrySpecs,
    src_dimensions: (u32, u32),
) -> Result<(), ErrorReported> {
    for (dest_dim_name, offset_name, dest_dim, src_dim, offset) in vec![
        ("img_width", "offset_x", &mut specs.img_width, src_dimensions.0, specs.offset_x),
        ("img_height", "offset_y", &mut specs.img_height, src_dimensions.1, specs.offset_y),
    ] {
        if dest_dim.is_missing() {
            if let Some(offset) = offset.as_explicit() {
                // TODO: in the future this will be an unconditional error
                if offset.value > &src_dim {
                    let inferred_value = src_dim - offset.value;
                    emitter.emit(warning!(
                        message("{offset_name} requires setting {dest_dim_name} when reading from an image file"),
                        primary(offset, "requires setting {dest_dim_name}"),
                        note("for backwards compatibility, a value of {inferred_value} has been inferred (reading to end of image), \
                        but this will become a hard error in the future."),
                    )).ignore();
                    dest_dim.set_softly_from_image_source(inferred_value);

                } else {
                    return Err(emitter.emit(error!(
                        message("{offset_name} requires setting {dest_dim_name} when reading from an image file"),
                        primary(offset, "requires setting {dest_dim_name}"),
                    )));
                }

            } else {
                // If dest_dim is missing then we don't have an ANM source; the offset must be zero.
                assert_eq!(offset.into_option(), Some(0));
                // All preconditions have been met to infer the texture dimensions from the image file.
                dest_dim.set_softly_from_image_source(src_dim);
            }
        }
    }
    Ok(())
}

// =============================================================================

/// Implementation of `truanm -x`.
pub fn extract(
    fs: &Fs<'_>,
    anms: &[AnmFile],
    out_path: &Path,
    conflict_debug_dir: Option<&Path>,
) -> Result<(), ErrorReported> {
    // call this now to make sure ancestors of out_path don't get implicitly created when
    // we use create_dir_all later
    fs.ensure_dir(out_path)?;

    let canonical_out_path = fs.canonicalize(out_path).map_err(|e| fs.emitter.emit(e))?;

    // Gather entries with textures we can extract.
    let mut all_entries = vec![];
    for anm in anms {
        let src_anm_path_display = anm.binary_filename.as_deref().unwrap_or("<unknown>");

        for (entry_index, entry) in anm.entries.iter().enumerate() {
            if let Some(texture_data) = &entry.texture_data {
                let texture_metadata = entry.texture_metadata.as_ref().expect("texture_data implies texture_metadata!");
                let rectangle = Rectangle {
                    start: [entry.specs.offset_x, entry.specs.offset_y],
                    size: [texture_metadata.width, texture_metadata.height],
                };

                let format = texture_metadata.format;
                if let Some(color_format) = ColorFormat::from_format_num(format) {
                    all_entries.push(EntryForExtraction {
                        entry, texture_data, rectangle,
                        color_format, src_anm_path_display, entry_index,
                    });
                } else {
                    fs.emitter.emit(warning!(
                        "{src_anm_path_display}: ignoring entry {entry_index}: \
                        cannot transcode from unknown color format {format}"
                    )).ignore();
                };
            }
        }
    }

    // An image file may come from multiple entries, even across separate ANM files.
    // Do all entries for a given image at a time.
    let grouped_by_path = get_groups_by(all_entries.into_iter(), |entry| entry.entry.path.clone());
    let mut mismatch_tracker = MismatchedPixelTracker::new(conflict_debug_dir);
    for (path, entries) in &grouped_by_path {
        if entries.is_empty() {
            return Ok(());
        }

        let full_path = join_with_tarbomb_prevention(fs, &canonical_out_path, path)?;
        let display_path = fs.display_path(&full_path);

        if let Some(parent) = full_path.parent() {
            fs.create_dir_all(&parent)?;
        }

        let image = produce_image_from_entries(entries, Some(&mut mismatch_tracker))?;
        image.save(full_path).map_err(|e| {
            fs.emitter.emit(error!("while writing '{}': {}", display_path, e))
        })?;

        println!("exported '{}'", display_path);
    }
    mismatch_tracker.finish(fs)?;

    Ok(())
}

fn join_with_tarbomb_prevention(fs: &Fs<'_>, a: &Path, b: &impl AsRef<Path>) -> Result<PathBuf, ErrorReported> {
    let full_path = a.join(b);
    let full_path = canonicalize_part_of_path_that_exists(full_path.as_ref()).map_err(|e| {
        fs.emitter.emit(error!("while resolving '{}': {}", fs.display_path(&full_path), e))
    })?;
    if full_path.strip_prefix(&a).is_err() {
        let display_path = fs.display_path(&full_path);
        return Err(fs.emitter.emit(error!(
            message("skipping '{}': outside of destination directory", display_path),
        )));
    }
    Ok(full_path)
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

pub(super) type BgraImage<V=Vec<u8>> = image::ImageBuffer<image::Bgra<u8>, V>;

#[derive(Copy, Clone)]
struct Rectangle {
    start: [u32; 2],
    size: [u32; 2],
}

impl Rectangle {
    fn end(&self) -> [u32; 2] {
        [self.start[0] + self.size[0], self.start[1] + self.size[1]]
    }

    fn intersection(&self, other: &Rectangle) -> Option<Rectangle> {
        let left = u32::max(self.start[0], other.start[0]);
        let right = u32::min(self.start[0] + self.size[0], other.start[0] + other.size[0]);
        let top = u32::max(self.start[1], other.start[1]);
        let bottom = u32::min(self.start[1] + self.size[1], other.start[1] + other.size[1]);
        if left < right && top < bottom {
            Some(Rectangle {
                start: [left, top],
                size: [right - left, bottom - top],
            })
        } else {
            None
        }
    }
}

#[derive(Clone)]
struct EntryForExtraction<'a> {
    entry: &'a Entry,
    // some parts of the Entry, without Options or with better types to make them easier to work with
    texture_data: &'a TextureData,
    rectangle: Rectangle,
    color_format: ColorFormat,
    // where it came from
    src_anm_path_display: &'a str,
    entry_index: usize,
}

/// Function to produce a single image, given all of the entries that contain regions of the image.
fn produce_image_from_entries<'a>(
    entries: &'a [EntryForExtraction<'a>],
    // This is `None` when outputting the actual conflicting images for a mismatch.
    mut mismatch_tracker: Option<&mut MismatchedPixelTracker<'a>>,
) -> Result<image::RgbaImage, ErrorReported> {
    use image::buffer::ConvertBuffer;

    // Extract entries with max color depth last (giving their pixels highest priority),
    // because sometimes the same image is saved in both ARGB 4444 and ARGB 8888 entries.
    let mut entries = entries.iter().collect::<Vec<_>>();
    entries.sort_by_key(|entry| entry.color_format.is_full_color());

    // Make an output image large enough to contain every texture's data.
    let mut output_width = 0;
    let mut output_height = 0;
    for &EntryForExtraction { rectangle, .. } in &entries {
        output_width = u32::max(output_width, rectangle.end()[0]);
        output_height = u32::max(output_height, rectangle.end()[1]);
    }

    let output_init_argb = vec![0xFF; 4 * output_width as usize * output_height as usize];
    let mut output_image = BgraImage::from_raw(output_width, output_height, output_init_argb).expect("size error?!");

    if let Some(mismatch_tracker) = mismatch_tracker.as_deref_mut() {
        mismatch_tracker.begin_image_path(&entries[0].entry.path);
    }
    for entry@&EntryForExtraction { rectangle, texture_data, color_format, .. } in &entries {
        let texture_argb = color_format.transcode_to_argb_8888(&texture_data.data);
        let texture_image = BgraImage::from_raw(rectangle.size[0], rectangle.size[1], &texture_argb[..]).expect("size error?!");
        if let Some(mismatch_tracker) = mismatch_tracker.as_deref_mut() {
            mismatch_tracker.visit_entry(entry, &output_image, &texture_image);
        }

        rectangle_subimage_mut(&mut output_image, &rectangle)
            .copy_from(&texture_image, 0, 0)
            .expect("region should definitely be large enough");
    }
    if let Some(mismatch_tracker) = mismatch_tracker {
        mismatch_tracker.finish_image();
    }

    Ok(output_image.convert())
}

/// Helper for the diagnostic on overlapping, mismatched pixels between multiple entries during image extraction.
#[derive(Default)]
struct MismatchedPixelTracker<'a> {
    prior_entries_for_current_image: Vec<&'a EntryForExtraction<'a>>,
    current_image_path: Option<String>,
    conflicts: Vec<(&'a EntryForExtraction<'a>, &'a EntryForExtraction<'a>, Rectangle)>,
    conflict_debug_dir: Option<&'a Path>,
}

impl<'a> MismatchedPixelTracker<'a> {
    fn new(conflict_debug_dir: Option<&'a Path>) -> Self {
        MismatchedPixelTracker {
            current_image_path: None,
            prior_entries_for_current_image: vec![],
            conflicts: vec![],
            conflict_debug_dir,
        }
    }

    fn begin_image_path(&mut self, path: &str) {
        assert!(self.current_image_path.is_none());
        self.current_image_path = Some(path.to_owned());
    }

    fn finish_image(&mut self) {
        assert!(self.current_image_path.is_some());
        self.current_image_path = None;
        self.prior_entries_for_current_image.clear();
    }

    fn visit_entry(
        &mut self,
        entry: &'a EntryForExtraction<'a>,
        current_output: &BgraImage,
        texture_image: &BgraImage<&[u8]>,
    ) {
        assert_eq!(&entry.entry.path[..], self.current_image_path.as_ref().expect("visit_entry called before setting image path"));

        // For now, just check the regions that intersect with previous images.
        //
        // Iterate in reverse order so that our warnings will name the thing that was most recently written.
        for prior_entry in self.prior_entries_for_current_image.iter().rev() {
            if entry.color_format.is_full_color() && !prior_entry.color_format.is_full_color() {
                continue;  // allow any mismatches as the new texture is superior
            }

            if let Some(overlap_rect_in_output) = prior_entry.rectangle.intersection(&entry.rectangle) {
                let overlap_rect_in_entry = Rectangle {
                    start: [
                        overlap_rect_in_output.start[0] - entry.rectangle.start[0],
                        overlap_rect_in_output.start[1] - entry.rectangle.start[1],
                    ],
                    size: overlap_rect_in_output.size
                };
                let output_region = rectangle_subimage(current_output, &overlap_rect_in_output);
                let output_pixels = output_region.pixels().map(|(_, _, pixel)| pixel);
                let entry_region = rectangle_subimage(texture_image, &overlap_rect_in_entry);
                let entry_pixels = entry_region.pixels().map(|(_, _, pixel)| pixel);
                if output_pixels.ne(entry_pixels) {
                    self.conflicts.push((prior_entry, entry, overlap_rect_in_output));
                    break;
                }
            }
        }
        self.prior_entries_for_current_image.push(entry);
    }

    fn finish(mut self, fs: &Fs) -> Result<(), ErrorReported> {
        let conflicts = self.conflicts.drain(..).collect::<Vec<_>>();
        for (conflict_index, (entry_1, entry_2, rect)) in conflicts.into_iter().enumerate() {
            let [x1, y1] = rect.start;
            let [x2, y2] = rect.end();

            let mut diagnostic = warning!(
                message("conflicting data for image '{}' region ({x1}, {y1})..({x2}, {y2})", entry_1.entry.path),
                note("between entry {:02} in '{}'", entry_1.entry_index, entry_1.src_anm_path_display),
                note("    and entry {:02} in '{}'", entry_2.entry_index, entry_2.src_anm_path_display),
            );

            if let Some(conflict_debug_dir) = self.conflict_debug_dir {
                let written_path = self.write_conflicting_images(fs, (entry_1, entry_2), conflict_debug_dir, conflict_index)?;
                diagnostic.note(format!("conflicting images written to '{}'", fs.display_path(&written_path)));
            }

            fs.emitter.emit(diagnostic).ignore();
        }
        Ok(())
    }

    fn write_conflicting_images(
        &mut self,
        fs: &Fs,
        entries: (&EntryForExtraction<'a>, &EntryForExtraction<'a>),
        conflict_debug_dir: &Path,
        conflict_index: usize,
    ) -> Result<PathBuf, ErrorReported>  {
        fs.ensure_dir(conflict_debug_dir)?;
        let subdir = conflict_debug_dir.join(format!("{conflict_index:02}"));
        fs.ensure_dir(&subdir)?;

        for (filename, entry) in vec![("a.png", entries.0), ("b.png", entries.1)] {
            let image = produce_image_from_entries(&[entry.clone()], None)?;

            let full_path = subdir.join(filename);
            let display_path = fs.display_path(&full_path);
            image.save(full_path).map_err(|e| {
                fs.emitter.emit(error!("while writing '{display_path}': {e}"))
            })?;
        }

        Ok(subdir)
    }
}

fn rectangle_subimage_mut<'a, I: image::GenericImage>(
    image: &'a mut I,
    rect: &Rectangle,
) -> image::SubImage<&'a mut I::InnerImage> {
    image.sub_image(rect.start[0], rect.start[1], rect.size[0], rect.size[1])
}

fn rectangle_subimage<'a, I: image::GenericImageView>(
    image: &'a I,
    rect: &Rectangle,
) -> image::SubImage<&'a I::InnerImageView> {
    image.view(rect.start[0], rect.start[1], rect.size[0], rect.size[1])
}
