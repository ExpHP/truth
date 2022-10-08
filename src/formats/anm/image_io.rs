use std::path::{Path, PathBuf};

use indexmap::IndexMap;
use image::{GenericImage, GenericImageView};
use crate::diagnostic::Emitter;

use super::{
    AnmFile, Entry, HasData, TextureData, TextureMetadata, TextureFromSource,
    WorkingAnmFile, WorkingEntry, WorkingEntrySpecs,
};

use crate::io::{Fs};
use crate::error::{ErrorReported};
use crate::image::{ColorFormat};

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
    img_path: &PathBuf,
) -> Result<(Option<TextureData>, TextureMetadata), ErrorReported> {
    let emitter = fs.emitter;

    let (src_image, src_dimensions): (Option<image::DynamicImage>, _);
    match specs.has_data.into_option().expect("defaults should be filled!") {
        HasData::True => {
            let image = image::open(img_path).map_err(|e| emitter.emit(error!(
                message("{}: {}", fs.display_path(img_path), e)
            )))?;
            src_dimensions = image.dimensions();
            src_image = Some(image);
        },
        HasData::Dummy | HasData::False => {
            // even though there is no need to load the entire image, we may still want its dimensions
            let dims = image::image_dimensions(img_path).map_err(|e| emitter.emit(error!(
                message("{}: {}", fs.display_path(img_path), e)
            )))?;
            src_image = None;
            src_dimensions = dims;
        },
    }

    // these must be well-defined for us to continue, so fill in defaults early
    let offsets = (
        specs.offset_x.into_option().unwrap_or(0),
        specs.offset_y.into_option().unwrap_or(0),
    );

    // use image dimensions to fill in any missing `img_*` fields
    // FIXME: This mutation is a bit surprising, but I'm not sure how to work out all of the edge cases
    //        without it.
    for (dest_dim, src_dim, offset) in vec![
        (&mut specs.img_width, src_dimensions.0, offsets.0),
        (&mut specs.img_height, src_dimensions.1, offsets.1),
    ] {
        if src_dim >= offset {
            dest_dim.set_soft(src_dim - offset);
        } else {
            return Err(emitter.emit(error!(
                "{}: image too small ({}x{}) for an offset of ({}, {})",
                fs.display_path(img_path),
                src_dimensions.0, src_dimensions.1,
                offsets.0, offsets.1,
            )))
        }
    }

    // all dest dimensions are set now, but pre-existing ones might not match the image
    let dest_dimensions = (specs.img_width.into_option().unwrap(), specs.img_height.into_option().unwrap());
    let expected_src_dimensions = (dest_dimensions.0 + offsets.0, dest_dimensions.1 + offsets.1);
    if src_dimensions != expected_src_dimensions && specs.has_data.into_option() != Some(HasData::Dummy) {
        return Err(emitter.emit(error!(
            "{}: wrong image dimensions (expected {}x{}, got {}x{})",
            fs.display_path(img_path),
            expected_src_dimensions.0, expected_src_dimensions.1,
            src_dimensions.0, src_dimensions.1,
        )))
    }

    // if 'has_data: true`, read the texture
    let texture_data: Option<TextureData> = src_image.map(|src_image| {
        // obtain ARGB bytes
        let src_data_argb = {
            src_image.into_bgra8()
                .sub_image(offsets.0, offsets.1, dest_dimensions.0, dest_dimensions.1)
                .to_image().into_raw()
        };
        src_data_argb.into()
    });
    let texture_metadata = TextureMetadata {
        width: dest_dimensions.0,
        height: dest_dimensions.1,
        format: ColorFormat::Argb8888 as u32,
    };
    Ok((texture_data, texture_metadata))
}

// =============================================================================

/// Implementation of `truanm -x`.
pub fn extract(
    fs: &Fs<'_>,
    anms: &[AnmFile],
    out_path: &Path,
) -> Result<(), ErrorReported> {
    // call this now to make sure ancestors of out_path don't get implicitly created when
    // we use create_dir_all later
    fs.ensure_dir(out_path)?;

    let canonical_out_path = fs.canonicalize(out_path).map_err(|e| fs.emitter.emit(e))?;

    let all_entries = anms.iter().flat_map(|anm| {
        let src_anm_path_display = anm.binary_filename.as_deref().unwrap_or("<unknown>");
        anm.entries.iter()
            .enumerate()
            .filter(|(_, entry)| entry.texture_data.is_some())
            .map(move |(entry_index, entry)| EntryAndLocation {
                entry, entry_index, src_anm_path_display,
            })
    });

    // An image file may come from multiple entries, even across separate ANM files.
    // Do all entries for a given image at a time.
    let grouped_by_path = get_groups_by(all_entries, |entry| entry.entry.path.clone());
    for (path, entries) in grouped_by_path {
        if entries.is_empty() {
            return Ok(());
        }

        let full_path = join_with_tarbomb_prevention(fs, &canonical_out_path, &path)?;
        let display_path = fs.display_path(&full_path);

        if let Some(parent) = full_path.parent() {
            fs.create_dir_all(&parent)?;
        }

        let image = produce_image_from_entries(&entries, fs.emitter).map_err(|s| {
            fs.emitter.emit(error!("skipping '{}': {}", display_path, s))
        })?;

        image.save(full_path).map_err(|e| {
            fs.emitter.emit(error!("while writing '{}': {}", display_path, e))
        })?;

        println!("exported '{}'", display_path);
    }
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

struct Rectangle {
    start: [u32; 2],
    size: [u32; 2],
}

impl Rectangle {
    fn end(&self) -> [u32; 2] {
        [self.start[0] + self.size[0], self.start[1] + self.size[1]]
    }

    fn from_entry(entry: &Entry) -> Self {
        let texture_meta = entry.texture_metadata.as_ref().expect("produce_image_from_entry called without texture!");
        Rectangle {
            start: [entry.specs.offset_x, entry.specs.offset_y],
            size: [texture_meta.width, texture_meta.height],
        }
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

#[derive(Copy, Clone)]
struct EntryAndLocation<'a> {
    entry: &'a Entry,
    entry_index: usize,
    src_anm_path_display: &'a str,
}

/// Function to produce a single image file, given all of the entries that contain regions of the image.
fn produce_image_from_entries(
    entries: &[EntryAndLocation<'_>],
    emitter: &impl Emitter,
) -> Result<image::RgbaImage, String> {
    use image::buffer::ConvertBuffer;

    let mut output_width = 0;
    let mut output_height = 0;
    for EntryAndLocation { entry, .. } in entries {
        let texture_metadata = entry.texture_metadata.as_ref().expect("produce_image_from_entry called without texture!");
        output_width = u32::max(output_width, entry.specs.offset_x + texture_metadata.width);
        output_height = u32::max(output_height, entry.specs.offset_y + texture_metadata.height);
    }

    let output_init_argb = vec![0xFF; 4 * output_width as usize * output_height as usize];
    let mut output_image = BgraImage::from_raw(output_width, output_height, output_init_argb).expect("size error?!");

    let mut mismatch_tracker = MismatchedPixelTracker::default();
    for &entry_and_location in entries {
        let EntryAndLocation { entry, .. } = entry_and_location;
        let texture_data = entry.texture_data.as_ref().expect("produce_image_from_entry called without texture!");
        let texture_metadata = entry.texture_metadata.as_ref().expect("produce_image_from_entry called without texture!");
        let texture_width = texture_metadata.width;
        let texture_height = texture_metadata.height;
        let format = texture_metadata.format;
        let cformat = ColorFormat::from_format_num(format).ok_or_else(|| {
            format!("cannot transcode from unknown color format {format}")
        })?;

        let texture_argb = cformat.transcode_to_argb_8888(&texture_data.data);
        let texture_image = BgraImage::from_raw(texture_width, texture_height, &texture_argb[..]).expect("size error?!");

        let rect = Rectangle::from_entry(entry);
        mismatch_tracker.visit(entry_and_location, &output_image, &texture_image);

        rectangle_subimage_mut(&mut output_image, &rect)
            .copy_from(&texture_image, 0, 0)
            .expect("region should definitely be large enough");
    }
    mismatch_tracker.finish(emitter);

    Ok(output_image.convert())
}

/// Helper for the diagnostic on overlapping, mismatched pixels between multiple entries during image extraction.
#[derive(Default)]
struct MismatchedPixelTracker<'a> {
    prior_entries: Vec<EntryAndLocation<'a>>,
    conflicts: Vec<(EntryAndLocation<'a>, EntryAndLocation<'a>, Rectangle)>,
}

impl<'a> MismatchedPixelTracker<'a> {
    fn visit(
        &mut self,
        entry: EntryAndLocation<'a>,
        current_output: &BgraImage,
        texture_image: &BgraImage<&[u8]>,
    ) {
        // For now, just check the regions that intersect with previous images.
        //
        // Iterate in reverse order so that our warnings will name the thing that was most recently written.
        let new_rectangle = Rectangle::from_entry(entry.entry);
        for &prior_entry in self.prior_entries.iter().rev() {
            if let Some(intersection) = Rectangle::from_entry(prior_entry.entry).intersection(&new_rectangle) {
                let output_region = rectangle_subimage(current_output, &intersection);
                if output_region.pixels().map(|(_, _, pixel)| pixel).ne(texture_image.pixels().copied()) {
                    self.conflicts.push((prior_entry, entry, intersection));
                    break;
                }
            }
        }
        self.prior_entries.push(entry);
    }

    fn finish(self, emitter: &impl Emitter) {
        for (entry_1, entry_2, rect) in self.conflicts {
            let [x1, y1] = rect.start;
            let [x2, y2] = rect.end();
            emitter.emit(warning!(
                message("conflicting data for image {} region ({x1}, {y1})..({x2}, {y2})", entry_1.entry.path),
                note("provided by entry {} in {}", entry_1.entry_index, entry_1.src_anm_path_display),
                note("provided by entry {} in {}", entry_2.entry_index, entry_2.src_anm_path_display),
            )).ignore();
        }
    }
}

fn rectangle_subimage_mut<'a, I: image::GenericImage>(
    image: &'a mut I,
    rect: &Rectangle,
) -> image::SubImage<&'a mut I::InnerImage> {
    image.sub_image(rect.start[0], rect.start[1], rect.size[0], rect.size[1])
}

fn rectangle_subimage<'a, I: image::GenericImage>(
    image: &'a I,
    rect: &Rectangle,
) -> image::SubImage<&'a I::InnerImageView> {
    image.view(rect.start[0], rect.start[1], rect.size[0], rect.size[1])
}

fn get_groups_by<T, K: Eq + core::hash::Hash>(
    items: impl Iterator<Item=T>,
    mut key_fn: impl FnMut(&T) -> K,
) -> IndexMap<K, Vec<T>> {
    let mut out = IndexMap::<_, Vec<_>>::default();
    for item in items {
        out.entry(key_fn(&item)).or_default().push(item);
    }
    out
}
