use std::path::{Path, PathBuf};

use super::{
    AnmFile, Entry, HasData, TextureData, TextureMetadata, TextureFromSource,
    WorkingAnmFile, WorkingEntry, WorkingEntrySpecs,
};

use crate::io::{Fs};
use crate::error::{GatherErrorIteratorExt, ErrorReported};
use crate::image::ColorFormat;

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
    use image::{GenericImage, GenericImageView};

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
    anm: &AnmFile,
    out_path: &Path,
) -> Result<(), ErrorReported> {
    // call this now to make sure ancestors of out_path don't get implicitly created when
    // we use create_dir_all later
    fs.ensure_dir(out_path)?;

    let canonical_out_path = fs.canonicalize(out_path).map_err(|e| fs.emitter.emit(e))?;

    anm.entries.iter().map(|entry| {
        if entry.texture_data.is_none() {
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

pub(super) type BgraImage<V=Vec<u8>> = image::ImageBuffer<image::Bgra<u8>, V>;

fn produce_image_from_entry(entry: &Entry) -> Result<image::RgbaImage, String> {
    use image::{GenericImage, buffer::ConvertBuffer};

    let texture_data = entry.texture_data.as_ref().expect("produce_image_from_entry called without texture!");
    let texture_metadata = entry.texture_metadata.as_ref().expect("produce_image_from_entry called without texture!");
    let content_width = texture_metadata.width as u32;
    let content_height = texture_metadata.height as u32;
    let format = texture_metadata.format;
    let cformat = ColorFormat::from_format_num(format).ok_or_else(|| {
        format!("cannot transcode from unknown color format {}", format)
    })?;

    let content_argb = cformat.transcode_to_argb_8888(&texture_data.data);
    let content = BgraImage::from_raw(content_width, content_height, &content_argb[..]).expect("size error?!");

    let offset_x = entry.specs.offset_x;
    let offset_y = entry.specs.offset_y;
    let output_width = content_width + offset_x;
    let output_height = content_height + offset_y;
    let output_init_argb = vec![0xFF; 4 * output_width as usize * output_height as usize];
    let mut output = BgraImage::from_raw(output_width, output_height, output_init_argb).expect("size error?!");

    output.sub_image(offset_x, offset_y, content_width, content_height)
        .copy_from(&content, 0, 0)
        .expect("region should definitely be large enough");

    Ok(output.convert())
}
