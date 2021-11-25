use std::path::{Path, PathBuf};

use super::{AnmFile, Entry, HasData, DEFAULT_HAS_DATA, DEFAULT_COLOR_FORMAT, Texture};

use crate::io::{Fs};
use crate::diagnostic::{Emitter};
use crate::error::{GatherErrorIteratorExt, ErrorReported};
use crate::image::ColorFormat;

pub fn apply_directory_image_source(
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
    let dest_format = *dest_entry.specs.img_format.get_or_insert(sp!(DEFAULT_COLOR_FORMAT as u32));
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

// =============================================================================

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
