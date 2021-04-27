use std::path::Path;
use std::io::Read;

pub use color::ColorFormat;
mod color;

pub fn read_image_dimensions() {

}

pub fn read_png() {
    // For reading and opening files
    use std::path::Path;
    use std::fs::File;
    use std::io::BufWriter;

    let path = Path::new(r"/path/to/image.png");
    let file = File::create(path).unwrap();
    let ref mut w = BufWriter::new(file);

    let mut encoder = png::Encoder::new(w, 2, 1); // Width is 2 pixels and height is 1.
    encoder.set_color(png::ColorType::RGBA);
    encoder.set_depth(png::BitDepth::Eight);
    let mut writer = encoder.write_header().unwrap();

    let data = [255, 0, 0, 255, 0, 0, 0, 255]; // An array containing a RGBA sequence. First pixel is red and second pixel is black.
    writer.write_image_data(&data).unwrap(); // Save
}

pub fn read_png_metadata<R: Read>(mut reader: R) -> Result<png::OutputInfo, png::DecodingError> {
    png::Decoder::new(reader).read_info().map(|x| x.0)
}
