use std::io::Cursor;
use std::rc::Rc;

use crate::io::{BinRead, BinWrite};

const FORMAT_ARGB_8888: u32 = 1;
const FORMAT_ARGB_1555: u32 = 2;
const FORMAT_RGB_565: u32 = 3;
const FORMAT_RGB_888: u32 = 4;
const FORMAT_ARGB_4444: u32 = 5;
const FORMAT_ARGB_8332: u32 = 6;
const FORMAT_GRAY_8: u32 = 7;
const FORMAT_RGB_332: u32 = 8;

#[repr(u32)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ColorFormat {
    Argb8888 = FORMAT_ARGB_8888,
    Argb1555 = FORMAT_ARGB_1555,
    Rgb565 = FORMAT_RGB_565,
    Rgb888 = FORMAT_RGB_888,
    Argb4444 = FORMAT_ARGB_4444,
    Argb8332 = FORMAT_ARGB_8332,
    Gray8 = FORMAT_GRAY_8,
    Rgb332 = FORMAT_RGB_332,
}

impl ColorFormat {
    pub fn from_format_num(num: u32) -> Option<Self> {
        match num {
            FORMAT_ARGB_8888 => Some(Self::Argb8888),
            FORMAT_ARGB_1555 => Some(Self::Argb1555),
            FORMAT_RGB_565 => Some(Self::Rgb565),
            FORMAT_RGB_888 => Some(Self::Rgb888),
            FORMAT_ARGB_4444 => Some(Self::Argb4444),
            FORMAT_ARGB_8332 => Some(Self::Argb8332),
            FORMAT_GRAY_8 => Some(Self::Gray8),
            FORMAT_RGB_332 => Some(Self::Rgb332),
            _ => None,
        }
    }

    pub fn get_all() -> Vec<ColorFormat> { vec![
        ColorFormat::Argb8888,
        ColorFormat::Argb1555,
        ColorFormat::Rgb565,
        ColorFormat::Rgb888,
        ColorFormat::Argb4444,
        ColorFormat::Argb8332,
        ColorFormat::Gray8,
        ColorFormat::Rgb332,
    ]}

    pub fn const_name(&self) -> &'static str {
        match self {
            ColorFormat::Argb8888 => "FORMAT_ARGB_8888",
            ColorFormat::Argb1555 => "FORMAT_ARGB_1555",
            ColorFormat::Rgb565 => "FORMAT_RGB_565",
            ColorFormat::Rgb888 => "FORMAT_RGB_888",
            ColorFormat::Argb4444 => "FORMAT_ARGB_4444",
            ColorFormat::Argb8332 => "FORMAT_ARGB_8332",
            ColorFormat::Gray8 => "FORMAT_GRAY_8",
            ColorFormat::Rgb332 => "FORMAT_RGB_332",
        }
    }

    pub fn bytes_per_pixel(&self) -> usize {
        match self {
            ColorFormat::Argb8888 => Argb8888::BYTES_PER_PIXEL,
            ColorFormat::Argb1555 => Argb1555::BYTES_PER_PIXEL,
            ColorFormat::Rgb565 => Rgb565::BYTES_PER_PIXEL,
            ColorFormat::Rgb888 => Rgb888::BYTES_PER_PIXEL,
            ColorFormat::Argb4444 => Argb4444::BYTES_PER_PIXEL,
            ColorFormat::Argb8332 => Argb8332::BYTES_PER_PIXEL,
            ColorFormat::Gray8 => Gray8::BYTES_PER_PIXEL,
            ColorFormat::Rgb332 => Rgb332::BYTES_PER_PIXEL,
        }
    }

    pub fn transcode_to_argb_8888(&self, bytes: &Rc<Vec<u8>>) -> Rc<Vec<u8>> {
        match self {
            ColorFormat::Argb8888 => Rc::clone(bytes),
            ColorFormat::Argb1555 => Rc::new(Argb8888::encode(&Argb1555::decode(bytes))),
            ColorFormat::Rgb565 => Rc::new(Argb8888::encode(&Rgb565::decode(bytes))),
            ColorFormat::Rgb888 => Rc::new(Argb8888::encode(&Rgb888::decode(bytes))),
            ColorFormat::Argb4444 => Rc::new(Argb8888::encode(&Argb4444::decode(bytes))),
            ColorFormat::Argb8332 => Rc::new(Argb8888::encode(&Argb8332::decode(bytes))),
            ColorFormat::Gray8 => Rc::new(Argb8888::encode(&Gray8::decode(bytes))),
            ColorFormat::Rgb332 => Rc::new(Rgb332::encode(&Rgb332::decode(bytes))),
        }
    }

    pub fn transcode_from_argb_8888(&self, bytes: &Rc<Vec<u8>>) -> Rc<Vec<u8>> {
        match self {
            ColorFormat::Argb8888 => Rc::clone(bytes),
            ColorFormat::Argb1555 => Rc::new(Argb1555::encode(&Argb8888::decode(bytes))),
            ColorFormat::Rgb565 => Rc::new(Rgb565::encode(&Argb8888::decode(bytes))),
            ColorFormat::Rgb888 => Rc::new(Rgb888::encode(&Argb8888::decode(bytes))),
            ColorFormat::Argb4444 => Rc::new(Argb4444::encode(&Argb8888::decode(bytes))),
            ColorFormat::Argb8332 => Rc::new(Argb8332::encode(&Argb8888::decode(bytes))),
            ColorFormat::Gray8 => Rc::new(Gray8::encode(&Argb8888::decode(bytes))),
            ColorFormat::Rgb332 => Rc::new(Rgb332::encode(&Argb8888::decode(bytes))),
        }
    }

    pub fn dummy_fill_color_bytes(&self) -> &'static [u8] {
        match self {
            // Slightly transparent magenta where possible
            // (if fully opaque, thcrap would overlay loaded images instead of overwriting the alpha channel)
            ColorFormat::Argb8888 => &[0xFF, 0xFF, 0x00, 0xFE],
            ColorFormat::Argb1555 => &[0b000_11111, 0b1_11111_00],
            ColorFormat::Rgb565 => &[0b000_11111, 0b11111_000],
            ColorFormat::Rgb888 => &[0xFF, 0x00, 0xFF],
            ColorFormat::Argb4444 => &[0x0F, 0xEF],
            ColorFormat::Argb8332 => &[0b111_000_11, 0xFE],
            ColorFormat::Gray8 => &[0x80],
            ColorFormat::Rgb332 => &[0b111_000_11],
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Components { red: u8, green: u8, blue: u8, alpha: u8 }

#[cfg(test)]
impl Components {
    pub const BLACK: Components = Components { red: 0, green: 0, blue: 0, alpha: 0xFF };
    pub const WHITE: Components = Components { red: 0xFF, green: 0xFF, blue: 0xFF, alpha: 0xFF };
}

/// Format which is the little-endian encoding of a 32-bit integer `0xAARRGGBB`.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Argb8888(u32);

/// Format which is the little-endian encoding of a 16-bit integer `0bA_RRRRR_GGGGG_BBBBB`.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Argb1555(u16);

/// Format which is the little-endian encoding of a 16-bit integer `0bRRRRR_GGGGGG_BBBBB`.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Rgb565(u16);

/// Format which is the little-endian encoding of a 24-bit integer `0xRGB`.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Rgb888(u32);

/// Format which is the little-endian encoding of a 16-bit integer `0xARGB`.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Argb4444(u16);

/// Format which is the little-endian encoding of a 16-bit integer `0bAAAAAAAA_RRR_GGG_BB`.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Argb8332(u16);

/// Format which is a single-byte luminosity channel.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Gray8(u8);

/// Format which is single byte encoding of a 8-bit integer `0bRRR_GGG_BB`.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Rgb332(u8);


trait ColorBytes: Sized
where
    Self: From<Components>,
    Components: From<Self>,
{
    const BYTES_PER_PIXEL: usize;
    fn read_color_bytes<R: BinRead>(r: R) -> Result<Self, R::Err> ;
    fn write_color_bytes<W: BinWrite>(&self, w: W) -> Result<(), W::Err>;

    fn decode(bytes: &[u8]) -> Vec<Components> {
        assert_eq!(bytes.len() % Self::BYTES_PER_PIXEL, 0);

        let mut reader = Cursor::new(bytes);
        (0..bytes.len() / Self::BYTES_PER_PIXEL)
            .map(|_| Components::from(Self::read_color_bytes(&mut reader).unwrap()))
            .collect()
    }

    fn encode(colors: &[Components]) -> Vec<u8> {
        let mut out = Cursor::new(Vec::with_capacity(colors.len() * Self::BYTES_PER_PIXEL));
        for &components in colors {
            Self::from(components).write_color_bytes(&mut out).unwrap()
        }
        out.into_inner()
    }
}

impl From<Argb8888> for Components {
    fn from(color: Argb8888) -> Components {
        let [alpha, red, green, blue] = color.0.to_be_bytes();
        Components { blue, green, red, alpha }
    }
}

impl From<Components> for Argb8888 {
    fn from(components: Components) -> Self {
        let Components { blue, green, red, alpha } = components;
        Argb8888(u32::from_be_bytes([alpha, red, green, blue]))
    }
}

impl ColorBytes for Argb8888 {
    const BYTES_PER_PIXEL: usize = 4;

    fn read_color_bytes<R: BinRead>(mut r: R) -> Result<Self, R::Err> { r.read_u32().map(Argb8888) }
    fn write_color_bytes<W: BinWrite>(&self, mut w: W) -> Result<(), W::Err> { w.write_u32(self.0) }
}

impl From<Argb1555> for Components {
    fn from(color: Argb1555) -> Components {
        let blue = (color.0 & 0x1F) as u8;
        let green = ((color.0 >> 5) & 0x1F) as u8;
        let red = ((color.0 >> 10) & 0x1F) as u8;
        let alpha = ((color.0 >> 15) & 1) as u8;
        Components {
            blue: change_bit_depth::<5, 8>(blue),
            green: change_bit_depth::<5, 8>(green),
            red: change_bit_depth::<5, 8>(red),
            alpha: change_bit_depth::<1, 8>(alpha),
        }
    }
}

impl From<Components> for Argb1555 {
    fn from(components: Components) -> Self {
        let blue = (components.blue >> 3) as u16;
        let green = (components.green >> 3) as u16;
        let red = (components.red >> 3) as u16;
        let alpha = (components.alpha >> 7) as u16;

        Argb1555((alpha << 15) + (red << 10) + (green << 5) + blue)
    }
}

impl ColorBytes for Argb1555 {
    const BYTES_PER_PIXEL: usize = 2;

    fn read_color_bytes<R: BinRead>(mut r: R) -> Result<Self, R::Err> { r.read_u16().map(Argb1555) }
    fn write_color_bytes<W: BinWrite>(&self, mut w: W) -> Result<(), W::Err> { w.write_u16(self.0) }
}

impl From<Rgb565> for Components {
    fn from(color: Rgb565) -> Components {
        let blue = (color.0 & 0x1F) as u8;
        let green = ((color.0 >> 5) & 0x3F) as u8;
        let red = ((color.0 >> 11) & 0x1F) as u8;
        Components {
            blue: change_bit_depth::<5, 8>(blue),
            green: change_bit_depth::<6, 8>(green),
            red: change_bit_depth::<5, 8>(red),
            alpha: 0xFF,
        }
    }
}

impl From<Components> for Rgb565 {
    fn from(components: Components) -> Self {
        let blue = (components.blue >> 3) as u16;
        let green = (components.green >> 2) as u16;
        let red = (components.red >> 3) as u16;

        Rgb565((red << 11) + (green << 5) + blue)
    }
}

impl ColorBytes for Rgb565 {
    const BYTES_PER_PIXEL: usize = 2;

    fn read_color_bytes<R: BinRead>(mut r: R) -> Result<Self, R::Err> { r.read_u16().map(Rgb565) }
    fn write_color_bytes<W: BinWrite>(&self, mut w: W) -> Result<(), W::Err> { w.write_u16(self.0) }
}

impl From<Rgb888> for Components {
    fn from(color: Rgb888) -> Components {
        let blue = (color.0 & 0xFF) as u8;
        let green = ((color.0 >> 8) & 0xFF) as u8;
        let red = ((color.0 >> 16) & 0xFF) as u8;
        Components {
            blue,
            green,
            red,
            alpha: 0xFF
        }
    }
}

impl From<Components> for Rgb888 {
    fn from(components: Components) -> Self {
        let blue = components.blue as u32;
        let green = components.green as u32;
        let red = components.red as u32;

        Rgb888((red << 16) + (green << 8) + blue)
    }
}

impl ColorBytes for Rgb888 {
    const BYTES_PER_PIXEL: usize = 3;

    fn read_color_bytes<R: BinRead>(mut r: R) -> Result<Self, R::Err> {
        let mut color = r.read_u8()? as u32;
        color |= (r.read_u8()? as u32) << 8;
        color |= (r.read_u8()? as u32) << 16;
        Ok(Rgb888(color))
    }
    fn write_color_bytes<W: BinWrite>(&self, mut w: W) -> Result<(), W::Err> {
        let blue = (self.0 & 0xFF) as u8;
        let green = ((self.0 >> 8) & 0xFF) as u8;
        let red = ((self.0 >> 16) & 0xFF) as u8;
        w.write_u8(blue)?;
        w.write_u8(green)?;
        w.write_u8(red)?;
        Ok(())
    }
}

impl From<Argb4444> for Components {
    fn from(color: Argb4444) -> Components {
        let blue = (color.0 & 0xF) as u8;
        let green = ((color.0 >> 4) & 0xF) as u8;
        let red = ((color.0 >> 8) & 0xF) as u8;
        let alpha = (color.0 >> 12) as u8;
        Components {
            blue: change_bit_depth::<4, 8>(blue),
            green: change_bit_depth::<4, 8>(green),
            red: change_bit_depth::<4, 8>(red),
            alpha: change_bit_depth::<4, 8>(alpha),
        }
    }
}

impl From<Components> for Argb4444 {
    fn from(components: Components) -> Self {
        let blue = (components.blue >> 4) as u16;
        let green = (components.green >> 4) as u16;
        let red = (components.red >> 4) as u16;
        let alpha = (components.alpha >> 4) as u16;

        Argb4444(((alpha * 16 + red) * 16 + green) * 16 + blue)
    }
}

impl ColorBytes for Argb4444 {
    const BYTES_PER_PIXEL: usize = 2;

    fn read_color_bytes<R: BinRead>(mut r: R) -> Result<Self, R::Err> { r.read_u16().map(Argb4444) }
    fn write_color_bytes<W: BinWrite>(&self, mut w: W) -> Result<(), W::Err> { w.write_u16(self.0) }
}

impl From<Argb8332> for Components {
    fn from(color: Argb8332) -> Components {
        let blue = (color.0 & 0x3) as u8;
        let green = ((color.0 >> 2) & 0x7) as u8;
        let red = ((color.0 >> 5) & 0x7) as u8;
        let alpha = ((color.0 >> 8) & 0xFF) as u8;
        Components {
            blue: change_bit_depth::<2, 8>(blue),
            green: change_bit_depth::<3, 8>(green),
            red: change_bit_depth::<3, 8>(red),
            alpha
        }
    }
}

impl From<Components> for Argb8332 {
    fn from(components: Components) -> Self {
        let blue = (components.blue >> 6) as u16;
        let green = (components.green >> 5) as u16;
        let red = (components.red >> 5) as u16;
        let alpha = components.alpha as u16;
        
        Argb8332((alpha << 8) + (red << 5) + (green << 2) + blue)
    }
}

impl ColorBytes for Argb8332 {
    const BYTES_PER_PIXEL: usize = 2;

    fn read_color_bytes<R: BinRead>(mut r: R) -> Result<Self, R::Err> { r.read_u16().map(Argb8332) }
    fn write_color_bytes<W: BinWrite>(&self, mut w: W) -> Result<(), W::Err> { w.write_u16(self.0) }
}

impl From<Gray8> for Components {
    fn from(Gray8(value): Gray8) -> Components {
        Components { blue: value, green: value, red: value, alpha: 0xFF }
    }
}

impl From<Components> for Gray8 {
    fn from(components: Components) -> Self {
        let Components { blue, green, red, alpha: _ } = components;
        let y = (red as f32) * 0.2126 + (green as f32) * 0.7152 + (blue as f32) * 0.0722;

        // To overcome rounding error from the decimal coefficients, a tiny amount is added
        // which is smaller than the smallest possible contribution of a color value (0.0722),
        // and larger than the size of the rounding errors (~255 * 1e-7);
        //
        // Float to int is defined to saturate in rust, so no need to clip the float.
        let byte = (y + 0.001) as u8;
        Gray8(byte)
    }
}

impl ColorBytes for Gray8 {
    const BYTES_PER_PIXEL: usize = 1;

    fn read_color_bytes<R: BinRead>(mut r: R) -> Result<Self, R::Err> { r.read_u8().map(Gray8) }
    fn write_color_bytes<W: BinWrite>(&self, mut w: W) -> Result<(), W::Err> { w.write_u8(self.0) }
}

impl From<Rgb332> for Components {
    fn from(color: Rgb332) -> Components {
        let blue = (color.0 & 0x3) as u8;
        let green = ((color.0 >> 2) & 0x7) as u8;
        let red = ((color.0 >> 5) & 0x7) as u8;
        Components {
            blue: change_bit_depth::<2, 8>(blue),
            green: change_bit_depth::<3, 8>(green),
            red: change_bit_depth::<3, 8>(red),
            alpha: 0xFF
        }
    }
}

impl From<Components> for Rgb332 {
    fn from(components: Components) -> Self {
        let blue = (components.blue >> 6) as u8;
        let green = (components.green >> 5) as u8;
        let red = (components.red >> 5) as u8;
        
        Rgb332((red << 5) + (green << 2) + blue)
    }
}

impl ColorBytes for Rgb332 {
    const BYTES_PER_PIXEL: usize = 1;

    fn read_color_bytes<R: BinRead>(mut r: R) -> Result<Self, R::Err> { r.read_u8().map(Rgb332) }
    fn write_color_bytes<W: BinWrite>(&self, mut w: W) -> Result<(), W::Err> { w.write_u8(self.0) }
}

// take a color value that is N bits large and rescale it to M bits.
#[inline(always)]
fn change_bit_depth<const IN: u32, const OUT: u32>(x: u8) -> u8 {
    assert!(OUT <= IN * 2);
    if OUT <= IN {
        // downsizing
        x >> (IN - OUT)
    } else {
        // upsizing.  The left shift will produce some zero bits, which we fill with
        // a copy of the most significant bits to evenly spread out the change
        x << (OUT - IN) | x >> (2*IN - OUT)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_change_bit_depth() {
        assert_eq!(change_bit_depth::<4, 8>(0b1101), 0b11011101);
        assert_eq!(change_bit_depth::<5, 8>(0b10111), 0b10111101);
        assert_eq!(change_bit_depth::<8, 5>(0b10111000), 0b10111);
        assert_eq!(change_bit_depth::<8, 5>(0b10111111), 0b10111);
    }

    // Test that in all cases where R = G = B, gray8 produces that value as its byte.
    #[test]
    fn gray_8_floating_point_is_reliable() {
        for x in 0..=255u8 {
            let components = Components { red: x, green: x, blue: x, alpha: 0xFF };
            let luminosity = Gray8::from(components).0;
            assert_eq!(x, luminosity);
        }
    }

    // Black and white should round-trip.
    #[track_caller]
    fn black_and_white_check<C: From<Components> + Into<Components>>() {
        let black: Components = C::from(Components::BLACK).into();
        let white: Components = C::from(Components::WHITE).into();
        assert_eq!(black, Components::BLACK);
        assert_eq!(white, Components::WHITE);
    }

    #[test]
    fn black_and_white() {
        black_and_white_check::<Rgb565>();
        black_and_white_check::<Argb4444>();
        black_and_white_check::<Gray8>();
    }
}
