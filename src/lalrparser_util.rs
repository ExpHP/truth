use std::str::FromStr;

/// Uses `FromStr` to parse something from a byte string.
///
/// This is only intended for use where the input is known in advance
/// to only contain ASCII, and may panic in other cases.
pub fn parse_ascii<B: AsRef<[u8]> + ?Sized, T: FromStr>(b: &B) -> Result<T, T::Err> {
    parse_utf8(b)
}

/// Uses `FromStr` to parse something from a byte string.
///
/// This is only intended for use where the input is known in advance
/// to contain valid UTF-8, and may panic in other cases.
pub fn parse_utf8<B: AsRef<[u8]> + ?Sized, T: FromStr>(b: &B) -> Result<T, T::Err> {
    std::str::from_utf8(b.as_ref()).expect("invalid utf-8!").parse()
}

/// Parses a `u32` from a byte string.
pub fn u32_from_ascii_radix<B: AsRef<[u8]> + ?Sized>(b: &B, radix: u32) -> Result<u32, std::num::ParseIntError> {
    u32::from_str_radix(std::str::from_utf8(b.as_ref()).expect("invalid utf-8!"), radix)
}

pub fn push<T>(mut vec: Vec<T>, item: T) -> Vec<T> {
    vec.push(item);
    vec
}
