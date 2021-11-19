//! Helper functions that ideally would have been defined inside the grammar file, but aren't
//! because they can't (?) be defined there.

use std::str::FromStr;
use core::fmt;

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

pub enum Either<A, B> { This(A), That(B) }

/// Parse a string literal, including surrounding quotes
pub fn parse_string_literal(string: &str) -> Result<String, crate::diagnostic::Diagnostic> {
    let mut out = String::new();
    let mut escape = false;

    assert_eq!(&string[0..1], "\"");
    assert_eq!(&string[string.len()-1..], "\"");
    for c in string[1..string.len()-1].chars() {
        if escape {
            escape = false;
            match c {
                '0' => out.push_str("\0"),
                '"' => out.push_str("\""),
                '\\' => out.push_str("\\"),
                'n' => out.push_str("\n"),
                'r' => out.push_str("\r"),
                _ => {
                    let escape = match c.is_ascii_graphic() {
                        true => format!("'{}'", c),
                        false => format!("U+{:04x}", c as u32),
                    };
                    return Err(error!(message("invalid escape character {}", escape)));
                },
            }
        } else if c == '\\' {
            escape = true;
        } else {
            out.push(c);
        }
    }
    assert!(!escape);  // should be impossible due to the token's regex
    Ok(out)
}

/// Type whose [`core::fmt::Display`] impl panics.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PanicDisplay;

impl fmt::Display for PanicDisplay {
    fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
        panic!("Whoops! You're not supposed to see this...")
    }
}
