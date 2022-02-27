//! Helper functions that ideally would have been defined inside the grammar file, but aren't
//! because they can't (?) be defined there.

use core::fmt;

use crate::pos::Span;
use crate::parse::lexer::Location;

pub fn push<T>(mut vec: Vec<T>, item: T) -> Vec<T> {
    vec.push(item);
    vec
}

pub enum Either<A, B> { This(A), That(B) }

pub fn parse_u32_literal(
    string: &str,
    (l, r): (Location, Location),
) -> Result<u32, crate::diagnostic::Diagnostic> {
    parse_u32_literal_nospan(string)
        .map_err(|mut diag| {
            diag.primary(Span::from_locs(l, r), format!(""));
            diag
        })
}

pub fn parse_string_literal(
    string: &str,
    (l, r): (Location, Location),
) -> Result<String, crate::diagnostic::Diagnostic> {
    parse_string_literal_nospan(string)
        .map_err(|mut diag| {
            diag.primary(Span::from_locs(l, r), format!(""));
            diag
        })
}

#[deprecated = "mid-refactor, will be deleted"]
pub fn parse_u32_literal_nospan(
    string: &str,
) -> Result<u32, crate::diagnostic::Diagnostic> {
    let result = match &string[..usize::min(string.len(), 2)] {
        "0x" | "0X" => u32::from_str_radix(&string[2..], 16),
        "0b" | "0B" => u32::from_str_radix(&string[2..], 2),
        _ => string.parse(),
    };
    result.map_err(|err| error!(
        message("bad integer literal"),
        // primary(Span::from_locs(l, r), "{}", err)
    ))
}

/// Parse a string literal, including surrounding quotes
#[deprecated = "mid-refactor, will be deleted"]
pub fn parse_string_literal_nospan(
    string: &str,
) -> Result<String, crate::diagnostic::Diagnostic> {
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
                    return Err(error!(
                        message("invalid escape character {}", escape),
                        // primary(Span::from_locs(l, r), "contains invalid escape"),
                    ));
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
