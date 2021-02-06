use std::fmt;

use thiserror::Error;
use lazy_static::lazy_static;
use regex::Regex;

use crate::pos::Sp;

/// An identifier.
///
/// Identifiers must contain ASCII text.  Furthermore, if it begins with `ins_`, it is
/// considered to an **instruction identifier**, and the remaining part is required to be a
/// canonically-formatted non-negative integer.
///
/// There are no other restrictions.  Notably, identifiers constructed for internal use are
/// permitted to clash with keywords and/or use characters that would not normally be valid
/// in a user-supplied identifier.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ident {
    ident: String,
}

impl Ident {
    pub fn new_ins(opcode: u16) -> Self {
        Ident { ident: format!("ins_{}", opcode) }
    }
}

impl Ident {
    pub fn as_ins(&self) -> Option<u16> {
        if let Some(remainder) = self.ident.strip_prefix("ins_") {
            Some(remainder.parse().expect("invalid instr ident, this is a bug!"))
        } else {
            None
        }
    }
}

#[derive(Debug, Error)]
pub enum ParseIdentError {
    #[error("invalid instruction identifier")]
    InvalidIns,
    #[error("non-ascii byte '\\x{:02x}'", .0)]
    NonAsciiByte(u8),
}

// FIXME need separate ways to parse system idents and user idents
impl std::str::FromStr for Ident {
    type Err = ParseIdentError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        lazy_static! {
                // * requires an integer after "ins_"
                // * forbids leading zeroes so that the strings are unique
                //   (to facilitate equality comparisons)
                static ref VALID_INS_RE: Regex = Regex::new("^ins_(0|[1-9][0-9]*)$").unwrap();
            }
        if let Some(byte) = s.bytes().find(|&c| c & 0x80 != 0) {
            return Err(ParseIdentError::NonAsciiByte(byte));
        }
        if s.starts_with("ins_") && !VALID_INS_RE.is_match(s) {
            return Err(ParseIdentError::InvalidIns);
        }
        Ok(Ident { ident: s.to_string() })
    }
}

impl PartialEq<str> for Ident {
    fn eq(&self, s: &str) -> bool { self.ident == s }
}

impl PartialEq<[u8]> for Ident {
    fn eq(&self, s: &[u8]) -> bool { self.ident.as_bytes() == s }
}

impl PartialEq<str> for Sp<Ident> {
    fn eq(&self, s: &str) -> bool { self.ident == s }
}

impl PartialEq<[u8]> for Sp<Ident>  {
    fn eq(&self, s: &[u8]) -> bool { self.ident.as_bytes() == s }
}

impl PartialEq<Ident> for str {
    fn eq(&self, s: &Ident) -> bool { s == self }
}

impl PartialEq<Ident> for [u8] {
    fn eq(&self, s: &Ident) -> bool { s == self }
}

impl PartialEq<Sp<Ident>> for str {
    fn eq(&self, s: &Sp<Ident>) -> bool { s == self }
}

impl PartialEq<Sp<Ident>> for [u8] {
    fn eq(&self, s: &Sp<Ident>) -> bool { s == self }
}

impl AsRef<str> for Ident {
    fn as_ref(&self) -> &str { &self.ident }
}

impl AsRef<[u8]> for Ident {
    fn as_ref(&self) -> &[u8] { self.ident.as_bytes() }
}

impl std::borrow::Borrow<str> for Ident {
    fn borrow(&self) -> &str { &self.ident }
}

impl std::borrow::Borrow<str> for Sp<Ident> {
    fn borrow(&self) -> &str { &self.ident }
}

impl fmt::Debug for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        fmt::Debug::fmt(&self.ident, f)
    }
}

impl std::fmt::Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        fmt::Display::fmt(&self.ident, f)
    }
}

// =============================================================================

/// Helper for generating unique identifiers.
#[derive(Debug, Clone, Default)]
pub struct GensymContext {
    next_id: u64,
}

impl GensymContext {
    pub const fn new() -> Self {
        GensymContext { next_id: 0 }
    }

    pub fn gensym(&mut self, prefix: &str) -> Ident {
        let id = self.next_id();
        format!("{}{}", prefix, id).parse().expect("invalid prefix")
    }

    fn next_id(&mut self) -> u64 {
        let x = self.next_id;
        self.next_id += 1;
        x
    }
}
