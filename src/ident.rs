use std::sync::atomic;

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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ident<S=String> {
    ident: S,
}

impl Ident {
    pub fn new_ins(opcode: u32) -> Self {
        Ident { ident: format!("ins_{}", opcode) }
    }
}

impl<S: AsRef<str>> Ident<S> {
    pub fn as_ins(&self) -> Option<u32> {
        if let Some(remainder) = self.ident.as_ref().strip_prefix("ins_") {
            Some(remainder.parse().expect("invalid instr ident, this is a bug!"))
        } else {
            None
        }
    }
}

#[derive(Debug, Error)]
pub enum ParseIdentError {
    #[error("Invalid instruction identifier")]
    InvalidIns,
    #[error("Non-ascii byte '\\x{:02x}'", .0)]
    NonAsciiByte(u8),
}
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

impl std::fmt::Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", &self.ident[..])
    }
}

// =============================================================================

/// Helper for generating unique identifiers in a threadsafe manner.
pub struct GensymContext {
    next_id: atomic::AtomicU64,
}

impl GensymContext {
    pub const fn new() -> Self {
        GensymContext { next_id: atomic::AtomicU64::new(0) }
    }

    pub fn gensym(&self, prefix: &str) -> Ident {
        let id = self.next_id();
        format!("{}{}", prefix, id).parse().expect("invalid prefix")
    }

    fn next_id(&self) -> u64 {
        self.next_id.fetch_add(1, atomic::Ordering::Relaxed)
    }
}
