use std::fmt;
use std::rc::Rc;

use thiserror::Error;
use lazy_static::lazy_static;
use regex::Regex;

use crate::var::ResolveId;
use crate::pos::Sp;

/// An identifier subject to name resolution.
///
/// This is a wrapper around [`Ident`] which additionally has room for a [`ResolveId`].  While this id
/// will initially be null after parsing the ident, the [name resolution][`crate::passes::resolve_names`]
/// pass will fill it in.
///
/// # Identifier syntax
///
/// See the documentation of [`Ident`].
///
/// # Comparison and equality
///
/// The impl of [`PartialEq`] for [`ResIdent`] is implemented to always compare the [`ResolveId`]s.
/// Accordingly, if name resolution has not been performed, **these comparisons will panic!**
/// (there is deliberately no fallback to comparing the identifier text, as this could mask bugs
/// where name resolution is skipped!)
///
/// This is perhaps not the most ideal situation, but these comparisons are mostly only provided for
/// the sake of `#[derive(PartialEq)]` on certain AST types, which in turn have little utility outside
/// of tests.
///
/// To compare the text part of the identifier, obtain a reference to an [`Ident`] by using
/// [`Deref<Target=Ident>`][`std::ops::Deref`] or [`Self::as_raw`].
#[derive(Clone)]
pub struct ResIdent {
    ident: Ident,
    disambig: Option<ResolveId>,
}

/// A raw identifier.
///
/// # Identifier syntax
///
/// Identifiers must contain ASCII text.  Furthermore, if it begins with `ins_`, it is
/// considered to be an **instruction identifier**, and the remaining part is required to be
/// a canonically-formatted non-negative integer.
///
/// These restrictions are checked when you construct an identifier using [`str::parse`].
///
/// There are no other restrictions.  Notably, identifiers constructed for internal use are
/// permitted to clash with keywords and/or use characters that would not normally be valid
/// in a user-supplied identifier.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ident {
    ident: Rc<str>,
}

impl ResIdent {
    pub fn new_ins(opcode: u16) -> Self {
        Ident::new_ins(opcode).into()
    }

    pub fn as_raw(&self) -> &Ident {
        &self.ident
    }

    pub(crate) fn set_res(&mut self, res: ResolveId) {
        self.disambig = Some(res);
    }

    #[track_caller]
    pub fn res(&self) -> Option<ResolveId> {
        self.disambig
    }

    /// Exposes the identification number used to resolve between identical names.
    ///
    /// As long as they are both resolved during the same call to the name resolution routine, no two
    /// identifiers representing different things will ever have the same [`ResolveId`] (even if
    /// the identifiers themselves are different), so the ID can stand alone in representing a named
    /// thing.
    #[track_caller]
    pub fn expect_res(&self) -> ResolveId {
        match self.disambig {
            Some(res) => res,
            None => panic!("(bug!) ident {} was not resolved!", self.ident),
        }
    }
}

impl Ident {
    pub fn new_ins(opcode: u16) -> Self {
        Ident { ident: format!("ins_{}", opcode).into() }
    }

    pub fn as_ins(&self) -> Option<u16> {
        if let Some(remainder) = self.ident.strip_prefix("ins_") {
            Some(remainder.parse().expect("(bug!) invalid instr ident!"))
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

impl std::str::FromStr for ResIdent {
    type Err = ParseIdentError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(ResIdent { ident: s.parse()?, disambig: None })
    }
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
        Ok(Ident { ident: s.into() })
    }
}

impl From<Ident> for ResIdent {
    fn from(ident: Ident) -> Self { ResIdent { ident, disambig: None }}
}

impl std::ops::Deref for ResIdent {
    type Target = Ident;

    fn deref(&self) -> &Self::Target { &self.ident }
}

// =============================================================================

impl PartialEq for ResIdent {
    fn eq(&self, rhs: &Self) -> bool {
        self.expect_res() == rhs.expect_res()
    }
}

// =============================================================================

impl PartialEq<str> for Ident {
    fn eq(&self, s: &str) -> bool { &self.ident[..] == s }
}

impl PartialEq<[u8]> for Ident {
    fn eq(&self, s: &[u8]) -> bool { self.ident.as_bytes() == s }
}

impl PartialEq<str> for Sp<Ident> {
    fn eq(&self, s: &str) -> bool { &self.ident[..] == s }
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

// =============================================================================

impl fmt::Debug for ResIdent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // NOTE: Deliberately using write! to disable :# formatting
        write!(f, "Ident({:?}, {})", &self.ident, self.disambig.map(|x| x.0.get()).unwrap_or(0))
    }
}

impl fmt::Display for ResIdent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.ident, f)
    }
}

impl fmt::Debug for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.ident, f)
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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
