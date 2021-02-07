use std::fmt;
use std::num::NonZeroU64;
use std::rc::Rc;

use thiserror::Error;
use lazy_static::lazy_static;
use regex::Regex;

use crate::pos::Sp;

// FIXME:  The recommendation that you can use EITHER Ident OR ResolveId after name resolution
//         is probably not wise, but for now I don't know which is a better recommendation.
//         We can revisit this later when we have more experience with it.
//
/// An identifier.
///
/// # Syntax
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
///
/// # Uniqueness and comparison
///
/// During [name resolution][`crate::passes::resolve_names`], disambiguating [ID numbers][`ResolveId`]
/// are embedded into the [`Ident`]s to resolve them by scope.  When these ID numbers are set, they
/// are used for hashing and equality instead of the ident text itself.
///
/// These properties make [`Ident`] a reasonable sort of "id type" for things that require
/// name resolution.  That said, you can also call [`Ident::expect_resolved`] to use these IDs
/// directly.
#[derive(Clone)]
pub struct Ident {
    ident: RawIdent,
    disambig: Option<ResolveId>,
}

/// Type of an ident without name resolution info.
pub(crate) type RawIdent = Rc<str>;

/// Represents an identifier that has been uniquely resolved according to its scope.
///
/// Strictly speaking, most code shouldn't *need* this, as directly comparing [`Ident`] will already
/// take advantage of these when available.  That said, if a pass requires name resolution in order
/// to be correct, obtaining these is at least a good excuse to panic when they're missing.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ResolveId(pub NonZeroU64);

impl Ident {
    pub fn new_ins(opcode: u16) -> Self {
        Ident {
            ident: format!("ins_{}", opcode).into(),
            disambig: None,
        }
    }

    pub fn as_ins(&self) -> Option<u16> {
        if let Some(remainder) = self.ident.strip_prefix("ins_") {
            Some(remainder.parse().expect("(bug!) invalid instr ident!"))
        } else {
            None
        }
    }

    pub(crate) fn as_raw(&self) -> &RawIdent {
        &self.ident
    }

    pub(crate) fn set_id(&mut self, id: ResolveId) {
        self.disambig = Some(id);
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
        self.disambig.unwrap_or_else(|| panic!("(bug!) ident {} was not resolved!", self.ident))
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
        Ok(Ident { ident: s.into(), disambig: None })
    }
}

/// A type that is used as the basis for Eq and Hash impls of [`Ident`].
type Comparable<'a> = Result<ResolveId, &'a str>;

impl Ident {
    fn as_comparable(&self) -> Comparable<'_> {
        match self.disambig {
            Some(disambig) => Ok(disambig),
            None => Err(&self.ident),
        }
    }
}

impl PartialEq for Ident {
    fn eq(&self, rhs: &Ident) -> bool {
        self.as_comparable() == rhs.as_comparable()
    }
}

impl Eq for Ident {}

impl std::hash::Hash for Ident {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_comparable().hash(state)
    }
}

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

impl fmt::Debug for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // NOTE: Deliberately using write! to disable :# formatting
        write!(f, "Ident({:?}, {})", &self.ident, self.disambig.map(|x| x.0.get()).unwrap_or(0))
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.ident, f)
    }
}

impl fmt::Debug for ResolveId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

impl fmt::Display for ResolveId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
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
