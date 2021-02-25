use std::fmt;
use std::rc::Rc;

use thiserror::Error;

use crate::resolve::ResId;
use crate::pos::Sp;

/// An identifier subject to name resolution.
///
/// This is a wrapper around [`Ident`] which additionally has room for a [`ResId`].  This ID
/// allows name resolution information (i.e. a [`DefId`]) to be recovered once the
/// [name resolution][`crate::passes::resolve_names`] pass has been run.
///
/// Note that the [`ResId`] will initially be null after parsing the ident; it is necessary
/// to call [`crate::passes::resolve_names::assign_res_ids`] to fill it in.
///
/// # Identifier syntax
///
/// See the documentation of [`Ident`].
///
/// # Uniqueness
///
/// There are some considerations that must be taken into account when cloning this type
/// (and in turn, for cloning AST nodes in general); please see [`RegId`] for more information.
///
/// # Comparison and equality
///
/// Comparison operators are derived, mostly just so that unit tests can compare Exprs.
/// Thanks to the [`ResId`]s being null after parsing, these comparisons will serendipitously
/// just compare the idents for freshly-parsed AST nodes.
///
/// Keep in mind that comparing two [`ResIdent`]s will **not** determine whether they resolve to
/// the same definition (to accomplish this, one must compare [`DefId`]s).
/// For this reason, [`ResIdent`] does not impl [`std::hash::Hash`] or [`Ord`], as there seems
/// to be little reason to use them as map keys. (one should use [`ResId`] or [`DefId`] depending
/// on their intent)
#[derive(Clone, PartialEq, Eq)]  // NOTE: expressly NOT Hash or Ord
pub struct ResIdent {
    ident: Ident,
    pub res: Option<ResId>,
}

impl ResIdent {
    /// Construct a [`ResIdent`] with no [`ResId`].
    ///
    /// Usage of this is niche and should be reserved for code that lacks mutable access to [`Resolutions`].
    /// (as otherwise, you should instead be calling [`Resolutions::attach_fresh_res`]!)
    pub fn new_null(ident: Ident) -> ResIdent {
        ResIdent { ident, res: None }
    }

    pub fn as_raw(&self) -> &Ident {
        &self.ident
    }

    /// Exposes the key for resolving this ident.
    #[track_caller]
    pub fn expect_res(&self) -> ResId {
        match self.res {
            Some(res) => res,
            None => panic!("(bug!) assign_res_ids has not been run yet for '{}'!", self.ident),
        }
    }
}


/// A raw identifier.
///
/// # Identifier syntax
///
/// Identifiers must contain ASCII text.  Furthermore, it may not begin with `ins_` (this is
/// a raw instruction identifier).
///
// FIXME:  The `ins_` restriction no longer makes sense (how is it different from a keyword?).
//         Remove this, and add a better function for parsing user-provided idents which accepts
//         contextual keywords, but not other keywords.
//
/// These restrictions are checked when you construct an identifier using [`str::parse`].
///
/// There are no other restrictions.  Notably, identifiers constructed for internal use are
/// permitted to clash with keywords and/or use characters that would not normally be valid
/// in a user-supplied identifier.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ident {
    ident: Rc<str>,
}

#[derive(Debug, Error)]
pub enum ParseIdentError {
    #[error("unexpected instruction identifier")]
    UnexpectedIns,
    #[error("non-ascii byte '\\x{:02x}'", .0)]
    NonAsciiByte(u8),
}

// FIXME need separate ways to parse system idents and user idents
impl std::str::FromStr for Ident {
    type Err = ParseIdentError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some(byte) = s.bytes().find(|&c| c & 0x80 != 0) {
            return Err(ParseIdentError::NonAsciiByte(byte));
        }
        // Reject stuff like `ins_a`, `ins
        if s.starts_with("ins_") {
            return Err(ParseIdentError::UnexpectedIns);
        }
        Ok(Ident { ident: s.into() })
    }
}

impl std::ops::Deref for ResIdent {
    type Target = Ident;

    fn deref(&self) -> &Self::Target { &self.ident }
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
        write!(f, "Ident({:?}, {})", &self.ident, self.res.map(|x| x.0.get()).unwrap_or(0))
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
