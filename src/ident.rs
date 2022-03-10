use std::fmt;
use std::rc::Rc;

use thiserror::Error;

use crate::resolve::ResId;
use crate::pos::Sp;

/// An identifier subject to name resolution.
///
/// This is a wrapper around [`Ident`] which additionally has room for a [`ResId`].  This ID
/// allows name resolution information (i.e. a [`DefId`]) to be recovered once the
/// [name resolution][`crate::passes::resolution`] pass has been run.
///
/// Note that the [`ResId`] will initially be null after parsing the ident; it is necessary
/// to call [`crate::passes::resolution::assign_res_ids`] to fill it in.
///
/// # Identifier syntax
///
/// See the documentation of [`Ident`].
///
/// # Uniqueness
///
/// There are some considerations that must be taken into account when cloning this type
/// (and in turn, for cloning AST nodes in general); please see [`ResId`] for more information.
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
    pub fn new(ident: Ident, res: ResId) -> ResIdent {
        ResIdent { ident, res: Some(res) }
    }

    /// Construct a [`ResIdent`] with no [`ResId`].
    ///
    /// Usage of this is niche and should be reserved for code that lacks mutable access to [`Resolutions`].
    /// (as otherwise, you should instead be calling [`Resolutions::attach_fresh_res`]!)
    pub fn new_null(ident: Ident) -> ResIdent {
        ResIdent { ident, res: None }
    }

    pub fn as_raw(&self) -> &Ident { &self.ident }
    pub fn as_raw_mut(&mut self) -> &mut Ident { &mut self.ident }

    /// Exposes the key for resolving this ident.
    #[track_caller]
    pub fn expect_res(&self) -> ResId {
        match self.res {
            Some(res) => res,
            None => panic!("(bug!) assign_res_ids has not been run yet for '{}'!", self.ident),
        }
    }

    pub fn as_str(&self) -> &str { self.ident.as_str() }
}


/// A raw identifier.
///
/// # Identifier syntax
///
/// An [`Ident`] must contain ASCII text.  This restriction is checked on construction.
///
/// There are no other restrictions.  Notably, [`Ident`] constructed for internal use are
/// permitted to clash with keywords and/or use characters that would not normally be valid
/// in a user-supplied identifier.
///
/// User idents (those parsed from files) follow the more conventional limitations of
/// C-like identifiers.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ident {
    ident: Rc<str>,
}

impl Ident {
    pub fn as_str(&self) -> &str { &self.ident }
}

#[derive(Debug, Error)]
pub enum ParseIdentError {
    #[error("non-ascii byte '\\x{:02x}'", .0)]
    NonAsciiByte(u8),
    /// Returned by [`Ident::new_user`] on any other ident which is a valid system identifier,
    /// but not a valid identifier token. (in terms of lexical class)
    #[error("invalid identifier: {}", .0)]
    NonUserIdent(Ident),
}

/// Wrapper around [`Ident::new_system`] and `format!` for use in cases that will obviously never fail.
/// (i.e. **no untrusted input**, no funny business with funky characters)
macro_rules! ident {
    ($($fmt_args:tt)+) => {
        $crate::ident::Ident::new_system(&format!($($fmt_args)+)).unwrap()
    };
}

impl Ident {
    /// Construct from any string which an [`Ident`] is allowed to hold (even strings that
    /// contain non-identifier characters like `@`, `*`, etc.).
    ///
    /// The precise set of restrictions is documented on the [`Ident`] type.
    pub fn new_system(s: &str) -> Result<Self, ParseIdentError> {
        if let Some(byte) = s.bytes().find(|&c| c & 0x80 != 0) {
            return Err(ParseIdentError::NonAsciiByte(byte));
        }
        Ok(Ident { ident: s.into() })
    }

    /// Construct from a string which would be a valid identifier in source code.
    ///
    /// This means that in addition to the limitations documented in [`Ident`], it must conform to
    /// the regex `[a-zA-Z_][a-zA-Z0-9_]*` and must not be a keyword. (contextual keywords are
    /// allowed).
    ///
    /// This might be a fair bit costlier than [`Ident::new_system`]!
    ///
    /// This function is rarely needed, as parsing a source file naturally only generates valid user
    /// [`Ident`]s by construction.  The primary use case is for places where an identifier must
    /// be embedded within e.g. a string literal.
    pub fn new_user(str: &str) -> Result<Self, ParseIdentError> {
        // get more specific error variants by delegating to the checks in `new_system` first
        let ident = Ident::new_system(str)?;

        // the restriction against keywords is tricky; the reliable solution is to ask our parser.
        //
        // we won't be using the diagnostics from the parser so `file_id = None` is okay.
        //
        // FIXME: this is bug prone.  If at some point in the future we introduce an immediately-
        //        emitted diagnostic (e.g. a warning) on some idents in the LALRPOP parser, that
        //        diagnostic will cause an internal compiler panic in this function.
        //        Not sure how to prevent this...
        let file_id = None;
        let spanned_str = crate::pos::SourceStr::from_full_source(file_id, str);
        let mut state = crate::parse::State::new();
        let mut lexer = crate::parse::lexer::GenericLexer::new(spanned_str);

        <Ident as crate::parse::Parse>::parse_stream(&mut state, &mut lexer)
            .map_err(|_| ParseIdentError::NonUserIdent(ident.clone()))?;

        if lexer.had_comment_or_ws() {
            return Err(ParseIdentError::NonUserIdent(ident));
        }

        Ok(ident)
    }
}

impl std::ops::Deref for ResIdent {
    type Target = Ident;

    fn deref(&self) -> &Self::Target { &self.ident }
}

impl AsRef<Ident> for ResIdent {
    fn as_ref(&self) -> &Ident { &self.ident }
}

impl AsRef<Ident> for Ident {
    fn as_ref(&self) -> &Ident { self }
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

    /// Generate a new, raw identifier.
    ///
    /// E.g. for a prefix of `"temp_"`, this could create an ident like `"temp_23"`.
    ///
    /// In an ideal world, this perhaps wouldn't be needed, since we already have [`DefId`]
    /// for representing unique identifiers.  But we need it anyways since those ids are stored
    /// on [`ResIdent`], which requires an [`Ident`].
    ///
    /// FIXME: The generated name can potentially clash with existing user-defined names.
    /// For now, to protect against this, any identifier that is gensym-ed should either be a
    /// [`ResIdent`] (and have a new [`DefId`] assigned to it immediately), or it should
    /// contain a non-identifier character.
    pub fn gensym(&mut self, prefix: &str) -> Ident {
        let id = self.next_id();
        Ident::new_system(&format!("{prefix}{id}")).expect("invalid prefix")
    }

    fn next_id(&mut self) -> u64 {
        let x = self.next_id;
        self.next_id += 1;
        x
    }
}

// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_user_ident() {
        use ParseIdentError::*;

        // specific errors
        assert!(matches!(Ident::new_user("ins_43"), Err(NonUserIdent { .. })));
        assert!(matches!(Ident::new_user("🐇"), Err(NonAsciiByte { .. })));
        // keyword
        assert!(matches!(Ident::new_user("while"), Err(NonUserIdent { .. })));
        // whitespace/comment
        assert!(matches!(Ident::new_user("  x"), Err(NonUserIdent { .. })));
        assert!(matches!(Ident::new_user("x  "), Err(NonUserIdent { .. })));
        assert!(matches!(Ident::new_user("x/* blah */"), Err(NonUserIdent { .. })));
        // followed by another token with no ws
        assert!(matches!(Ident::new_user("x*"), Err(NonUserIdent { .. })));
        // contextual keyword; check a few in case they get renamed
        assert!(matches!(Ident::new_user("entry"), Ok(_)));
        assert!(matches!(Ident::new_user("timeline"), Ok(_)));
        assert!(matches!(Ident::new_user("default"), Ok(_)));
    }
}
