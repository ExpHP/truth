//! Source code locations (some parts borrowed from [qluon])
//!
//! [qluon]: https://github.com/gluon-lang/gluon/blob/master/base/src/pos.rs

use std::fmt;
use std::borrow::Cow;
use std::num::NonZeroU32;
use std::cell::RefCell;
use std::rc::Rc;

use crate::diagnostic::Diagnostic;
use crate::parse::lexer;

pub type FileId = Option<NonZeroU32>;
use codespan_reporting::{files as cs_files};
pub use codespan::{ByteIndex as BytePos, ByteOffset, RawIndex, RawOffset};

/// Helper to wrap a value in [`Sp`]. It is recommended to use this in place of the type constructor.
///
/// * `sp!(span => value)` uses the given span.
/// * `sp!(value)` uses [`Span::NULL`].
///
/// ```
/// # let my_span = truth::Span::NULL;
/// # fn do_something() -> Expr { Expr::LitFloat { value: 2.0 } };
/// # fn do_something_else() -> Sp<Expr> { sp!(do_something()) };
/// use truth::{sp, Sp, ast::Expr};
///
/// let expr: Expr = do_something();
/// let something_else: Sp<Expr> = do_something_else();
///
/// // creating a value with the span of something else
/// let spanned: Sp<Expr> = sp!(something_else.span => expr.clone());
/// assert_eq!(spanned.span, something_else.span);
///
/// // creating a value with a dummy span (useful for generated code, e.g. during decompilation)
/// let spanned: Sp<Expr> = sp!(expr);
/// # let _ = spanned;
/// ```
#[macro_export]
macro_rules! sp {
    ($span:expr => $expr:expr) => { $crate::Sp { span: $span, value: $expr } };
    ($expr:expr) => { $crate::Sp { span: $crate::pos::Span::NULL, value: $expr } };
}

/// Pattern for matching against [`Sp`].
///
/// In this crate it is more common to match a pattern against `x.value` rather than to match
/// `sp_pat!` against `x`, but this can be useful to reduce nesting of `match`es when dealing
/// with nested `Sp`s.
///
/// ```
/// # let my_span = truth::Span::NULL;
/// # fn do_something() -> Sp<Expr> { truth::sp!(Expr::LitFloat { value: 2.0 }) };
/// use truth::{sp_pat, Sp, ast::Expr, ast::BinopKind};
///
/// let expr: Sp<Expr> = do_something();
///
/// // extracting just the value
/// let sp_pat!(value_1) = &expr;   // value has type &Expr
///
/// // extracting both the value and the span
/// let sp_pat!(span => value_2) = &expr;  // span has type &Span
///
/// assert_eq!(span, &expr.span);
/// assert_eq!(value_1, value_2);
///
/// // example use for matching a nested `Sp`
/// match &expr.value {
///     Expr::Binop(_, sp_pat!(BinopKind::Add), _) => println!("adding!"),
///     _ => println!("not adding!"),
/// }
/// ```
#[macro_export]
macro_rules! sp_pat {
    ($span:pat => $pat:pat) => { $crate::Sp { span: $span, value: $pat } };
    ($pat:pat) => { $crate::Sp { value: $pat, span: _ } };
}

/// An implementation of [`codespan_reporting::files::Files`] for `truth`.
///
/// This is the type responsible for keeping track of source text so that snippets can be displayed
/// in diagnostic error messages.
#[derive(Debug, Clone)]
pub struct Files {
    inner: RefCell<simple_files::SimpleFiles<String, Rc<str>>>,
}

impl Files {
    pub fn new() -> Self { Files { inner: RefCell::new(simple_files::SimpleFiles::new()) } }

    /// Add a piece of source text to the database, and give it a name (usually a filepath)
    /// which will appear in error messages.  Also validate the source as UTF-8.
    ///
    /// The name does not need to be a valid path or even unique; for instance, it is common to use
    /// the name `"<input>"` for source text not associated with any file.
    pub fn add(&self, name: &str, source: &[u8]) -> Result<(FileId, Rc<str>), Diagnostic> {
        let utf8_cow = prepare_diagnostic_text_source(source);
        let rc_source: Rc<str> = utf8_cow[..].into();

        let file_id = Self::shift_file_id(self.inner.borrow_mut().add(name.to_owned(), rc_source.clone()));

        // the cow is borrowed iff the input was valid UTF-8
        if let Cow::Owned(_) = utf8_cow {
            let err = std::str::from_utf8(source).unwrap_err();
            let pos = err.valid_up_to();
            return Err(error!(
                message("invalid UTF-8"),
                primary(Span::new(file_id, BytePos(pos as _), BytePos(pos as _)), "not valid UTF-8"),
                note("truth expects all input script files to be UTF-8 regardless of the output encoding"),
            ));
        }

        Ok((file_id, rc_source))
    }

    fn unshift_file_id(file_id: FileId) -> Result<usize, cs_files::Error> {
        // produce Error on file_id = None; such spans aren't fit for diagnostics
        let file_id: u32 = file_id.ok_or(cs_files::Error::FileMissing)?.into();
        Ok(file_id as usize - 1)
    }

    fn shift_file_id(file_id: usize) -> FileId {
        NonZeroU32::new(file_id as u32 + 1)
    }
}

/// This implementation provides source text that has been lossily modified to be valid UTF-8,
/// and which should only be used for diagnostic purposes.
impl<'a> cs_files::Files<'a> for Files {
    type FileId = FileId;
    type Name = String;
    type Source = Rc<str>;

    // Just delegate everything
    fn name(&self, file_id: FileId) -> Result<String, cs_files::Error> {
        self.inner.borrow().name(Self::unshift_file_id(file_id)?)
    }

    fn source(&self, file_id: FileId) -> Result<Rc<str>, cs_files::Error> {
        self.inner.borrow().source(Self::unshift_file_id(file_id)?).map(Clone::clone)
    }

    fn line_index(&self, file_id: FileId, byte_index: usize) -> Result<usize, cs_files::Error> {
        self.inner.borrow().line_index(Self::unshift_file_id(file_id)?, byte_index)
    }
    fn line_range(&self, file_id: FileId, line_index: usize) -> Result<std::ops::Range<usize>, cs_files::Error> {
        self.inner.borrow().line_range(Self::unshift_file_id(file_id)?, line_index)
    }
}

/// Obtain a UTF-8 version of the source that is suitable for rendering spans in error messages
/// for potentially non-UTF8 text.
fn prepare_diagnostic_text_source(s: &[u8]) -> Cow<'_, str> {
    // Back when truth allowed scripts to be Shift-JIS, we had to worry about the replacement character
    // messing up byte offsets, and so this was more complicated.
    //
    // Now that we require UTF-8, the only possible error that needs to be rendered from a non-UTF-8 file
    // is an error at the FIRST appearance of non-UTF8 data; thus the byte offsets will be just fine.
    String::from_utf8_lossy(s)
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    pub start: BytePos,
    pub end: BytePos,
    // FIXME: This is somewhat undesirable as it gets repeated all over the place.
    //        Gluon seems to have some way of making byte indices work as FileIds,
    //        but something seemed off about their Files impl when I tried it...
    pub file_id: FileId,
}

impl Span {
    /// A dummy span for generated code during decompilation.
    ///
    /// Because it uses an invalid file ID, diagnostic labels using this Span cannot be displayed.
    pub const NULL: Span = Span { start: BytePos(0), end: BytePos(0), file_id: None };

    /// Create a new span from a starting and ending span.
    pub fn new(file_id: FileId, start: impl Into<BytePos>, end: impl Into<BytePos>) -> Span {
        let start = start.into();
        let end = end.into();
        assert!(end >= start);

        Span { file_id, start, end }
    }

    /// Gives an empty span at the start of a source.
    pub const fn initial(file_id: FileId) -> Span {
        Span {
            file_id,
            start: BytePos(0),
            end: BytePos(0),
        }
    }

    pub(crate) fn from_locs(left: lexer::Location, right: lexer::Location) -> Self {
        debug_assert_eq!(left.0, right.0);
        Self::new(left.0, left.1, right.1)
    }

    /// Combine two spans by taking the start of the earlier span
    /// and the end of the later span.
    ///
    /// Note: this will work even if the two spans are disjoint.
    /// If this doesn't make sense in your application, you should handle it yourself.
    /// In that case, you can use `Span::disjoint` as a convenience function.
    ///
    /// ```rust
    /// use truth::Span;
    ///
    /// let span1 = Span::from(0..4);
    /// let span2 = Span::from(10..16);
    ///
    /// assert_eq!(Span::merge(span1, span2), Span::from(0..16));
    /// ```
    pub fn merge(self, other: Span) -> Span {
        use std::cmp::{max, min};

        assert_eq!(self.file_id, other.file_id);
        let start = min(self.start, other.start);
        let end = max(self.end, other.end);
        Span::new(self.file_id, start, end)
    }

    /// A helper function to tell whether two spans do not overlap.
    ///
    /// ```
    /// use truth::Span;
    /// let span1 = Span::from(0..4);
    /// let span2 = Span::from(10..16);
    /// assert!(span1.disjoint(span2));
    /// ```
    pub fn disjoint(self, other: Span) -> bool {
        assert_eq!(self.file_id.is_some(), other.file_id.is_some(), "can't compare dummy file span to non-dummy");
        if self.file_id != other.file_id {
            return true;
        }
        let (first, last) = if self.end < other.end {
            (self, other)
        } else {
            (other, self)
        };
        first.end <= last.start
    }

    /// Get the starting byte index.
    ///
    /// ```rust
    /// use truth::pos::{BytePos, Span};
    ///
    /// let span = Span::new(None, 0, 4);
    ///
    /// assert_eq!(span.start(), BytePos::from(0));
    /// ```
    pub fn start(self) -> BytePos {
        self.start
    }

    /// Get the ending byte index.
    ///
    /// ```rust
    /// use truth::pos::{BytePos, Span};
    ///
    /// let span = Span::new(None, 0, 4);
    ///
    /// assert_eq!(span.end(), BytePos::from(4));
    /// ```
    pub fn end(self) -> BytePos {
        self.end
    }

    pub fn start_span(self) -> Span {
        Span { file_id: self.file_id, start: self.start, end: self.start }
    }
    pub fn end_span(self) -> Span {
        Span { file_id: self.file_id, start: self.end, end: self.end }
    }
}

impl Default for Span {
    fn default() -> Span {
        Span::initial(None)
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{start}, {end})",
            start = self.start(),
            end = self.end(),
        )
    }
}

impl<I> From<std::ops::Range<I>> for Span
where
    I: Into<BytePos>,
{
    fn from(range: std::ops::Range<I>) -> Span {
        Span::new(None, range.start, range.end)
    }
}

impl From<Span> for std::ops::Range<usize> {
    fn from(span: Span) -> std::ops::Range<usize> {
        span.start.into()..span.end.into()
    }
}

impl From<Span> for std::ops::Range<RawIndex> {
    fn from(span: Span) -> std::ops::Range<RawIndex> {
        span.start.0..span.end.0
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn test_merge() {
        use super::Span;

        // overlap
        let a = Span::from(1..5);
        let b = Span::from(3..10);
        assert_eq!(a.merge(b), Span::from(1..10));
        assert_eq!(b.merge(a), Span::from(1..10));

        // subset
        let two_four = (2..4).into();
        assert_eq!(a.merge(two_four), (1..5).into());
        assert_eq!(two_four.merge(a), (1..5).into());

        // disjoint
        let ten_twenty = (10..20).into();
        assert_eq!(a.merge(ten_twenty), (1..20).into());
        assert_eq!(ten_twenty.merge(a), (1..20).into());

        // identity
        assert_eq!(a.merge(a), a);
    }

    #[test]
    fn test_disjoint() {
        use super::Span;

        // overlap
        let a = Span::from(1..5);
        let b = Span::from(3..10);
        assert!(!a.disjoint(b));
        assert!(!b.disjoint(a));

        // subset
        let two_four = (2..4).into();
        assert!(!a.disjoint(two_four));
        assert!(!two_four.disjoint(a));

        // disjoint
        let ten_twenty = (10..20).into();
        assert!(a.disjoint(ten_twenty));
        assert!(ten_twenty.disjoint(a));

        // identity
        assert!(!a.disjoint(a));

        // off by one (upper bound)
        let c = Span::from(5..10);
        assert!(a.disjoint(c));
        assert!(c.disjoint(a));
        // off by one (lower bound)
        let d = Span::from(0..1);
        assert!(a.disjoint(d));
        assert!(d.disjoint(a));
    }
}

/// An AST node with a span.
///
/// This type generally tries to behave like `T`.  It implements `Deref`, and the span is not
/// included in comparisons or hashes.
///
/// Use the [`sp!`][`sp`] macro to construct it.
///
/// ## Should functions take `&Sp<T>` or `Sp<&T>`?
///
/// **Prefer `&Sp<T>` where possible, use `Sp<&T>` where necessary.**
///
/// General wisdom for `Option<T>` is that it is better for functions to take `Option<&T>`
/// than `&Option<T>`, because the latter can easily be converted into the former but not
/// the other way around.  This comes at an ergonomic cost because parameters are now different
/// from other Options (the vast majority of non-parameter options will still be `Option<T>`).
/// Thankfully, `match` default bindings helps paper over this, because `let Some(x) = opt`
/// produces the same result for both `opt: &Option<T>` and `opt: &Option<T>`.
///
/// In the case of `Sp<T>`, however, we normally match on `sp.value`, so this distinction gets
/// more annoying.  Meanwhile, it turns out that it really isn't that hard to ensure that `&Sp<T>`
/// can be constructed in 99% of places that need it.  In most contexts where you need to apply a
/// new span to something, you're already required to clone it for at least one other reason.
///
/// One notable downside is that things like [`Expr::Var`] end up needing an `Sp<Var>` instead
/// of a [`Var`], even though the span will be identical to the span on the surrounding `Sp<Expr>`.
/// Currently, however, there's only a rare few instances of this sort of problem.
#[derive(Copy, Clone, Default)]
pub struct Sp<T: ?Sized> {
    pub span: Span,
    pub value: T,
}

impl<T> Sp<T> {
    /// Transform the value in some way while keeping the same span.
    pub fn sp_map<B>(self, func: impl FnOnce(T) -> B) -> Sp<B> {
        sp!(self.span => func(self.value))
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Sp<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // emit a compressed notation to make dbg! slightly less of an abomination
        write!(f, "sp!({:?} => ", &(self.span.start().0..self.span.end().0))?;
        // delegate for the main body so it is affected by {:#?}
        fmt::Debug::fmt(&self.value, f)?;
        write!(f, ")")
    }
}

impl<T: ?Sized + Eq> Eq for Sp<T> {}

impl<T: ?Sized + PartialEq> PartialEq for Sp<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<T: ?Sized + PartialEq> PartialEq<T> for Sp<T> {
    fn eq(&self, other: &T) -> bool {
        self.value == *other
    }
}

impl<T: ?Sized + std::hash::Hash> std::hash::Hash for Sp<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

impl<T: ?Sized> std::ops::Deref for Sp<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.value
    }
}

impl<T: ?Sized> std::ops::DerefMut for Sp<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

impl<T: ?Sized, U: ?Sized> AsRef<U> for Sp<T>
where
    T: AsRef<U>,
{
    fn as_ref(&self) -> &U {
        self.value.as_ref()
    }
}

impl<T: ?Sized> std::borrow::Borrow<T> for Sp<T> {
    fn borrow(&self) -> &T {
        &self.value
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for Sp<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.value)
    }
}


mod simple_files {
    use codespan_reporting::files::{line_starts, Files, Error};
    use std::ops::Range;

    /// Identical to [`codespan_reporting::files::SimpleFile`] but the associated
    /// `Source` type is `&'a Source`.
    #[derive(Debug, Clone)]
    pub struct SimpleFile<Name, Source> {
        name: Name,
        source: Source,
        line_starts: Vec<usize>,
    }

    impl<Name, Source> SimpleFile<Name, Source>
        where
            Name: std::fmt::Display,
            Source: AsRef<str>,
    {
        pub fn new(name: Name, source: Source) -> SimpleFile<Name, Source> {
            SimpleFile {
                name,
                line_starts: line_starts(source.as_ref()).collect(),
                source,
            }
        }

        pub fn name(&self) -> &Name {
            &self.name
        }

        pub fn source(&self) -> &Source {
            &self.source
        }

        fn line_start(&self, line_index: usize) -> Result<usize, Error> {
            use std::cmp::Ordering;

            match line_index.cmp(&self.line_starts.len()) {
                Ordering::Less => Ok(self
                    .line_starts
                    .get(line_index)
                    .cloned()
                    .expect("failed despite previous check")),
                Ordering::Equal => Ok(self.source.as_ref().len()),
                Ordering::Greater => Err(Error::LineTooLarge {
                    given: line_index,
                    max: self.line_starts.len() - 1,
                }),
            }
        }
    }

    impl<'a, Name, Source> Files<'a> for SimpleFile<Name, Source>
    where
        Name: 'a + std::fmt::Display + Clone,
        Source: 'a + AsRef<str>,
    {
        type FileId = ();
        type Name = Name;
        type Source = &'a Source;

        fn name(&self, (): ()) -> Result<Name, Error> {
            Ok(self.name.clone())
        }

        fn source(&self, (): ()) -> Result<&Source, Error> {
            Ok(&self.source)
        }

        fn line_index(&self, (): (), byte_index: usize) -> Result<usize, Error> {
            Ok(self
                .line_starts
                .binary_search(&byte_index)
                .unwrap_or_else(|next_line| next_line - 1))
        }

        fn line_range(&self, (): (), line_index: usize) -> Result<Range<usize>, Error> {
            let line_start = self.line_start(line_index)?;
            let next_line_start = self.line_start(line_index + 1)?;

            Ok(line_start..next_line_start)
        }
    }

    /// Identical to [`codespan_reporting::files::SimpleFiles`] but the associated
    /// `Source` type is `&'a Source`.
    #[derive(Debug, Clone)]
    pub struct SimpleFiles<Name, Source> {
        files: Vec<SimpleFile<Name, Source>>,
    }

    impl<Name, Source> SimpleFiles<Name, Source>
    where
        Name: std::fmt::Display,
        Source: AsRef<str>,
    {
        pub fn new() -> SimpleFiles<Name, Source> {
            SimpleFiles { files: Vec::new() }
        }

        pub fn add(&mut self, name: Name, source: Source) -> usize {
            let file_id = self.files.len();
            self.files.push(SimpleFile::new(name, source));
            file_id
        }

        pub fn get(&self, file_id: usize) -> Result<&SimpleFile<Name, Source>, Error> {
            self.files.get(file_id).ok_or(Error::FileMissing)
        }
    }

    impl<'a, Name, Source> Files<'a> for SimpleFiles<Name, Source>
    where
        Name: 'a + std::fmt::Display + Clone,
        Source: 'a + AsRef<str>,
    {
        type FileId = usize;
        type Name = Name;
        type Source = &'a Source;

        fn name(&self, file_id: usize) -> Result<Name, Error> {
            Ok(self.get(file_id)?.name().clone())
        }

        fn source(&self, file_id: usize) -> Result<&Source, Error> {
            Ok(self.get(file_id)?.source())
        }

        fn line_index(&self, file_id: usize, byte_index: usize) -> Result<usize, Error> {
            self.get(file_id)?.line_index((), byte_index)
        }

        fn line_range(&self, file_id: usize, line_index: usize) -> Result<Range<usize>, Error> {
            self.get(file_id)?.line_range((), line_index)
        }
    }
}

// =============================================================================

/// Used by error macros to allow either an [`Sp`] or a [`Span`] to serve as a location.
pub trait HasSpan {
    fn span(&self) -> Span;
}

impl<T: ?Sized> HasSpan for Sp<T> {
    fn span(&self) -> Span { self.span }
}

impl HasSpan for Span {
    fn span(&self) -> Span { *self }
}

impl<T: ?Sized + HasSpan> HasSpan for &T {
    fn span(&self) -> Span { (**self).span() }
}

impl<T: ?Sized + HasSpan> HasSpan for &mut T {
    fn span(&self) -> Span { (**self).span() }
}

impl<T: ?Sized + HasSpan> HasSpan for Box<T> {
    fn span(&self) -> Span { (**self).span() }
}
