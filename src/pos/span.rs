use core::fmt;

use crate::pos::{BytePos, FileId, RawIndex};
use crate::parse::lexer;

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
/// use truth::{sp_pat, Sp, ast::Expr, ast::BinOpKind};
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
///     Expr::BinOp(_, sp_pat!(BinOpKind::Add), _) => println!("adding!"),
///     _ => println!("not adding!"),
/// }
/// ```
#[macro_export]
macro_rules! sp_pat {
    ($span:pat => $pat:pat) => { $crate::Sp { span: $span, value: $pat } };
    ($pat:pat) => { $crate::Sp { value: $pat, span: _ } };
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

    /// Create a new span representing the full span of a source string, taken to start at position 0.
    pub fn of_full_source(file_id: FileId, source: &str) -> Span {
        Span { file_id, start: 0.into(), end: u32::try_from(source.len()).unwrap().into() }
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

    pub fn len(self) -> usize { (self.end - self.start).into() }

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

impl<T: ?Sized + PartialOrd> PartialOrd<T> for Sp<T> {
    fn partial_cmp(&self, other: &T) -> Option<std::cmp::Ordering> {
        self.value.partial_cmp(other)
    }
}

impl<T: ?Sized + PartialOrd> PartialOrd for Sp<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.value.partial_cmp(&other.value)
    }
}

impl<T: ?Sized + Ord> Ord for Sp<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.value.cmp(&other.value)
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

// Can't generalize, would conflict with the Borrow<T> for T impl. </3
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
