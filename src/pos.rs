//! Source code locations (some parts borrowed from [qluon])
//!
//! [qluon]: https://github.com/gluon-lang/gluon/blob/master/base/src/pos.rs

use std::fmt;
use std::borrow::Cow;

pub type FileId = usize;
use codespan_reporting::{files as cs_files};
pub use codespan::Span;
pub use codespan::{ByteIndex as BytePos};

pub type Files = NonUtf8Files;

/// An implementation of [`codespan_reporting::files::Files`] adapted to non-UTF8 files.
#[derive(Debug, Clone)]
pub struct NonUtf8Files {
    inner: cs_files::SimpleFiles<String, String>,
}

impl NonUtf8Files {
    pub fn new() -> Self { NonUtf8Files { inner: cs_files::SimpleFiles::new() } }

    pub fn add(&mut self, name: impl AsRef<std::path::Path>, source: &[u8]) -> FileId {
        self.inner.add(
            name.as_ref().to_string_lossy().into_owned(),
            prepare_diagnostic_text_source(source).into(),
        )
    }
    pub fn source(&mut self, file_id: FileId) -> Result<&[u8], cs_files::Error> {
        <_ as cs_files::Files>::source(&self.inner, file_id)
            .map(|s| s.as_bytes())
    }
    pub fn get(&mut self, file_id: FileId) -> Result<&cs_files::SimpleFile<String, String>, cs_files::Error> {
        self.inner.get(file_id)
    }
}

impl<'a> cs_files::Files<'a> for NonUtf8Files {
    type FileId = FileId;
    type Name = String;
    type Source = &'a str;

    // Just delegate everything
    fn name(&self, file_id: FileId) -> Result<String, cs_files::Error> { self.inner.name(file_id) }

    fn source(&self, file_id: FileId) -> Result<&str, cs_files::Error> { self.inner.source(file_id) }

    fn line_index(&self, file_id: FileId, byte_index: usize) -> Result<usize, cs_files::Error> {
        self.inner.line_index(file_id, byte_index)
    }
    fn line_range(&self, file_id: FileId, line_index: usize) -> Result<std::ops::Range<usize>, cs_files::Error> {
        self.inner.line_range(file_id, line_index)
    }
}

/// A version of `from_utf8_lossy` that preserves byte positions.
///
/// The output of this is suitable for rendering spans in error messages.
///
/// It accomplishes this by using `?` as the replacement character, which only takes a single byte
/// and can thus easily fill arbitrarily-sized spaces, unlike `U+FFFD REPLACEMENT CHARACTER`
/// which takes three bytes.
fn prepare_diagnostic_text_source(s: &[u8]) -> Cow<str> {
    match std::str::from_utf8(s) {
        Ok(valid) => Cow::Borrowed(valid),
        Err(error) => {
            let mut remaining = s;
            let mut out = String::new();
            let mut res = Err(error);
            while let Err(error) = res {
                let (valid, after_valid) = remaining.split_at(error.valid_up_to());
                out.push_str(std::str::from_utf8(valid).expect("already validated"));

                let num_bad = error.error_len().unwrap_or(after_valid.len());
                for _ in 0..num_bad {
                    out.push('?');
                }
                remaining = &after_valid[num_bad..];
                res = std::str::from_utf8(remaining);
            }
            match res {
                Err(_) => unreachable!(),
                Ok(remaining_str) => out.push_str(remaining_str),
            }
            assert_eq!(s.len(), out.len());
            Cow::Owned(out)
        },
    }
}

#[test]
fn test_lossy_utf8() {
    let func = prepare_diagnostic_text_source;

    // valid UTF-8
    assert_eq!(func(b"ab\xF0\x9F\x92\x96cd"), "ab💖cd");

    // invalid byte sequence...
    assert_eq!(func(b"\x80\xFFcd"), "??cd"); // ...at beginning
    assert_eq!(func(b"ab\x80\xFFcd"), "ab??cd"); // ...in middle
    assert_eq!(func(b"ab\x80\xFF"), "ab??"); // ...at end

    // incomplete character; byte 0b11110000 expects 3 more bytes after it.
    // (this is the case where Utf8Error::error_len() returns None)
    assert_eq!(func(b"ab\xF0\x80\x80"), "ab???");

    // unpaired surrogate
    // http://simonsapin.github.io/wtf-8/#surrogates-byte-sequences
    assert_eq!(func(b"ab\xED\xA3\xA4cd"), "ab???cd");

    // ambiguous case.  This begins with a 4-byte character starter byte, but returns to ascii after
    // 2 bytes. I'm not sure whether the documentation of `Utf8Error::error_len` is specified
    // well-enough to determine whether this would replace the two 'w' characters.
    let input = b"ab\xF0\x80wwcd";
    let output = func(input);
    assert_eq!(output.len(), input.len());
    assert_eq!(&output.as_bytes()[..2], &input[..2]);
    assert_eq!(&output.as_bytes()[2..2+2], b"??");
    assert_eq!(&output.as_bytes()[2+4..], &input[2+4..]);
}

/// An AST node with a span.  The span is not included in comparisons or hashes.
#[derive(Copy, Clone, Default)]
pub struct Spanned<T: ?Sized> {
    pub span: Span,
    pub value: T,
}

impl<T: fmt::Debug> fmt::Debug for Spanned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Spanned")
            // format as a range instead of Span's derived Debug
            .field("span", &(self.span.start().0..self.span.end().0))
            .field("value", &self.value)
            .finish()
    }
}

impl<T> Spanned<T> {
    pub fn null_from<U: Into<T>>(value: U) -> Self {
        Spanned {
            span: Span::default(),
            value: value.into(),
        }
    }

    pub fn new_from<U: Into<T>>(span: Span, value: U) -> Self {
        Spanned { span, value: value.into() }
    }
}

impl<T> From<T> for Spanned<T> {
    fn from(value: T) -> Self {
        Spanned {
            span: Span::default(),
            value,
        }
    }
}

impl<T: ?Sized + Eq> Eq for Spanned<T> {}

impl<T: ?Sized + PartialEq> PartialEq for Spanned<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<T: ?Sized + PartialEq> PartialEq<T> for Spanned<T> {
    fn eq(&self, other: &T) -> bool {
        self.value == *other
    }
}

impl<T: ?Sized + std::hash::Hash> std::hash::Hash for Spanned<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

impl<T: ?Sized> std::ops::Deref for Spanned<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.value
    }
}

impl<T: ?Sized> std::ops::DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

impl<T: ?Sized, U: ?Sized> AsRef<U> for Spanned<T>
where
    T: AsRef<U>,
{
    fn as_ref(&self) -> &U {
        self.value.as_ref()
    }
}

impl<T> Spanned<T> {
    pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> Spanned<U> {
        Spanned {
            span: self.span,
            value: f(self.value),
        }
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for Spanned<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.value)
    }
}
