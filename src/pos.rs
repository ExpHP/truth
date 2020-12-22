//! Source code locations (borrowed from [qluon])
//!
//! [qluon]: https://github.com/gluon-lang/gluon/blob/master/base/src/pos.rs

use std::fmt;
use std::borrow::Cow;

pub use codespan::Files;
pub use codespan::Span;
pub use codespan::{ByteIndex as BytePos};

/// A version of `from_utf8_lossy` that preserves byte positions.
///
/// The output of this is suitable for rendering spans in error messages.
///
/// It accomplishes this by using `?` as the replacement character, which only takes a single byte
/// and can thus easily fill arbitrarily-sized spaces, unlike `U+FFFD REPLACEMENT CHARACTER`
/// which takes three bytes.
pub fn prepare_diagnostic_text_source(s: &[u8]) -> Cow<str> {
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

#[derive(Copy, Clone, Debug, Eq, PartialEq, Default, Hash)]
pub struct Spanned<T: ?Sized> {
    pub span: Span,
    pub value: T,
}

impl<T> From<T> for Spanned<T> {
    fn from(value: T) -> Self {
        Spanned {
            span: Span::default(),
            value,
        }
    }
}

impl<T: ?Sized + PartialEq> PartialEq<T> for Spanned<T> {
    fn eq(&self, other: &T) -> bool {
        self.value == *other
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

pub fn spanned<T>(span: Span, value: T) -> Spanned<T> {
    Spanned { span, value }
}

pub fn spanned2<T>(start: BytePos, end: BytePos, value: T) -> Spanned<T> {
    spanned(Span::new(start, end), value)
}
