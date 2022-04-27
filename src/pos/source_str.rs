use regex::Regex;

use crate::pos::{FileId, Sp, Span};

/// Represents a piece of input source text with a known span.
///
/// Provides operations for slicing this text in a manner that also slices the span.
///
/// The text stored in [`SourceStr`] should be exactly the input source text, so that the length of
/// the [`Span`] is identical to the length of the string. Contrast this with [`Sp`]`<String>`, whose
/// span length and string length may differ due to e.g. escape sequences and inclusion/exclusion of
/// delimiters like `"`.
#[derive(Debug, Clone, Copy)]
pub struct SourceStr<'a> {
    pub str: &'a str,
    file_id: FileId,
    start_pos: usize,
}

lazy_static::lazy_static! {
    static ref LINE_END_RE: Regex = Regex::new(r#"\r\n?|\n"#).unwrap();
}

impl<'a> SourceStr<'a> {
    /// Constructs a [`SourceStr`] from a string that isn't in the source map.
    ///
    /// This is primarily meant to facilitate writing tests.  The spans from this will
    /// have a [`FileId`] of `None`, meaning that diagnostics may panic.
    pub(crate) fn new_null(str: &'a str) -> Self {
        Self::from_full_source(None, str)
    }

    /// Construct from the full source text associated with a [`FileId`].
    pub fn from_full_source(file_id: FileId, str: &'a str) -> Self {
        SourceStr { str, file_id, start_pos: 0 }
    }

    /// Construct from a source string and its corresponding span.
    pub fn from_span(span: Span, str: &'a str) -> Self {
        println!("{:?}", span);
        println!("{:?}", str);
        assert_eq!(span.len(), str.len(), "input str is not original source text, or span is wrong!");
        SourceStr {
            str,
            file_id: span.file_id,
            start_pos: span.start.into(),
        }
    }

    pub fn span(&self) -> Span {
        Span {
            file_id: self.file_id,
            start: (self.start_pos as u32).into(),
            end: ((self.start_pos + self.str.len()) as u32).into(),
        }
    }
}

/// Helper functions for some handwritten parsers.
impl<'a> SourceStr<'a> {
    /// Return a line (with the line terminator) and remove it from this string.
    pub fn split_next_line(&mut self) -> Option<SourceStr<'a>> {
        LINE_END_RE.find(self.str)
            .map(|m| self.split_off_front(m.end()))
            .or_else(|| {
                // last line may be missing terminator
                match self.str.len() {
                    0 => None,
                    n => Some(self.split_off_front(n)),
                }
            })
    }

    /// Return the first character and remove it from this string.
    pub fn split_next_char(&mut self) -> Option<Sp<char>> {
        self.str.chars().next().map(|char| {
            let char_str = self.split_off_front(char.len_utf8());
            sp!(char_str.span() => char)
        })
    }

    /// Return a copy with the first `index` characters and remove them from `self`.
    fn split_off_front(&mut self, index: usize) -> SourceStr<'a> {
        let out = self.slice_to(index);
        *self = self.slice_from(index);
        out
    }

    pub fn trim(&self) -> SourceStr<'a> {
        self.trim_end().trim_start()
    }

    pub fn trim_end(&self) -> SourceStr<'a> {
        self.slice_to(self.str.trim_end().len())
    }

    pub fn trim_start(&self) -> SourceStr<'a> {
        let ws_len = self.len() - self.str.trim_start().len();
        self.slice_from(ws_len)
    }

    pub fn slice(&self, index: std::ops::Range<usize>) -> SourceStr<'a> {
        self.slice_to(index.end).slice_from(index.start)
    }

    pub fn slice_to(&self, index: usize) -> SourceStr<'a> {
        SourceStr { str: &self.str[..index], ..*self }
    }

    pub fn slice_from(&self, index: usize) -> SourceStr<'a> {
        SourceStr {
            str: &self.str[index..],
            start_pos: self.start_pos + index,
            file_id: self.file_id,
        }
    }
}

impl std::ops::Deref for SourceStr<'_> {
    type Target = str;

    fn deref(&self) -> &str { self.str }
}

#[test]
fn test_trim() {
    // nontrivial
    let input = SourceStr { file_id: None, str: "  aaf io    ", start_pos: 17 };
    let trimmed = input.trim();
    assert_eq!(trimmed.start_pos, 19);
    assert_eq!(trimmed.str, "aaf io");

    // trivial
    let input = SourceStr { file_id: None, str: "aaf io", start_pos: 17 };
    let trimmed = input.trim();
    assert_eq!(trimmed.start_pos, 17);
    assert_eq!(trimmed.str, "aaf io");

    // all whitespace; edge case where a bad implementation could double-count
    let input = SourceStr { file_id: None, str: "   ", start_pos: 17 };
    let trimmed = input.trim();
    assert!(17 <= trimmed.start_pos && trimmed.start_pos <= 17 + input.len());
    assert_eq!(trimmed.str, "");
}
