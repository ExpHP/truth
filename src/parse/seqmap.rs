use regex::Regex;
use lazy_static::lazy_static;

use crate::pos::{Sp, Span, BytePos};
use crate::diagnostic::{Emitter};
use crate::error::{ErrorReported};

/// Fairly direct representation of Seqmap syntax.
///
/// It doesn't handle any processing of "duplicate" entries or etc.,
/// just faithfully gives all lines as they appeared in the file.
#[derive(Debug)]
pub struct SeqmapRaw<'a> {
    /// This includes the `!`.
    pub magic: Sp<&'a str>,
    pub sections: Vec<SeqmapRawSection<'a>>,
}

#[derive(Debug)]
pub struct SeqmapRawSection<'a> {
    /// This does not include the `!` and will have at least one character, but is otherwise unvalidated.
    pub header: Sp<&'a str>,
    pub lines: Vec<(Sp<i32>, Sp<&'a str>)>,
}

lazy_static! {
    static ref SEQMAP_START_RE: Regex = Regex::new(r"^!([_a-zA-Z][_a-zA-Z0-9]*)$").unwrap();
    static ref SEQMAP_ITEM_RE: Regex = Regex::new(r"^(-?[0-9]+)\s*(\S*)$").unwrap();
}

impl<'a> SeqmapRaw<'a> {
    pub fn parse(file_start: BytePos, text: &'a str, emitter: &impl Emitter) -> Result<Self, ErrorReported> {
        parse_seqmap(SpannedStr::new(file_start, text), emitter)
    }
}

fn parse_seqmap<'a>(mut text: SpannedStr<'a>, emitter: &impl Emitter) -> Result<SeqmapRaw<'a>, ErrorReported> {
    let mut sections = vec![];
    let mut cur_section = None;

    let magic = match text.split_next_line() {
        Some(magic_line) => {
            let magic_line = magic_line.trim_end();
            if magic_line.chars().next() != Some('!') {
                return Err(emitter.emit(error!(
                    message("missing magic for mapfile"),
                    primary(magic_line.span(), "line does not begin with '!'"),
                )));
            }
            sp!(magic_line.span() => magic_line.str)
        },
        None => return Err(emitter.emit(error!("file is empty"))),
    };

    while let Some(mut line) = text.split_next_line() {
        if let Some(hash_index) = line.find("#") {
            line = line.slice_to(hash_index);
        }
        line = line.trim();

        if line.is_empty() {
            continue;
        } else if line.starts_with("!") {
            let header = match SEQMAP_START_RE.captures(&line) {
                Some(captures) => {
                    let capture = captures.get(1).unwrap();
                    let matched_str = line.slice(capture.start()..capture.end());
                    sp!(matched_str.span() => matched_str.str)
                },
                None => return Err(emitter.emit(error!(
                    message("bad section start: {:?}", line.str.trim()),
                    primary(line.trim_end().span(), "bad section header"),
                ))),
            };

            cur_section = {
                sections.push(SeqmapRawSection { header, lines: vec![] });
                Some(sections.last_mut().unwrap())
            };
        } else {
            match SEQMAP_ITEM_RE.captures(&line) {
                None => return Err(emitter.emit(error!(
                    message("error parsing mapfile item"),
                    primary(line.trim_end().span(), "invalid mapfile item")
                ))),
                Some(captures) => {
                    let number_capture = captures.get(1).unwrap();
                    let value_capture = captures.get(2).unwrap();
                    let number_spanned = line.slice(number_capture.start()..number_capture.end());
                    let value_spanned = line.slice(value_capture.start()..value_capture.end());
                    let number = sp!(number_spanned.span() => number_spanned.parse().unwrap());
                    let value = sp!(value_spanned.span() => value_spanned.str);

                    match &mut cur_section {
                        None => return Err(emitter.emit(error!(
                            message("mapfile missing section header"),
                            primary(line.trim_end().span(), "entry without section header"),
                        ))),
                        Some(section) => section.lines.push((number, value)),
                    }
                }
            }
        }
    }
    Ok(SeqmapRaw { magic, sections })
}

// Seqmap syntax isn't amenable to a lexer so we can't use LALRPOP.
//
// Here's a quick utility to help deal with the spans for us as we do stringly things.
use spanned_str::SpannedStr;
mod spanned_str {
    use super::*;

    #[derive(Debug, Clone)]
    pub struct SpannedStr<'a> {
        pub str: &'a str,
        start_pos: BytePos,
    }

    lazy_static! {
        static ref LINE_END_RE: Regex = Regex::new(r#"\r\n?|\n"#).unwrap();
    }

    impl<'a> SpannedStr<'a> {
        pub fn new(start_pos: BytePos, str: &'a str) -> Self {
            SpannedStr { str, start_pos }
        }

        pub fn span(&self) -> Span {
            Span::new(self.start_pos, self.start_pos.add_safe(self.str.len() as _))
        }

        /// Return a line (with the line terminator) and remove it from this string.
        pub fn split_next_line(&mut self) -> Option<SpannedStr<'a>> {
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

        /// Return a copy with the first `index` characters and remove them from `self`.
        fn split_off_front(&mut self, index: usize) -> SpannedStr<'a> {
            let out = self.slice_to(index);
            *self = self.slice_from(index);
            out
        }

        pub fn trim(&self) -> SpannedStr<'a> {
            self.trim_end().trim_start()
        }

        pub fn trim_end(&self) -> SpannedStr<'a> {
            self.slice_to(self.str.trim_end().len())
        }

        pub fn trim_start(&self) -> SpannedStr<'a> {
            let ws_len = self.len() - self.str.trim_start().len();
            self.slice_from(ws_len)
        }

        pub fn slice(&self, index: std::ops::Range<usize>) -> SpannedStr<'a> {
            self.slice_to(index.end).slice_from(index.start)
        }

        pub fn slice_to(&self, index: usize) -> SpannedStr<'a> {
            SpannedStr { str: &self.str[..index], ..*self }
        }

        pub fn slice_from(&self, index: usize) -> SpannedStr<'a> {
            SpannedStr {
                str: &self.str[index..],
                start_pos: self.start_pos.add_safe(index as _),
            }
        }
    }

    impl std::ops::Deref for SpannedStr<'_> {
        type Target = str;

        fn deref(&self) -> &str { self.str }
    }

    #[test]
    fn test_trim() {
        // nontrivial
        let input = SpannedStr { str: "  aaf io    ", start_pos: BytePos::new(17) };
        let trimmed = input.trim();
        assert_eq!(u32::from(trimmed.start_pos), 19);
        assert_eq!(trimmed.str, "aaf io");

        // trivial
        let input = SpannedStr { str: "aaf io", start_pos: BytePos::new(17) };
        let trimmed = input.trim();
        assert_eq!(u32::from(trimmed.start_pos), 17);
        assert_eq!(trimmed.str, "aaf io");

        // all whitespace; edge case where a bad implementation could double-count
        let input = SpannedStr { str: "   ", start_pos: BytePos::new(17) };
        let trimmed = input.trim();
        assert!(17 <= usize::from(trimmed.start_pos) && usize::from(trimmed.start_pos) <= 17 + input.len());
        assert_eq!(trimmed.str, "");
    }
}
