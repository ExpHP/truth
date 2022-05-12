use std::borrow::Cow;
use core::fmt;

use regex::Regex;
use lazy_static::lazy_static;

use crate::pos::{Sp, Span, FileId, SourceStr};
use crate::diagnostic::{Emitter};
use crate::error::{ErrorReported};

/// Fairly direct representation of Seqmap syntax.
///
/// It doesn't handle any processing of "duplicate" entries or etc.,
/// just faithfully gives all lines as they appeared in the file.
///
/// It can be written back to text via [`fmt::Display`].
#[derive(Debug)]
pub struct SeqmapRaw<'a> {
    /// This includes the `!`.
    pub magic: Sp<Cow<'a, str>>,
    pub sections: Vec<SeqmapRawSection<'a>>,
}

#[derive(Debug)]
pub struct SeqmapRawSection<'a> {
    /// This does not include the `!` and will have at least one character, but is otherwise unvalidated.
    pub header: Sp<Cow<'a, str>>,
    pub lines: Vec<(Sp<i32>, Sp<Cow<'a, str>>)>,
}

const IDENT_RE_STR: &str = "[_a-zA-Z][_a-zA-Z0-9]*";
lazy_static! {
    static ref SEQMAP_START_RE: Regex = Regex::new(&format!(r"^!({}(?:\([^\)]+\))?)$", IDENT_RE_STR)).unwrap();
    static ref SEQMAP_ITEM_RE: Regex = Regex::new(r"^(-?[0-9]+)\s*(.*)$").unwrap();
}

impl<'a> SeqmapRaw<'a> {
    pub fn parse(file_id: FileId, text: &'a str, emitter: &impl Emitter) -> Result<Self, ErrorReported> {
        parse_seqmap(SourceStr::from_full_source(file_id, text), emitter)
    }
}

fn parse_seqmap<'a>(mut text: SourceStr<'a>, emitter: &impl Emitter) -> Result<SeqmapRaw<'a>, ErrorReported> {
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
                sections.push(SeqmapRawSection { header: header.sp_map(Cow::Borrowed), lines: vec![] });
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
                        Some(section) => section.lines.push((number, value.sp_map(Cow::Borrowed))),
                    }
                }
            }
        }
    }
    Ok(SeqmapRaw { magic: magic.sp_map(Cow::Borrowed), sections })
}

impl fmt::Display for SeqmapRaw<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "{}", self.magic)?;
        for SeqmapRawSection { header, lines } in &self.sections {
            writeln!(f)?;
            writeln!(f, "!{header}")?;
            for &(num, ref text) in lines {
                writeln!(f, "{num} {text}")?;
            }
        }
        Ok(())
    }
}
