use bstr::{ByteSlice, ByteVec};
use core::fmt;
use codespan_reporting::term::termcolor;

lazy_static::lazy_static! {
    static ref SOURCE_POS_RE: regex::Regex = {
        regex::Regex::new(r"^ *┌─* (.+):(\d+):(\d+)\s*$").unwrap()
    };
}

#[derive(Debug, Clone)]
pub struct ParsedDiagnostic {
    kind: DiagnosticKind,
    /// `None` for diagnostics with no span.
    src_line_number: Option<i32>,
    src_filename: Option<String>,
    /// The full diagnostic text as written to STDERR, including source snippets.
    text: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DiagnosticKind { Error, Warning, Bug, Info }

#[derive(Debug, Clone)]
pub struct ExpectedDiagnostic {
    kind: DiagnosticKind,
    src_line_number: Option<i32>,
    src_filename: Option<String>,
    pattern: String,
}

impl ExpectedDiagnostic {
    pub fn new_error_without_location(pattern: String) -> Self {
        Self::new_without_location(DiagnosticKind::Error, pattern)
    }

    pub fn new_warning_without_location(pattern: String) -> Self {
        Self::new_without_location(DiagnosticKind::Warning, pattern)
    }

    fn new_without_location(kind: DiagnosticKind, pattern: String) -> Self {
        ExpectedDiagnostic {
            kind, pattern,
            src_filename: None,
            src_line_number: None,
        }
    }

    pub fn implies_failure(&self) -> bool {
        matches!(self.kind, DiagnosticKind::Error | DiagnosticKind::Bug)
    }
}

// This screenscrapes diagnostic output for error messages.
//
// This is sadly what must be done, until a JSON output format is added to codespan_reporting.
pub fn parse_diagnostics(text: &[u8]) -> Vec<ParsedDiagnostic> {
    let line_starts = [
        (&b"bug: "[..], DiagnosticKind::Bug),
        (&b"error: "[..], DiagnosticKind::Error),
        (&b"warning: "[..], DiagnosticKind::Warning),
        (&b"info: "[..], DiagnosticKind::Info),
    ];

    let mut cur_diagnostic = None;
    let mut out = vec![];
    for line in text.lines() {
        let line_str = core::str::from_utf8(line).ok();
        if let Some(&(_, kind)) = line_starts.iter().find(|&(label, _)| line.starts_with(label)) {
            // header line of diagnostic.  ("error:", "warning:", etc.)
            if let Some(diagnostic) = cur_diagnostic {
                out.push(diagnostic);
            }
            cur_diagnostic = Some(ParsedDiagnostic {
                kind,
                src_filename: None,
                src_line_number: None,
                text: String::new(),  // first line will be added at end of loop iteration
            });
        } else if let Some(captures) = SOURCE_POS_RE.captures(line_str.unwrap_or("")) {
            // location line of diagnostic  (e.g. "┌─ /tmp/3798afg2r89f:7:1")
            let filename = captures.get(1).unwrap().as_str();
            let line_no = captures.get(2).unwrap().as_str().parse::<i32>().unwrap();

            let diagnostic = cur_diagnostic.as_mut().expect("no diagnostic header line?");
            if diagnostic.src_line_number.is_none() {
                diagnostic.src_line_number = Some(line_no);
                // filenames should've been replaced with things like <input> and etc. before calling us
                assert!(
                    filename.starts_with("<") && filename.ends_with(">"),
                    "file path was not made deterministic: {:?}", filename,
                );

                diagnostic.src_filename = Some(filename.to_string());
            }
        }

        if let Some(diagnostic) = &mut cur_diagnostic {
            diagnostic.text.push_str(&String::from_utf8_lossy(line));
            diagnostic.text.push_str("\n");
        }
    }

    if let Some(diagnostic) = cur_diagnostic {
        out.push(diagnostic);
    }
    out
}

/// Parse `//~` comments from source text.
///
/// NOTE: Currently, this also strips them and returns a modified source text, for a couple of reasons:
/// 1. the actual diagnostics are currently screenscraped and we don't want them to trivially
///    contain the expected pattern.
/// 2. //~ isn't valid in mapfiles
pub fn parse_expected_diagnostics(filename: &str, source: &[u8]) -> (Vec<u8>, Vec<ExpectedDiagnostic>) {
    let mut prev_diagnostic_line_num = None;

    let mut cleaned_source = Vec::new();
    let mut out = vec![];
    for (line_index, line) in source.lines().enumerate() {
        let (cleaned_line, comment) = match line.find("//~") {
            Some(index) => (&line[..index], Some(&line[index + "//~".len()..])),
            None => (line, None),
        };
        cleaned_source.extend_from_slice(cleaned_line.trim_end());
        cleaned_source.push_str("\n");

        let mut remainder = match comment {
            Some(comment) => comment,
            None => continue,
        };

        // determine expected line number
        let mut expected_diagnostic_line = line_index + 1;  // numbered from 1
        if remainder.get(0) == Some(&b'|') {
            remainder = &remainder[1..];
            expected_diagnostic_line = prev_diagnostic_line_num.expect("invalid `//~|` (no previous annotation)");
        } else {
            while let Some(&b'^') = remainder.get(0) {
                remainder = &remainder[1..];
                expected_diagnostic_line -= 1;
            }
        }

        remainder = remainder.trim_start();
        let types = [
            (&b"BUG "[..], DiagnosticKind::Bug),
            (&b"ERROR "[..], DiagnosticKind::Error),
            (&b"WARNING "[..], DiagnosticKind::Warning),
            (&b"INFO "[..], DiagnosticKind::Info),
        ];
        let &(label, kind) = match types.iter().find(|&(label, _)| remainder.starts_with(label)) {
            Some(tup) => tup,
            None => panic!("bad diagnostic line: {:?}", std::str::from_utf8(line)),
        };
        remainder = &remainder[label.len()..];
        remainder = remainder.trim();
        if remainder.is_empty() {
            panic!("diagnostic comment has no expected message: {:?}", std::str::from_utf8(line));
        }
        out.push(ExpectedDiagnostic {
            kind,
            src_filename: Some(filename.to_string()),
            src_line_number: Some(expected_diagnostic_line as _),
            pattern: remainder.to_str().expect("non-utf8 pattern").to_string(),
        });
        prev_diagnostic_line_num = Some(expected_diagnostic_line);
    }
    (cleaned_source, out)
}

/// Strip all `//~ ERROR` tags and similar from a source string.
pub fn strip_diagnostic_comments(source: &str) -> String {
    let bytes = parse_expected_diagnostics("DUMMY", source.as_bytes()).0;
    String::from_utf8(bytes).unwrap()
}

pub fn compare_actual_and_expected_diagnostics(
    actual_diagnostics: &[ParsedDiagnostic],
    expected_diagnostics: &[ExpectedDiagnostic],
    allow_extra: bool,
) {
    let mut actual_seen = vec![false; actual_diagnostics.len()];
    let mut expected_seen = vec![false; expected_diagnostics.len()];

    for (actual_index, actual) in actual_diagnostics.iter().enumerate() {
        for (expected_index, expected) in expected_diagnostics.iter().enumerate() {
            if expected_seen[expected_index] {
                continue;
            }

            let actual_meta = (&actual.kind, &actual.src_filename, actual.src_line_number);
            let expected_meta = (&expected.kind, &expected.src_filename, expected.src_line_number);
            if actual_meta == expected_meta {
                if actual.text.contains(&expected.pattern) {
                    actual_seen[actual_index] = true;
                    expected_seen[expected_index] = true;
                    break;
                }
            }
        }
    }

    let has_extra = actual_seen.iter().any(|&x| !x);
    let has_missing = expected_seen.iter().any(|&x| !x);
    if has_missing || (has_extra && !allow_extra) {
        for (actual, seen) in actual_diagnostics.iter().zip(actual_seen) {
            if !seen {
                let color = termcolor::Color::Green;
                eprintln_as_color(color, format_args!("=== EXTRA diagnostic"));
                eprintln_as_color(color, format_args!("{:?}", actual));
            }
        }
        if !allow_extra {
            for (pattern, seen) in expected_diagnostics.iter().zip(expected_seen) {
                if !seen {
                    let color = termcolor::Color::Red;
                    eprintln_as_color(color, format_args!("== MISSING diagnostic =="));
                    eprintln_as_color(color, format_args!("{:?}", pattern));
                }
            }
        }
        panic!("diagnostics did not match");
    }
}

fn eprintln_as_color(color: termcolor::Color, text: impl fmt::Display) {
    use termcolor::WriteColor;
    use std::io::Write;

    let mut buf = termcolor::Ansi::new(vec![]);
    buf.set_color(termcolor::ColorSpec::new().set_fg(Some(color))).unwrap();
    write!(buf, "{}", text).unwrap();
    buf.reset().unwrap();

    eprintln!("{}", String::from_utf8_lossy(&buf.into_inner()));
}
