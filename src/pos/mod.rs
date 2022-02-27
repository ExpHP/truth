//! Source code locations (some parts borrowed from [qluon])
//!
//! [qluon]: https://github.com/gluon-lang/gluon/blob/master/base/src/pos.rs

pub type FileId = Option<std::num::NonZeroU32>;
pub use codespan::{ByteIndex as BytePos, ByteOffset, RawIndex, RawOffset};

pub use span::{Sp, Span, HasSpan};
#[macro_use] mod span;

pub use source_map::Files;
mod source_map;

pub use spanned_str::SpannedStr;
mod spanned_str;
