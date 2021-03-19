#[macro_use]
mod util_macros;

pub use error::{CompileError};

pub mod error;
pub mod diagnostic;

pub use pos::{Files, Span, Sp};
#[macro_use]
pub mod pos;

#[macro_use]
pub mod quote;

pub use ast::{Visit, VisitMut};
pub mod ast;
pub use fmt::{Format, Formatter};
pub mod fmt;

pub mod parse;

// FIXME make this part of `ast`
pub mod meta;

pub use eclmap::Eclmap;
pub mod eclmap;

pub use context::{CompilerContext};
pub mod context;

pub use passes::DecompileKind;
pub mod passes;

pub use ident::{Ident, ParseIdentError};
pub mod ident;

pub use formats::anm::{self, AnmFile};
pub use formats::msg::{self, MsgFile};
pub use formats::std::{self, StdFile};
mod formats;

pub use game::Game;
mod game;

#[doc(hidden)]
pub mod cli_def;

pub use resolve::{RegId, DefId};
mod resolve;

mod io;

pub mod llir;

pub mod pseudo;

pub mod vm;

pub use value::{ScalarValue, ScalarType};
mod value;

pub trait VeclikeIterator: ExactSizeIterator + DoubleEndedIterator { }
impl<Xs: ExactSizeIterator + DoubleEndedIterator> VeclikeIterator for Xs { }

/// Sets global environment to improve testing conditions.
///
/// List of effects:
/// * Ensures there is no default search path for mapfiles.
/// * Will allow warnings to be captured by the test harness instead of going straight to stderr.
///
/// Of course, because the test harness runs tests in parallel, this ultimately only needs to run
/// once; but it is safe to run it any number of times.
#[doc(hidden)]
pub fn setup_for_test_harness() {
    ::std::env::set_var("_TRUTH_DEBUG__TEST", "1");
    ::std::env::remove_var("TRUTH_MAP_PATH");
}

/// To let tests iterate over all main subcommands.
pub fn all_main_commands() -> Vec<&'static str> {
    vec!["thanm", "thstd"]
}
