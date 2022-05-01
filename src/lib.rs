#[macro_use]
mod util_macros;

pub use error::ErrorReported;
pub mod error;
pub mod diagnostic;

pub use pos::{Files, Span, Sp};
#[macro_use]
pub mod pos;

pub use ident::{Ident, ParseIdentError};
#[macro_use]
pub mod ident;

#[macro_use]
pub mod quote;

mod core_mapfiles;

pub use ast::{Visit, VisitMut};
pub mod ast;
pub use fmt::{Format, Formatter};
pub mod fmt;

pub mod parse;

pub use mapfile::Mapfile;
pub mod mapfile;

pub use context::{Scope, CompilerContext};
pub mod context;

pub mod passes;


pub mod raw;

pub use formats::anm::{self, AnmFile, WorkingAnmFile};
pub use formats::msg::{self, MsgFile};
pub use formats::mission::{self, MissionMsgFile};
pub use formats::std::{self, StdFile};
pub use formats::ecl::{self, OldeEclFile as EclFile};
mod formats;

mod bitset;
mod diff_switch_utils;

pub use game::{Game, LanguageKey};
mod game;

#[doc(hidden)]
pub mod cli_def;

pub use resolve::{RegId, DefId};
mod resolve;

mod image;

pub use io::Fs;
pub mod io;

pub use llir::DecompileOptions;
pub mod llir;

pub mod vm;

pub use value::{ScalarValue, ScalarType};
mod value;

pub use api::{Builder, Truth};
mod api;

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

mod env {
    pub fn is_test_mode() -> bool {
        ::std::env::var("_TRUTH_DEBUG__TEST").ok().as_deref() == Some("1")
    }
}

/// To let tests iterate over all main subcommands.
pub fn all_main_commands() -> Vec<&'static str> {
    vec!["thanm", "thstd"]
}
