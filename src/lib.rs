#[macro_use]
mod util_macros;

pub use error::ErrorReported;
pub mod error;
pub mod diagnostic;

pub use pos::{Files, Span, Sp};
#[macro_use]
pub mod pos;

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

pub use ident::{Ident, ParseIdentError};
pub mod ident;

pub mod raw;

pub use formats::anm::{self, AnmFile};
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

#[test]
fn SIZES<'input>() {
    use crate::ast::{self, meta, Meta};
    use crate::ident::ResIdent;
    use crate::parse::lalrparser_util as util;

    let mut max = 0;
    macro_rules! check {
        ($ty:ty) => {
            max = usize::max(max, core::mem::size_of::<$ty>());
            eprintln!("{:3} {}", core::mem::size_of::<$ty>(), stringify!($ty));
        };
    }

    check!(&'input str);
    check!(i32);
    check!(core::option::Option<Sp<ast::Expr>>);
    check!(Vec<core::option::Option<Sp<ast::Expr>>>);
    check!(Sp<i32>);
    check!(core::option::Option<Sp<i32>>);
    check!(());
    check!(Sp<ast::Expr>);
    check!((Sp<Ident>, Sp<Meta>));
    check!(Sp<ast::Var>);
    check!(core::option::Option<Sp<ast::Var>>);
    check!(crate::parse::lexer::Location);
    check!(Sp<crate::parse::AnythingValue>);
    check!(crate::parse::AnythingValue);
    check!(ast::Block);
    check!(Box<ast::Block>);
    check!(Box<ast::Expr>);
    check!(Box<ast::Item>);
    check!(Box<ast::LitString>);
    check!(Box<Meta>);
    check!(Box<ast::ScriptFile>);
    check!(Box<Sp<ast::Expr>>);
    check!(Box<Sp<ast::Item>>);
    check!(Box<ast::Var>);
    check!(Box<ast::Stmt>);
    check!(Box<ast::StmtKind>);
    check!(ast::BreakContinueKeyword);
    check!(ast::CallAsyncKind);
    check!(core::option::Option<ast::CallAsyncKind>);
    check!(ast::CallableName);
    check!(ast::Cond);
    check!(ast::CondBlock);
    check!(ast::StmtCondChain);
    check!(ast::CondKeyword);
    check!((Sp<ast::Var>, Sp<ast::Expr>));
    check!(ast::TypeKeyword);
    check!(ast::DiffLabel);
    check!(util::Either<Sp<ast::PseudoArg>, Sp<ast::Expr>>);
    check!(ast::Expr);
    check!(Vec<Sp<ast::Expr>>);
    check!((Vec<Sp<ast::PseudoArg>>, Vec<Sp<ast::Expr>>));
    check!(ast::FuncParam);
    check!(ast::UnOpKind);
    check!(Ident);
    check!(ast::Item);
    check!(ast::ItemFunc);
    check!(Vec<Sp<ast::Item>>);
    check!(ast::LabelPropertyKeyword);
    check!(f32);
    check!(Result<u32, core::num::ParseIntError>);
    check!(ast::LitString);
    check!(Meta);
    check!(meta::Fields);
    check!(ast::MetaKeyword);
    check!(ast::BinOpKind);
    check!(ast::AssignOpKind);
    check!(ast::PseudoArg);
    check!(ast::PseudoArgKind);
    check!(u16);
    check!(ResIdent);
    check!(ast::ScriptFile);
    check!(Vec<Sp<(Sp<ast::Var>, Sp<ast::Expr>)>>);
    check!(Vec<Sp<(Sp<ast::Var>, Option<Sp<ast::Expr>>)>>);
    check!(Vec<(Sp<Ident>, Sp<Meta>)>);
    check!(Vec<util::Either<Sp<ast::PseudoArg>, Sp<ast::Expr>>>);
    check!(Vec<Sp<ast::FuncParam>>);
    check!(Vec<Sp<Meta>>);
    check!(ast::FuncQualifier);
    check!(Sp<()>);
    check!(Sp<Box<ast::Stmt>>);
    check!(Sp<ast::BreakContinueKeyword>);
    check!(Sp<ast::CallableName>);
    check!(Sp<ast::Cond>);
    check!(Sp<ast::CondKeyword>);
    check!(Sp<(Sp<ast::Var>, Sp<ast::Expr>)>);
    check!(Sp<ast::TypeKeyword>);
    check!(Sp<ast::DiffLabel>);
    check!(Sp<ast::FuncParam>);
    check!(Sp<ast::UnOpKind>);
    check!(Sp<Ident>);
    check!(Sp<ast::Item>);
    check!(Sp<ast::LabelPropertyKeyword>);
    check!(Sp<ast::LitString>);
    check!(Sp<Meta>);
    check!(Sp<meta::Fields>);
    check!(Sp<ast::MetaKeyword>);
    check!(Sp<ast::BinOpKind>);
    check!(Sp<ast::AssignOpKind>);
    check!(Sp<ast::PseudoArg>);
    check!(Sp<ast::PseudoArgKind>);
    check!(Sp<ResIdent>);
    check!(Sp<ast::FuncQualifier>);
    check!(core::option::Option<Sp<ast::FuncQualifier>>);
    check!(Sp<(Sp<ast::Var>, Option<Sp<ast::Expr>>)>);
    check!(Vec<Sp<ast::Stmt>>);
    check!(Span);
    check!((Sp<ast::Var>, Option<Sp<ast::Expr>>));
    check!(ast::StmtJumpKind);
    check!(ast::Var);
    check!(ast::VarName);
    check!(Option<ast::VarSigil>);
    eprintln!("{}", max);
    panic!();
}
