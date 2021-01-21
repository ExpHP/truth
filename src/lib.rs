#[macro_use]
mod util_macros;

pub use error::{CompileError};
#[macro_use]
#[doc(hidden)]
pub mod error;

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

pub use anm::AnmFile;
pub mod anm;
pub use self::std::StdFile;
pub mod std;

// FIXME make this part of `ast`
pub mod meta;

pub use eclmap::Eclmap;
pub mod eclmap;

pub use type_system::{TypeSystem, ScalarType};
pub mod type_system;

pub use passes::DecompileKind;
pub mod passes;

pub use ident::{Ident, ParseIdentError};
pub mod ident;

pub use game::Game;
mod game;

#[doc(hidden)]
pub mod cli_def;
pub mod cli_helper;

pub use var::{RegId, VarId, LocalId, Variables};
mod var;

mod binary_io;

pub mod llir;

pub mod vm;

pub use value::ScalarValue;
mod value {
    use std::fmt;
    use crate::ast;
    use crate::type_system::ScalarType;

    #[derive(Debug, Copy, Clone, PartialEq, PartialOrd)]
    pub enum ScalarValue { Int(i32), Float(f32) }

    impl From<ScalarValue> for ast::Expr {
        fn from(value: ScalarValue) -> Self { match value {
            ScalarValue::Int(value) => ast::Expr::from(value),
            ScalarValue::Float(value) => ast::Expr::from(value),
        }}
    }

    impl ScalarValue {
        pub fn ty(&self) -> ScalarType { match self {
            ScalarValue::Int(_) => ScalarType::Int,
            ScalarValue::Float(_) => ScalarType::Float,
        }}

        /// Allows simulating the effect of e.g. `%INT_VAR` or `$FLOAT_VAR`.
        /// (basically, the game performs typecasts when variables are read as the other type)
        pub fn apply_sigil(self, ty_sigil: Option<ast::VarReadType>) -> ScalarValue {
            match ty_sigil {
                None => return self,
                Some(ast::VarReadType::Int) => ScalarValue::Int(self.read_as_int()),
                Some(ast::VarReadType::Float) => ScalarValue::Float(self.read_as_float()),
            }
        }

        /// Obtain an integer value, as if read with a `$` prefix.  (i.e. casting if float)
        pub fn read_as_int(self) -> i32 {
            match self {
                ScalarValue::Int(x) => x,
                ScalarValue::Float(x) => x as i32,
            }
        }

        /// Obtain a float value, as if read with a `%` prefix.  (i.e. casting if integer)
        pub fn read_as_float(self) -> f32 {
            match self {
                ScalarValue::Int(x) => x as f32,
                ScalarValue::Float(x) => x,
            }
        }
    }

    impl fmt::Display for ScalarValue {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                ScalarValue::Float(x) => write!(f, "{:?}", x),
                ScalarValue::Int(x) => write!(f, "{}", x),
            }
        }
    }
}

pub trait VeclikeIterator: ExactSizeIterator + DoubleEndedIterator { }
impl<Xs: ExactSizeIterator + DoubleEndedIterator> VeclikeIterator for Xs { }
