use crate::ast;

pub use high::{TypeSystem, Signature, SignatureParam, NameId};
pub use low::{InstrAbi, ArgEncoding};
mod low;
mod high;

// --------------------------------------------

/// Type of an expression.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(enum_map::Enum)]
pub enum ScalarType {
    Int,
    Float,
    String,
}

impl ScalarType {
    /// Textual description, e.g. `"an integer"`.
    pub fn descr(self) -> &'static str {
        match self {
            ScalarType::Int => "an integer",
            ScalarType::Float => "a float",
            ScalarType::String => "a string",
        }
    }

    pub fn descr_plural(self) -> &'static str {
        match self {
            ScalarType::Int => "integers",
            ScalarType::Float => "floats",
            ScalarType::String => "strings",
        }
    }

    pub fn sigil(self) -> Option<ast::VarReadType> {
        match self {
            ScalarType::Int => Some(ast::VarReadType::Int),
            ScalarType::Float => Some(ast::VarReadType::Float),
            ScalarType::String => None,
        }
    }
}
