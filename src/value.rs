//! Enums for reasoning about values and types in the program.

use std::fmt;
use crate::ast;

/// The value of an expression.
#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum ScalarValue {
    Int(i32),
    Float(f32),
    String(String),
}

impl From<ScalarValue> for ast::Expr {
    fn from(value: ScalarValue) -> Self { match value {
        ScalarValue::Int(value) => ast::Expr::from(value),
        ScalarValue::Float(value) => ast::Expr::from(value),
        ScalarValue::String(value) => ast::Expr::from(value),
    }}
}

impl ScalarValue {
    pub fn ty(&self) -> ScalarType { match self {
        ScalarValue::Int(_) => ScalarType::Int,
        ScalarValue::Float(_) => ScalarType::Float,
        ScalarValue::String(_) => ScalarType::String,
    }}

    /// Allows simulating the effect of e.g. `%INT_VAR` or `$FLOAT_VAR`.
    /// (basically, the game performs typecasts when variables are read as the other type)
    pub fn apply_sigil(self, ty_sigil: Option<ast::VarSigil>) -> Option<ScalarValue> {
        match ty_sigil {
            None => Some(self),
            Some(ast::VarSigil::Int) => self.read_as_int().map(ScalarValue::Int),
            Some(ast::VarSigil::Float) => self.read_as_float().map(ScalarValue::Float),
        }
    }

    /// Obtain an integer value, as if read with a `$` prefix.  (i.e. casting if float)
    ///
    /// Returns `None` for e.g. string values.
    pub fn read_as_int(&self) -> Option<i32> {
        match self {
            &ScalarValue::Int(x) => Some(x),
            &ScalarValue::Float(x) => Some(x as i32),
            &ScalarValue::String(_) => None,
        }
    }

    /// Obtain a float value, as if read with a `%` prefix.  (i.e. casting if integer)
    ///
    /// Returns `None` for e.g. string values.
    pub fn read_as_float(&self) -> Option<f32> {
        match self {
            &ScalarValue::Int(x) => Some(x as f32),
            &ScalarValue::Float(x) => Some(x),
            &ScalarValue::String(_) => None,
        }
    }
}

/// `Display` impl, for ease of use in error messages.
impl fmt::Display for ScalarValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ScalarValue::String(x) => write!(f, "{}", crate::fmt::stringify(x)),
            ScalarValue::Float(x) => write!(f, "{}", crate::fmt::stringify(x)),
            ScalarValue::Int(x) => write!(f, "{}", x),
        }
    }
}

// =============================================================================

/// The type of a value.
///
/// The variants of this directly correspond to [`ScalarValue`].  If you want to add untyped-ness
/// or void-ness as possibilities, see [`VarType`] and [`ExprType`].
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

    pub fn sigil(self) -> Option<ast::VarSigil> {
        ast::VarSigil::from_ty(self)
    }
}

/// Inherent type of a variable, which may be untyped. (but is never void)
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VarType { Untyped, Typed(ScalarType) }

/// The type of an expression, which can be void. (but is never untyped)
///
/// This includes all types that can appear in the abstract language, including strings.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExprType { Void, Value(ScalarType) }

/// The type of a register at a specific read or write site.
///
/// In contrast to [`ExprType`] and [`VarType`], there is only int and float.
// FIXME: historically VarSigil has been 'abused' for this meaning.  At this time however I don't see
//        any compelling reason to split the two up.
pub use ast::VarSigil as ReadType;

impl VarType {
    pub fn as_known_ty(self) -> Option<ScalarType> {
        match self {
            VarType::Typed(ty) => Some(ty),
            VarType::Untyped => None,
        }
    }
}

impl ExprType {
    pub fn as_value_ty(self) -> Option<ScalarType> {
        match self {
            ExprType::Value(ty) => Some(ty),
            ExprType::Void => None,
        }
    }

    pub fn descr(self) -> &'static str {
        match self {
            ExprType::Value(ty) => ty.descr(),
            ExprType::Void => "void",
        }
    }
}

impl From<ScalarType> for VarType {
    fn from(ty: ScalarType) -> Self { VarType::Typed(ty) }
}

impl From<ScalarType> for ExprType {
    fn from(ty: ScalarType) -> Self { ExprType::Value(ty) }
}
