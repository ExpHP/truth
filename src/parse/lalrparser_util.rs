//! Helper functions that ideally would have been defined inside the grammar file, but aren't
//! because they can't (?) be defined there.

use std::str::FromStr;

use crate::pos::Sp;
use crate::ast;
use crate::error::CompileError;

/// Uses `FromStr` to parse something from a byte string.
///
/// This is only intended for use where the input is known in advance
/// to only contain ASCII, and may panic in other cases.
pub fn parse_ascii<B: AsRef<[u8]> + ?Sized, T: FromStr>(b: &B) -> Result<T, T::Err> {
    parse_utf8(b)
}

/// Uses `FromStr` to parse something from a byte string.
///
/// This is only intended for use where the input is known in advance
/// to contain valid UTF-8, and may panic in other cases.
pub fn parse_utf8<B: AsRef<[u8]> + ?Sized, T: FromStr>(b: &B) -> Result<T, T::Err> {
    std::str::from_utf8(b.as_ref()).expect("invalid utf-8!").parse()
}

/// Parses a `u32` from a byte string.
pub fn u32_from_ascii_radix<B: AsRef<[u8]> + ?Sized>(b: &B, radix: u32) -> Result<u32, std::num::ParseIntError> {
    u32::from_str_radix(std::str::from_utf8(b.as_ref()).expect("invalid utf-8!"), radix)
}

pub fn push<T>(mut vec: Vec<T>, item: T) -> Vec<T> {
    vec.push(item);
    vec
}

pub enum Either<A, B> { This(A), That(B) }

// FIXME:  Change these to stuff like the following after https://github.com/lalrpop/lalrpop/pull/594 is merged
// #[inline]
// VarTypeKeyword: ast::TypeKeyword = {
//    <keyword:Sp<TypeKeyword>> =>? match keyword.value {
//        token![void] => Err(error!(
//            message("void-typed variable"),
//            primary(keyword, "variables must have a value"),
//        ).into()),
//        kw => Ok(kw),
//    },
// };

pub fn func_return_type_keyword(keyword: Sp<ast::TypeKeyword>) -> Result<ast::TypeKeyword, CompileError> {
    match keyword.value {
        token![var] => Err(error!(
            message("var-typed function"),
            primary(keyword, "cannot be used on functions"),
        ).into()),
        kw => Ok(kw),
    }
}

pub fn const_var_type_keyword(keyword: Sp<ast::TypeKeyword>) -> Result<ast::TypeKeyword, CompileError> {
    let keyword = sp!(keyword.span => var_type_keyword(keyword)?);

    if keyword.var_ty().is_none() {
        return Err(error!(
            message("illegal untyped const"),
            primary(keyword, "const vars must have a type"),
        ).into());
    }
    Ok(keyword.value)
}

pub fn local_var_type_keyword(keyword: Sp<ast::TypeKeyword>) -> Result<ast::TypeKeyword, CompileError> {
    let keyword = sp!(keyword.span => var_type_keyword(keyword)?);

    match keyword.value {
        token![string] => Err(error!(
            message("non-const string variable"),
            primary(keyword, "only possible for const vars"),
        ).into()),
        kw => Ok(kw),
    }
}

pub fn var_type_keyword(keyword: Sp<ast::TypeKeyword>) -> Result<ast::TypeKeyword, CompileError> {
    match keyword.value {
        token![void] => Err(error!(
            message("void-typed variable"),
            primary(keyword, "variables must have a value"),
        ).into()),
        kw => Ok(kw),
    }
}
