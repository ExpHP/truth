use crate::lalrparser;
use crate::{ast, meta};
use crate::lexer::{Lexer, Token};

pub type ErrorPayload = &'static str; // FIXME: this is the default for LALRPOP
pub type Error<'input> = lalrpop_util::ParseError<usize, Token<'input>, ErrorPayload>;
pub type Result<'input, T> = std::result::Result<T, Error<'input>>;

pub trait Parse<'input>: Sized {
    fn parse<B: AsRef<[u8]> + ?Sized>(s: &'input B) -> Result<'input, Self> {
        Self::parse_stream(Lexer::new(s.as_ref()))
    }

    fn parse_stream(lexer: Lexer<'input>) -> Result<'input, Self>;
}

/// Return type of the LALRPOP `Anything` parser.
///
/// This is only an implementation detail of the [`Parse`] trait.
/// Use that instead.
#[doc(hidden)]
pub enum AnythingValue {
    Script(ast::Script),
    Item(ast::Item),
    Stmt(ast::Stmt),
    Expr(ast::Expr),
    Var(ast::Var),
    Ident(ast::Ident),
    Meta(meta::Meta),
    LitString(ast::LitString),
}

/// Implementation detail of the [`Parse`] trait.  Use that instead.
#[doc(hidden)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AnythingTag {
    Script,
    Item,
    Stmt,
    Expr,
    Var,
    Ident,
    LitString,
    Meta,
}

// Inserts the virtual token and calls the Anything parser
fn call_anything_parser(tag: AnythingTag, lexer: Lexer<'_>) -> Result<'_, AnythingValue> {
    let offset = lexer.offset();
    let lexer = std::iter::once(Ok((offset, Token::VirtualDispatch(tag), offset))).chain(lexer);
    lalrparser::AnythingParser::new().parse(lexer)
}

impl<'input> Parse<'input> for ast::Script {
    fn parse_stream(lexer: Lexer<'input>) -> Result<'input, Self> {
        match call_anything_parser(AnythingTag::Script, lexer)? {
            AnythingValue::Script(x) => Ok(x),
            _ => unreachable!(),
        }
    }
}

impl<'input> Parse<'input> for ast::Item {
    fn parse_stream(lexer: Lexer<'input>) -> Result<'input, Self> {
        match call_anything_parser(AnythingTag::Item, lexer)? {
            AnythingValue::Item(x) => Ok(x),
            _ => unreachable!(),
        }
    }
}

impl<'input> Parse<'input> for ast::Stmt {
    fn parse_stream(lexer: Lexer<'input>) -> Result<'input, Self> {
        match call_anything_parser(AnythingTag::Stmt, lexer)? {
            AnythingValue::Stmt(x) => Ok(x),
            _ => unreachable!(),
        }
    }
}

impl<'input> Parse<'input> for ast::Expr {
    fn parse_stream(lexer: Lexer<'input>) -> Result<'input, Self> {
        match call_anything_parser(AnythingTag::Expr, lexer)? {
            AnythingValue::Expr(x) => Ok(x),
            _ => unreachable!(),
        }
    }
}

impl<'input> Parse<'input> for ast::Var {
    fn parse_stream(lexer: Lexer<'input>) -> Result<'input, Self> {
        match call_anything_parser(AnythingTag::Var, lexer)? {
            AnythingValue::Var(x) => Ok(x),
            _ => unreachable!(),
        }
    }
}

impl<'input> Parse<'input> for ast::Ident {
    fn parse_stream(lexer: Lexer<'input>) -> Result<'input, Self> {
        match call_anything_parser(AnythingTag::Ident, lexer)? {
            AnythingValue::Ident(x) => Ok(x),
            _ => unreachable!(),
        }
    }
}

impl<'input> Parse<'input> for ast::LitString {
    fn parse_stream(lexer: Lexer<'input>) -> Result<'input, Self> {
        match call_anything_parser(AnythingTag::LitString, lexer)? {
            AnythingValue::LitString(x) => Ok(x),
            _ => unreachable!(),
        }
    }
}

impl<'input> Parse<'input> for meta::Meta {
    fn parse_stream(lexer: Lexer<'input>) -> Result<'input, Self> {
        match call_anything_parser(AnythingTag::Meta, lexer)? {
            AnythingValue::Meta(x) => Ok(x),
            _ => unreachable!(),
        }
    }
}
