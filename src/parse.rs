use crate::parser;
use crate::ast;
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

impl<'input> Parse<'input> for ast::Var {
    fn parse_stream(lexer: Lexer<'input>) -> Result<'input, Self> {
        parser::VarParser::new().parse(lexer) // FIXME lifetime
    }
}

impl<'input> Parse<'input> for ast::Expr {
    fn parse_stream(lexer: Lexer<'input>) -> Result<'input, Self> {
        parser::ExprParser::new().parse(lexer).map(|x| *x)
    }
}
