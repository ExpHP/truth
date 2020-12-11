use crate::{parser, ast};

pub type Error<'input> = lalrpop_util::ParseError<usize, parser::Token<'input>, &'static str>;
pub type Result<'input, T> = std::result::Result<T, Error<'input>>;
pub trait Parse<'input>: Sized {
    fn parse(s: &'input str) -> Result<'input, Self>;
}

impl<'input> Parse<'input> for ast::Var {
    fn parse(s: &'input str) -> Result<'input, Self> {
        parser::VarParser::new().parse(s)
    }
}

impl<'input> Parse<'input> for ast::Expr {
    fn parse(s: &'input str) -> Result<'input, Self> {
        parser::ExprParser::new().parse(s).map(|x| *x)
    }
}
