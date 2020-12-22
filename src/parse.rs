use crate::lalrparser;
use crate::{ast, meta};
use crate::lexer::{Lexer, Token};
use crate::pos::BytePos;

pub type ErrorPayload = &'static str; // FIXME: this is the default for LALRPOP
pub type Error<'input> = lalrpop_util::ParseError<BytePos, Token<'input>, ErrorPayload>;
pub type Result<'input, T> = std::result::Result<T, Error<'input>>;

pub trait Parse<'input>: Sized {
    fn parse<B: AsRef<[u8]> + ?Sized>(s: &'input B) -> Result<'input, Self> {
        let mut state = State::new();
        Self::parse_stream(&mut state, Lexer::new(s.as_ref()))
    }

    fn parse_stream(state: &mut State, lexer: Lexer<'input>) -> Result<'input, Self>;
}

/// Extra state during parsing.
pub struct State {
    /// When we are parsing instructions, tracks the last time label so that we can produce an
    /// AST with time fields instead of explicit labels.
    ///
    /// A stack is used *as if* we supported nested function definitions.  In practice, the level at
    /// index 0 gets used exclusively when parsing `Stmt` at toplevel, and a level at index 1 gets
    /// used when parsing `Item`s.
    pub time_stack: Vec<i32>,
}

impl State {
    pub fn new() -> State { State {
        time_stack: vec![0],
    }}
}

impl Default for State {
    fn default() -> State { Self::new() }
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
    LitString,
    Meta,
}

// Inserts the virtual token and calls the Anything parser
fn call_anything_parser<'input>(
    tag: AnythingTag,
    state: &mut State,
    lexer: Lexer<'input>,
) -> Result<'input, AnythingValue> {
    let offset = BytePos(lexer.offset() as u32);
    let lexer = std::iter::once(Ok((offset, Token::VirtualDispatch(tag), offset))).chain(lexer);
    lalrparser::AnythingParser::new().parse(state, lexer)
}

impl<'input> Parse<'input> for ast::Script {
    fn parse_stream(state: &mut State, lexer: Lexer<'input>) -> Result<'input, Self> {
        match call_anything_parser(AnythingTag::Script, state, lexer)? {
            AnythingValue::Script(x) => Ok(x),
            _ => unreachable!(),
        }
    }
}

impl<'input> Parse<'input> for ast::Item {
    fn parse_stream(state: &mut State, lexer: Lexer<'input>) -> Result<'input, Self> {
        match call_anything_parser(AnythingTag::Item, state, lexer)? {
            AnythingValue::Item(x) => Ok(x),
            _ => unreachable!(),
        }
    }
}

impl<'input> Parse<'input> for ast::Stmt {
    fn parse_stream(state: &mut State, lexer: Lexer<'input>) -> Result<'input, Self> {
        match call_anything_parser(AnythingTag::Stmt, state, lexer)? {
            AnythingValue::Stmt(x) => Ok(x),
            _ => unreachable!(),
        }
    }
}

impl<'input> Parse<'input> for ast::Expr {
    fn parse_stream(state: &mut State, lexer: Lexer<'input>) -> Result<'input, Self> {
        match call_anything_parser(AnythingTag::Expr, state, lexer)? {
            AnythingValue::Expr(x) => Ok(x),
            _ => unreachable!(),
        }
    }
}

impl<'input> Parse<'input> for ast::Var {
    fn parse_stream(state: &mut State, lexer: Lexer<'input>) -> Result<'input, Self> {
        match call_anything_parser(AnythingTag::Var, state, lexer)? {
            AnythingValue::Var(x) => Ok(x),
            _ => unreachable!(),
        }
    }
}

impl<'input> Parse<'input> for ast::LitString {
    fn parse_stream(state: &mut State, lexer: Lexer<'input>) -> Result<'input, Self> {
        match call_anything_parser(AnythingTag::LitString, state, lexer)? {
            AnythingValue::LitString(x) => Ok(x),
            _ => unreachable!(),
        }
    }
}

impl<'input> Parse<'input> for meta::Meta {
    fn parse_stream(state: &mut State, lexer: Lexer<'input>) -> Result<'input, Self> {
        match call_anything_parser(AnythingTag::Meta, state, lexer)? {
            AnythingValue::Meta(x) => Ok(x),
            _ => unreachable!(),
        }
    }
}
