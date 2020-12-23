use lalrpop_util::lalrpop_mod;

use crate::{ast, meta};
use crate::pos::{BytePos, Spanned, Span};

lalrpop_mod!(pub lalrparser, "/parse/lalrparser.rs");
mod lalrparser_util;

use lexer::{Lexer, Token};
pub mod lexer;

pub type ErrorPayload = &'static str; // FIXME: this is the default for LALRPOP
pub type Error<'input> = lalrpop_util::ParseError<BytePos, Token<'input>, ErrorPayload>;
pub type Result<'input, T> = std::result::Result<T, Error<'input>>;

pub trait Parse<'input>: Sized {
    fn parse<B: AsRef<[u8]> + ?Sized>(s: &'input B) -> Result<'input, Self> {
        Self::parse_spanned(s).map(|x| x.value)
    }

    fn parse_spanned<B: AsRef<[u8]> + ?Sized>(s: &'input B) -> Result<'input, Spanned<Self>> {
        let mut state = State::new();
        Self::parse_stream(&mut state, Lexer::new(s.as_ref()))
    }

    fn parse_stream(state: &mut State, lexer: Lexer<'input>) -> Result<'input, Spanned<Self>>;
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
) -> Result<'input, Spanned<AnythingValue>> {
    let offset = BytePos(lexer.offset() as u32);
    let lexer = std::iter::once(Ok((offset, Token::VirtualDispatch(tag), offset))).chain(lexer);
    lalrparser::AnythingParser::new().parse(state, lexer)
}


macro_rules! impl_parse {
    ($AstType:ty, $TagName:ident) => {
        impl<'input> Parse<'input> for $AstType {
            fn parse_stream(state: &mut State, lexer: Lexer<'input>) -> Result<'input, Spanned<Self>> {
                Ok(call_anything_parser(AnythingTag::$TagName, state, lexer)?.map(|x| match x {
                    AnythingValue::$TagName(x) => x,
                    _ => unreachable!(),
                }))
            }
        }
    }
}

impl_parse!(ast::Script, Script);
impl_parse!(ast::Item, Item);
impl_parse!(ast::Stmt, Stmt);
impl_parse!(ast::Expr, Expr);
impl_parse!(ast::Var, Var);
impl_parse!(ast::LitString, LitString);
impl_parse!(meta::Meta, Meta);
