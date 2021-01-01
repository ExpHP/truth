use lalrpop_util::lalrpop_mod;

use crate::{ast, meta};
use crate::pos::{BytePos, Sp, FileId};

lalrpop_mod!(pub lalrparser, "/parse/lalrparser.rs");
mod lalrparser_util;

use lexer::{Lexer, Token};
pub mod lexer;

pub type ErrorPayload = &'static str; // FIXME: this is the default for LALRPOP
pub type Error<'input> = lalrpop_util::ParseError<BytePos, Token<'input>, ErrorPayload>;
pub type Result<'input, T> = std::result::Result<T, Error<'input>>;

pub trait Parse<'input>: Sized {
    /// Parse a string into an AST node.
    ///
    /// This is for quick-and-dirty use only; the spans in the output will have incomplete
    /// information and [`crate::pos::Files`] will be unable to locate the corresponding
    /// strings of text. For proper diagnostics you should prefer the helper method
    /// [`crate::pos::Files::parse`] instead.
    fn parse<B: AsRef<[u8]> + ?Sized>(s: &'input B) -> Result<'input, Self> {
        let mut state = State::new(None);
        Self::parse_stream(&mut state, Lexer::new(s.as_ref()))
            .map(|x| x.value)
    }

    fn parse_stream(state: &mut State, lexer: Lexer<'input>) -> Result<'input, Sp<Self>>;
}

/// Extra state during parsing.
pub struct State {
    file_id: FileId,
    mapfiles: Vec<Sp<ast::LitString>>,

    /// When we are parsing instructions, tracks the last time label so that we can produce an
    /// AST with time fields instead of explicit labels.
    ///
    /// A stack is used *as if* we supported nested function definitions.  In practice, the level at
    /// index 0 gets used exclusively when parsing `Stmt` at toplevel, and a level at index 1 gets
    /// used when parsing `Item`s.
    time_stack: Vec<i32>,
}

impl State {
    pub fn new(file_id: FileId) -> State { State {
        file_id,
        mapfiles: vec![],
        time_stack: vec![0],
    }}
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
) -> Result<'input, Sp<AnythingValue>> {
    let offset = BytePos(lexer.offset() as u32);
    let lexer = std::iter::once(Ok((offset, Token::VirtualDispatch(tag), offset))).chain(lexer);
    lalrparser::AnythingParser::new().parse(state, lexer)
}


macro_rules! impl_parse {
    ($AstType:ty, $TagName:ident) => {
        impl<'input> Parse<'input> for $AstType {
            fn parse_stream(state: &mut State, lexer: Lexer<'input>) -> Result<'input, Sp<Self>> {
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
