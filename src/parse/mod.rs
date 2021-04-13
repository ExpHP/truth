use lalrpop_util::lalrpop_mod;

use crate::diagnostic::Diagnostic;
use crate::ast;
use crate::meta;
use crate::pos::{Sp, Span};

lalrpop_mod!(pub lalrparser, "/parse/lalrparser.rs");
lalrpop_mod!(pub abi, "/parse/abi.rs");
mod lalrparser_util;

use lexer::{Lexer, Token};
pub mod lexer;

#[cfg(test)]
mod tests;

pub trait Parse: Sized {
    /// Parse a string into an AST node.
    ///
    /// This is for quick-and-dirty use only; the spans in the output will have incomplete
    /// information and [`crate::Files`] will be unable to locate the corresponding
    /// strings of text. For proper diagnostics you should prefer the helper method
    /// [`crate::pos::NonUtf8Files::parse`] instead.
    fn parse<B: AsRef<str> + ?Sized>(s: &B) -> Result<'_, Self> {
        let mut state = State::new();
        Self::parse_stream(&mut state, Lexer::new(None, s.as_ref()))
            .map(|x| x.value)
    }

    fn parse_stream<'input>(state: &mut State, lexer: Lexer<'input>) -> Result<'input, Sp<Self>>;
}


pub type Error<'input> = lalrpop_util::ParseError<lexer::Location, Token<'input>, Diagnostic>;
pub type Result<'input, T> = std::result::Result<T, Error<'input>>;


/// Extra state during parsing.
pub struct State {
    mapfiles: Vec<Sp<ast::LitString>>,
    image_sources: Vec<Sp<ast::LitString>>,

    /// When we are parsing instructions, tracks the last time label so that we can produce an
    /// AST with time fields instead of explicit labels.
    ///
    /// It is a stack in order to support nested function definitions.
    time_stack: Vec<i32>,
}

impl State {
    pub fn new() -> State { State {
        mapfiles: vec![],
        image_sources: vec![],
        time_stack: vec![0],
    }}
}

impl crate::diagnostic::IntoDiagnostics for Error<'_> {
    fn into_diagnostics(self) -> Vec<crate::diagnostic::Diagnostic> {
        use lalrpop_util::ParseError::*;

        match self {
            User { error } => vec![error],
            UnrecognizedEOF { location, ref expected } => vec![error!(
                message("unexpected EOF"),
                primary(Span::from_locs(location, location), "unexpected EOF"),
                note("{}", DisplayExpected(expected)),
            )],
            UnrecognizedToken { token: (start, token, end), ref expected } => vec![error!(
                message("unexpected token `{}`", token),
                primary(Span::from_locs(start, end), "unexpected token"),
                note("{}", DisplayExpected(expected)),
            )],
            ExtraToken { token: (start, token, end) } => vec![error!(
                message("unexpected extra token `{}`", token),
                primary(Span::from_locs(start, end), "extra token"),
            )],
            InvalidToken { .. } => unreachable!("we don't use lalrpop's lexer"),
        }
    }
}

struct DisplayExpected<'a>(&'a [String]);
impl std::fmt::Display for DisplayExpected<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // copied from lalrpop_util
        if !self.0.is_empty() {
            writeln!(f)?;
            for (i, e) in self.0.iter().enumerate() {
                let sep = match i {
                    0 => "Expected one of",
                    _ if i < self.0.len() - 1 => ",",
                    // Last expected message to be written
                    _ => " or",
                };
                write!(f, "{} {}", sep, e)?;
            }
        }
        Ok(())
    }
}

/// Return type of the LALRPOP `Anything` parser.
///
/// This is only an implementation detail of the [`Parse`] trait.
/// Use that instead.
#[doc(hidden)]
pub enum AnythingValue {
    Script(ast::Script),
    Item(ast::Item),
    Block(ast::Block),
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
    Block,
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
    let start = lexer.location();
    let lexer = std::iter::once(Ok((start, Token::VirtualDispatch(tag), start))).chain(lexer);
    lalrparser::AnythingParser::new().parse(state, lexer)
}


macro_rules! impl_parse {
    ($AstType:ty, $TagName:ident) => {
        impl Parse for $AstType {
            fn parse_stream<'input>(state: &mut State, lexer: Lexer<'input>) -> Result<'input, Sp<Self>> {
                let sp = call_anything_parser(AnythingTag::$TagName, state, lexer)?;
                Ok(sp!(sp.span => match sp.value {
                    AnythingValue::$TagName(x) => x,
                    _ => unreachable!(),
                }))
            }
        }
    }
}

impl_parse!(ast::Script, Script);
impl_parse!(ast::Item, Item);
impl_parse!(ast::Block, Block);
impl_parse!(ast::Stmt, Stmt);
impl_parse!(ast::Expr, Expr);
impl_parse!(ast::Var, Var);
impl_parse!(ast::LitString, LitString);
impl_parse!(meta::Meta, Meta);
