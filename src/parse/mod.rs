use lalrpop_util::lalrpop_mod;

use crate::diagnostic::Diagnostic;
use crate::ast;
use crate::pos::{Sp, Span};

pub mod lalrparser_util;

lalrpop_mod!(pub lalrparser, "/parse/lalrparser.rs");

pub mod abi {
    use super::*;
    lalrpop_mod!(generated, "/parse/abi.rs");

    // AbiParser uses lalrpop's default lexer, which apparently takes an ABSURD amount
    // of time to construct.  Cache it.
    lazy_static::lazy_static! {
        pub(crate) static ref PARSER: generated::AbiParser = generated::AbiParser::new();
    }
}

use lexer::{Lexer, Token};
pub mod lexer;

pub mod seqmap;

#[cfg(test)]
mod tests;

pub trait Parse: Sized {
    /// Parse a string into an AST node.
    ///
    /// This is for quick-and-dirty use only; the spans in the output will have incomplete
    /// information and [`crate::Files`] will be unable to locate the corresponding
    /// strings of text. For proper diagnostics you should prefer the helper method
    /// [`crate::api::Truth::parse`] instead.
    fn parse<B: AsRef<str> + ?Sized>(s: &B) -> Result<'_, Self> {
        State::scope(|mut state| {
            Self::parse_stream(&mut state, Lexer::new(None, s.as_ref()))
                .map(|x| x.value)
        })
    }

    /// Parse from lexed tokens, producing an AST node with correct span info.
    fn parse_stream<'input>(state: &mut State, lexer: Lexer<'input>) -> Result<'input, Sp<Self>>;
}


pub type Error<'input> = lalrpop_util::ParseError<lexer::Location, Token<'input>, Diagnostic>;
pub type Result<'input, T> = std::result::Result<T, Error<'input>>;


/// Extra state during parsing.
pub struct State<'a, 'b> {
    mapfiles: Vec<Sp<ast::LitString>>,
    image_sources: Vec<Sp<ast::LitString>>,
    owner: qcell::LCellOwner<'b>,
    pools: &'a StatePools<'b>,
}

#[derive(Default)]
pub struct StatePools<'a> {
    stmt_kind: crate::pool::Pool<'a, ast::StmtKind>,
    stmt: crate::pool::Pool<'a, ast::Stmt>,
}

impl State<'static, 'static> {
    pub fn scope<T>(func: impl for<'a, 'b> FnOnce(State<'a, 'b>) -> T) -> T {
        // FIXME why doesn't qcell::LCellOwner::scope return a value
        let mut out = None;
        qcell::LCellOwner::scope(|owner| {
            let pools = Default::default();
            let value = func(State {
                mapfiles: Default::default(),
                image_sources: Default::default(),
                pools: &pools,
                owner,
            });
            out = Some(value);
        });
        out.unwrap()
    }
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
    ScriptFile(Box<ast::ScriptFile>),
    Item(Box<ast::Item>),
    Block(Box<ast::Block>),
    Stmt(Box<ast::Stmt>),
    Expr(Box<ast::Expr>),
    Var(Box<ast::Var>),
    Meta(Box<ast::Meta>),
    LitString(Box<ast::LitString>),
}

/// Implementation detail of the [`Parse`] trait.  Use that instead.
#[doc(hidden)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AnythingTag {
    ScriptFile,
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
                    AnythingValue::$TagName(x) => *x,
                    _ => unreachable!(),
                }))
            }
        }
    }
}

impl_parse!(ast::ScriptFile, ScriptFile);
impl_parse!(ast::Item, Item);
impl_parse!(ast::Block, Block);
impl_parse!(ast::Stmt, Stmt);
impl_parse!(ast::Expr, Expr);
impl_parse!(ast::Var, Var);
impl_parse!(ast::LitString, LitString);
impl_parse!(ast::Meta, Meta);
