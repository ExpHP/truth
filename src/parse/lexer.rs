//! We need our own lexer to insert a virtual token at the beginning.
//!
//! Why not use LALRPOP's built-in lexer?  Well, the original reason was that a custom
//! lexer was required to allow Shift-JIS text files, as the default lexer operates on `str`.
//! Now that truth also requires UTF-8, the only real reason this still exists is because
//! I don't see a satisfactory alternative for how to embed the virtual token

use crate::diagnostic::Diagnostic;
use crate::pos::{FileId, BytePos, SourceStr};

define_token_enum! {
    #[derive(logos::Logos, Clone, Copy, Debug, PartialEq)]
    #[logos(extras = LexerExtras)]
    pub enum Token<'a> {
        #[token(",")] Comma,
        #[token("?")] Question,
        #[token(":")] Colon,
        #[token(";")] Semicolon,
        #[token("[")] BracketOpen,
        #[token("]")] BracketClose,
        #[token("{")] BraceOpen,
        #[token("}")] BraceClose,
        #[token("(")] ParenOpen,
        #[token(")")] ParenClose,
        #[token("@")] AtSign,
        #[token("...")] Ellipsis,
        #[token(".")] Dot,
        #[token("=")] Eq,
        #[token("+")] Plus,
        #[token("-")] Minus,
        #[token("*")] Star,
        #[token("/")] Slash,
        #[token("%")] Percent,
        #[token("^")] Caret,
        #[token("|")] Or,
        #[token("&")] And,
        #[token("~")] Tilde,
        #[token("+=")] PlusEq,
        #[token("-=")] MinusEq,
        #[token("*=")] StarEq,
        #[token("/=")] SlashEq,
        #[token("%=")] PercentEq,
        #[token("^=")] CaretEq,
        #[token("|=")] OrEq,
        #[token("&=")] AndEq,
        #[token("==")] EqEq,
        #[token("!=")] NotEq,
        #[token("<")] Less,
        #[token("<=")] LessEq,
        #[token(">")] Greater,
        #[token(">=")] GreaterEq,
        #[token("<<")] LessLess,
        #[token(">>")] GreaterGreater,
        #[token(">>>")] GreaterGreaterGreater,
        #[token("<<=")] LessLessEq,
        #[token(">>=")] GreaterGreaterEq,
        #[token(">>>=")] GreaterGreaterGreaterEq,
        #[token("!")] Not,
        #[token("||")] OrOr,
        #[token("&&")] AndAnd,
        #[token("--")] MinusMinus,
        #[token("++")] PlusPlus,
        #[token("$")] Cash,
        #[token("#")] Hash,
        #[token("anim")] Anim,
        #[token("ecli")] Ecli,
        #[token("meta")] Meta,
        #[token("sub")] Sub,
        #[token("script")] Script,
        #[token("entry")] Entry,
        #[token("var")] Var,
        #[token("int")] Int,
        #[token("float")] Float,
        #[token("string")] String,
        #[token("void")] Void,
        #[token("const")] Const,
        #[token("inline")] Inline,
        #[token("insdef")] Insdef,
        #[token("return")] Return,
        #[token("goto")] Goto,
        #[token("loop")] Loop,
        #[token("if")] If,
        #[token("else")] Else,
        #[token("unless")] Unless,
        #[token("do")] Do,
        #[token("while")] While,
        #[token("times")] Times,
        #[token("break")] Break,
        #[token("switch")] Switch,
        #[token("case")] Case,
        #[token("default")] Default,
        #[token("interrupt")] Interrupt,
        #[token("async")] Async,
        #[token("global")] Global,
        #[token("pragma")] Pragma,
        #[token("mapfile")] Mapfile,
        #[token("image_source")] ImageSource,
        #[token("offsetof")] OffsetOf,
        #[token("timeof")] TimeOf,
        #[token("sin")] Sin,
        #[token("cos")] Cos,
        #[token("tan")] Tan,
        #[token("asin")] Asin,
        #[token("acos")] Acos,
        #[token("atan")] Atan,
        #[token("sqrt")] Sqrt,
        #[token("_S")] LegacyEncodeI,
        #[token("_f")] LegacyEncodeF,
        #[token("REG")] Reg,

        #[regex(r##""([^\\"]|\\.)*""##)] LitString(&'a str),
        #[regex(r##"[0-9]+(\.([0-9]*f|[0-9]+)|f)"##)] LitFloat(&'a str),
        #[regex(r##"rad\([-+]?[0-9]+(\.([0-9]*f|[0-9]+)|f)?\)"##)] LitRad(&'a str),
        #[regex(r##"[0-9]+|0[xX][0-9a-fA-F]+|0[bB][0-1]+"##)] LitInt(&'a str),
        #[regex(r##"![-*ENHLWXYZO4567]+"##)] DifficultyStr(&'a str),
        #[regex(r##"ins_[a-zA-Z0-9_]*"##)] Instr(&'a str),
        #[regex(r##"[a-zA-Z_][a-zA-Z0-9_]*"##)] Ident(&'a str),

        #[error]
        #[regex(r##"\s+"##, skip_comment_or_ws)] // whitespace
        #[regex(r##"//[^\n\r]*[\n\r]*"##, skip_comment_or_ws)] // line comment
        #[regex(r##"/\*([^*]|\**[^*/])*\*+/"##, skip_comment_or_ws)] // block comment
        #[regex(r##"/\*([^*]|\*+[^*/])*\*?"##)] // unclosed block comment
        #[doc(hidden)]
        /// Implementation detail. Basically, [`logos`] requires an error variant.
        /// [`Lexer`] never actually produces this variant, returning `Result::Err` instead.
        Error,

        /// Implementation detail. A virtual token used to select a nonterminal to parse.
        /// (part of a workaround to reduce LALRPOP output size)
        #[doc(hidden)]
        VirtualDispatch(crate::parse::AnythingTag),
    }
}

pub type Lexer<'input> = GenericLexer<'input, Token<'input>>;

#[derive(Default)]
pub struct LexerExtras {
    /// Records whether a comment or whitespace was ever encountered.
    had_comment_or_ws: bool,
}

fn skip_comment_or_ws<'a>(lexer: &mut logos::Lexer<'a, Token<'a>>) -> logos::Skip {
    lexer.extras.had_comment_or_ws = true;
    logos::Skip
}

/// truth's lexer.
///
/// You should not need to use this type; the primary API for parsing code in truth
/// is provided by [`crate::pos::NonUtf8Files::parse`].
pub struct GenericLexer<'input, Tok>
where
    Tok: logos::Logos<'input>,
{
    file_id: FileId,
    /// Starting offset of the input source relative to the beginning of the file.
    /// This should be added to byte positions derived from logos.
    initial_offset: usize,
    imp: logos::Lexer<'input, Tok>,
}

impl<'input, Tok: logos::Logos<'input, Source=str>> GenericLexer<'input, Tok> {
    pub fn new(input: SourceStr<'input>) -> GenericLexer<'input, Tok>
    where
        <Tok as logos::Logos<'input>>::Extras: Default
    {
        GenericLexer {
            file_id: input.span().file_id,
            initial_offset: input.span().start.into(),
            imp: logos::Lexer::new(input.str),
        }
    }

    pub fn location(&self) -> Location {
        self.location_from_logos_offset(self.imp.span().end as u32)
    }
}

impl<'input, Tok: logos::Logos<'input>> GenericLexer<'input, Tok> {
    fn location_from_logos_offset(&self, logos_offset: u32) -> Location {
        (self.file_id, BytePos(self.initial_offset as u32 + logos_offset))
    }
}

/// Methods for the primary lexer.
impl<'input> Lexer<'input> {
    /// Returns `true` if the lexer has ever encountered (and skipped over) a comment or whitespace.
    pub fn had_comment_or_ws(&self) -> bool {
        self.imp.extras.had_comment_or_ws
    }
}

/// The location type reported to LALRPOP.
///
/// This type only exists because LALRPOP needs a type to represent a single point in the source code,
/// and generally speaking these are converted into the more common [`crate::pos::Span`] type as soon
/// as reasonably possible.
pub type Location = (FileId, BytePos);

impl<'a, Tok: logos::Logos<'a> + PartialEq> Iterator for GenericLexer<'a, Tok> {
    type Item = Result<(Location, Tok, Location), Diagnostic>;

    fn next(&mut self) -> Option<Self::Item> {
        self.imp.next().map(|token| {
            let range = self.imp.span();
            let start = self.location_from_logos_offset(range.start as _);
            let end = self.location_from_logos_offset(range.end as _);
            if token == Tok::ERROR {
                Err(error!(
                    message("invalid token"),
                    primary(crate::pos::Span::from_locs(start, end), "invalid token"),
                ))
            } else {
                Ok((start, token, end))
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tokenize(s: &str) -> Vec<(BytePos, Token<'_>, BytePos)> {
        GenericLexer::<Token<'_>>::new(SourceStr::new_null(s.as_ref()))
            .map(|res| res.unwrap())
            .map(|(start, tok, end)| (start.1, tok, end.1))
            .collect::<Vec<_>>()
    }

    #[test]
    fn ident_vs_keyword() {
        let p = BytePos;
        assert_eq!(tokenize("int"), vec![(p(0), Token::Int, p(3))]);
        assert_eq!(tokenize("intint"), vec![(p(0), Token::Ident("intint".as_ref()), p(6))]);
        assert_eq!(tokenize("int int"), vec![(p(0), Token::Int, p(3)), (p(4), Token::Int, p(7))]);
    }

    #[test]
    fn no_whitespace() {
        let p = BytePos;
        assert_eq!(tokenize("+("), vec![(p(0), Token::Plus, p(1)), (p(1), Token::ParenOpen, p(2))]);
    }

    #[test]
    fn whitespace_at_end() {
        let p = BytePos;
        assert_eq!(tokenize("+ "), vec![(p(0), Token::Plus, p(1))]);
    }

    #[test]
    fn multi_whitespace() {
        let p = BytePos;
        assert_eq!(
            tokenize("  \r\n  /* lol */ // \n\n\n 32"),
            vec![(p(23), Token::LitInt("32".as_ref()), p(25))],
        );
    }

    #[test]
    fn multiline_comment() {
        let p = BytePos;
        assert_eq!(
            tokenize("1 /* lol **/ 2 /** //lol */ 3"), vec![
                (p(0), Token::LitInt("1".as_ref()), p(1)),
                (p(13), Token::LitInt("2".as_ref()), p(14)),
                (p(28), Token::LitInt("3".as_ref()), p(29)),
            ],
        );
    }

    #[test]
    fn ins() {
        let p = BytePos;
        assert_eq!(
            tokenize("ins_23  ins_x"),
            vec![
                (p(0), Token::Instr("ins_23".as_ref()), p(6)),
                (p(8), Token::Instr("ins_x".as_ref()), p(13)),
            ],
        );
    }
}
