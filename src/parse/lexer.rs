//! We need our own lexer to insert a virtual token at the beginning.
//!
//! Why not use LALRPOP's built-in lexer?  Well, the original reason was that a custom
//! lexer was required to allow Shift-JIS text files, as the default lexer operates on `str`.
//! Now that truth also requires UTF-8, the only real reason this still exists is because
//! I don't see a satisfactory alternative for how to embed the virtual token

use std::fmt;

use crate::diagnostic::Diagnostic;
use crate::pos::{FileId, BytePos};

macro_rules! define_token_enum {
    (
        $( #[$($meta:tt)+] )*
        pub enum $Token:ident<$lt:lifetime> {
            $( #[token($fixed_str:literal)] $fixed_variant:ident, )*

            $(
                #[regex($($regex_tt:tt)+)]
                $regex_variant:ident($regex_ty:ty),
            )*

            #[error]
            $( #[ $($error_meta:tt)+ ] )*
            Error,

            $($other_variants:tt)*
        }
    ) => {
        $( #[$($meta)+] )*
        pub enum $Token<$lt> {
            $( #[token($fixed_str)] $fixed_variant, )*

            $( #[regex($($regex_tt)+)] $regex_variant($regex_ty), )*

            #[error]
            $( #[ $($error_meta)+ ] )*
            Error,

            $($other_variants)*
        }

        impl<'input> $Token<'input> {
            pub(super) fn as_str(&self) -> &'input str {
                match self {
                    $( Token::$fixed_variant => $fixed_str, )*
                    $( Token::$regex_variant(str) => str, )*
                    Token::Error => "<invalid>",
                    _ => "<special>",
                }
            }
        }
    };
}

define_token_enum! {
    #[derive(logos::Logos, Clone, Copy, Debug, PartialEq)]
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
        #[token("$")] Cash,
        #[token("#")] Hash,
        #[token("anim")] Anim,
        #[token("ecli")] Ecli,
        #[token("meta")] Meta,
        #[token("sub")] Sub,
        #[token("timeline")] Timeline,
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
        #[token("difficulty")] Difficulty, // FIXME: I don't want this to be a keyword... :/
        #[token("async")] Async,
        #[token("global")] Global,
        #[token("false")] False,
        #[token("true")] True,
        #[token("pragma")] Pragma,
        #[token("mapfile")] Mapfile,
        #[token("image_source")] ImageSource,
        #[token("offsetof")] OffsetOf,
        #[token("timeof")] TimeOf,
        #[token("sin")] Sin,
        #[token("cos")] Cos,
        #[token("sqrt")] Sqrt,
        #[token("_S")] CastI,
        #[token("_f")] CastF,
        #[token("REG")] Reg,

        #[regex(r##""([^\\"]|\\.)*""##)] LitString(&'a str),
        #[regex(r##"[0-9]+(\.([0-9]*f|[0-9]+)|f)"##)] LitFloat(&'a str),
        #[regex(r##"rad\([-+]?[0-9]+(\.([0-9]*f|[0-9]+)|f)?\)"##)] LitRad(&'a str),
        #[regex(r##"[0-9]+"##)] LitIntDec(&'a str),
        #[regex(r##"0[xX][0-9a-fA-F]+"##)] LitIntHex(&'a str),
        #[regex(r##"0[bB][0-1]+"##)] LitIntBin(&'a str),
        #[regex(r##"![-*ENHLWXYZO4567]+"##)] DifficultyStr(&'a str),
        #[regex(r##"ins_[a-zA-Z0-9_]*"##)] Instr(&'a str),
        #[regex(r##"[a-zA-Z_][a-zA-Z0-9_]*"##)] Ident(&'a str),

        #[error]
        #[regex(r##"\s+"##, logos::skip)] // whitespace
        #[regex(r##"//[^\n\r]*[\n\r]*"##, logos::skip)] // line comment
        #[regex(r##"/\*([^*]|\**[^*/])*\*+/"##, logos::skip)] // block comment
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

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.as_str(), f)
    }
}

/// truth's lexer.
///
/// You should not need to use this type; the primary API for parsing code in truth
/// is provided by [`crate::pos::NonUtf8Files::parse`].
pub struct Lexer<'input> {
    file_id: FileId,
    offset: usize,
    imp: logos::SpannedIter<'input, Token<'input>>,
}

impl<'input> Lexer<'input> {
    pub fn new(file_id: FileId, input: &'input str) -> Lexer<'input> {
        Lexer {
            file_id,
            offset: 0,
            imp: logos::Lexer::new(input).spanned(),
        }
    }

    pub fn location(&self) -> Location { (self.file_id, BytePos(self.offset as u32)) }
}

/// The location type reported to LALRPOP.
///
/// This type only exists because LALRPOP needs a type to represent a single point in the source code,
/// and generally speaking these are converted into the more common [`crate::pos::Span`] type as soon
/// as reasonably possible.
pub type Location = (FileId, BytePos);

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<(Location, Token<'a>, Location), Diagnostic>;

    fn next(&mut self) -> Option<Self::Item> {
        self.imp.next().map(|(token, range)| {
            let start = (self.file_id, BytePos(range.start as _));
            let end = (self.file_id, BytePos(range.end as _));
            match token {
                Token::Error => Err(error!(
                    message("invalid token"),
                    primary(crate::pos::Span::from_locs(start, end), "invalid token"),
                )),
                token => Ok((start, token, end)),
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tokenize(s: &str) -> Vec<(BytePos, Token<'_>, BytePos)> {
        Lexer::new(None, s.as_ref())
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
            vec![(p(23), Token::LitIntDec("32".as_ref()), p(25))],
        );
    }

    #[test]
    fn multiline_comment() {
        let p = BytePos;
        assert_eq!(
            tokenize("1 /* lol **/ 2 /** //lol */ 3"), vec![
                (p(0), Token::LitIntDec("1".as_ref()), p(1)),
                (p(13), Token::LitIntDec("2".as_ref()), p(14)),
                (p(28), Token::LitIntDec("3".as_ref()), p(29)),
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
