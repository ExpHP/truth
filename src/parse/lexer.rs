//! Because LALRPOP's default lexer requires UTF-8 (and ECL script files may
//! instead be encoded in Shift-JIS), we need to use our own lexer.

use std::fmt;
use bstr::{BStr, ByteSlice};

use crate::pos::{FileId, BytePos};
use crate::error::CompileError;

macro_rules! define_token_enum {
    (
        $( #[$($meta:tt)+] )*
        pub enum $Token:ident<$lt:lifetime> {
            $( #[token($fixed_bstr:literal)] $fixed_variant:ident, )*

            $(
                #[regex($regex_bstr:literal)]
                $regex_variant:ident($regex_ty:ty),
            )*

            #[error]
            $( #[ $($error_meta:tt)+ ] )*
            Error,

            $($other_variants:tt)*
        }
    ) => {
        $( #[$($meta)+] )*
        pub enum Token<'a> {
            $( #[token($fixed_bstr)] $fixed_variant, )*

            $( #[regex($regex_bstr, |lex| lex.slice().as_bstr())] $regex_variant($regex_ty), )*

            #[error]
            $( #[ $($error_meta)+ ] )*
            Error,

            $($other_variants)*
        }

        impl<'input> Token<'input> {
            pub(super) fn as_bstr(&self) -> &'input BStr {
                match self {
                    $( Token::$fixed_variant => $fixed_bstr.as_bstr(), )*
                    $( Token::$regex_variant(bstr) => bstr, )*
                    Token::Error => b"<invalid>".as_bstr(),
                    _ => b"<special>".as_bstr(),
                }
            }
        }
    };
}

define_token_enum! {
    #[derive(logos::Logos, Clone, Copy, Debug, PartialEq)]
    pub enum Token<'a> {
        #[token(b",")] Comma,
        #[token(b"?")] Question,
        #[token(b":")] Colon,
        #[token(b";")] Semicolon,
        #[token(b"[")] BracketOpen,
        #[token(b"]")] BracketClose,
        #[token(b"{")] BraceOpen,
        #[token(b"}")] BraceClose,
        #[token(b"(")] ParenOpen,
        #[token(b")")] ParenClose,
        #[token(b"@")] AtSign,
        #[token(b"...")] Ellipsis,
        #[token(b".")] Dot,
        #[token(b"=")] Eq,
        #[token(b"+")] Plus,
        #[token(b"-")] Minus,
        #[token(b"*")] Star,
        #[token(b"/")] Slash,
        #[token(b"%")] Percent,
        #[token(b"^")] Caret,
        #[token(b"|")] Or,
        #[token(b"&")] And,
        #[token(b"+=")] PlusEq,
        #[token(b"-=")] MinusEq,
        #[token(b"*=")] StarEq,
        #[token(b"/=")] SlashEq,
        #[token(b"%=")] PercentEq,
        #[token(b"^=")] CaretEq,
        #[token(b"|=")] OrEq,
        #[token(b"&=")] AndEq,
        #[token(b"==")] EqEq,
        #[token(b"!=")] NotEq,
        #[token(b"<")] Less,
        #[token(b"<=")] LessEq,
        #[token(b">")] Greater,
        #[token(b">=")] GreaterEq,
        #[token(b"!")] Not,
        #[token(b"||")] OrOr,
        #[token(b"&&")] AndAnd,
        #[token(b"--")] MinusMinus,
        #[token(b"$")] Cash,
        #[token(b"#")] Hash,
        #[token(b"anim")] Anim,
        #[token(b"ecli")] Ecli,
        #[token(b"meta")] Meta,
        #[token(b"sub")] Sub,
        #[token(b"timeline")] Timeline,
        #[token(b"script")] Script,
        #[token(b"entry")] Entry,
        #[token(b"var")] Var,
        #[token(b"int")] Int,
        #[token(b"float")] Float,
        #[token(b"void")] Void,
        #[token(b"inline")] Inline,
        #[token(b"insdef")] Insdef,
        #[token(b"return")] Return,
        #[token(b"goto")] Goto,
        #[token(b"loop")] Loop,
        #[token(b"if")] If,
        #[token(b"else")] Else,
        #[token(b"unless")] Unless,
        #[token(b"do")] Do,
        #[token(b"while")] While,
        #[token(b"times")] Times,
        #[token(b"break")] Break,
        #[token(b"switch")] Switch,
        #[token(b"case")] Case,
        #[token(b"default")] Default,
        #[token(b"interrupt")] Interrupt,
        #[token(b"async")] Async,
        #[token(b"global")] Global,
        #[token(b"false")] False,
        #[token(b"true")] True,
        #[token(b"pragma")] Pragma,
        #[token(b"mapfile")] Mapfile,
        #[token(b"image_source")] ImageSource,
        #[token(b"sin")] Sin,
        #[token(b"cos")] Cos,
        #[token(b"sqrt")] Sqrt,
        #[token(b"_S")] CastI,
        #[token(b"_f")] CastF,

        #[regex(br##""([^\\"]|\\.)*""##)] LitString(&'a BStr),
        #[regex(br"[0-9]+(\.([0-9]*f|[0-9]+)|f)")] LitFloat(&'a BStr),
        #[regex(br"rad\([-+]?[0-9]+(\.([0-9]*f|[0-9]+)|f)?\)")] LitRad(&'a BStr),
        #[regex(br"[0-9]+")] LitIntDec(&'a BStr),
        #[regex(br"0[xX][0-9a-fA-F]+")] LitIntHex(&'a BStr),
        #[regex(br"0[bB][0-1]+")] LitIntBin(&'a BStr),
        #[regex(br"![-*ENHLWXYZO4567]+")] Difficulty(&'a BStr),
        #[regex(br"ins_[a-zA-Z0-9_]*")] Instr(&'a BStr),
        #[regex(br"[a-zA-Z_][a-zA-Z0-9_]*")] Ident(&'a BStr),

        #[error]
        #[regex(r"\s+", logos::skip)] // whitespace
        #[regex(r"//[^\n\r]*[\n\r]*", logos::skip)] // line comment
        #[regex(r"/\*([^*]|\**[^*/])*\*+/", logos::skip)] // block comment
        #[regex(r"/\*([^*]|\*+[^*/])*\*?")] // unclosed block comment
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
        fmt::Display::fmt(&self.as_bstr().to_str_lossy(), f)
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
    pub fn new(file_id: FileId, input: &'input [u8]) -> Lexer<'input> {
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
    type Item = Result<(Location, Token<'a>, Location), CompileError>;

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
