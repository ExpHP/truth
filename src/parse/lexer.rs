//! Because LALRPOP's default lexer requires UTF-8 (and ECL script files may
//! instead be encoded in Shift-JIS), we need to use our own lexer.

use std::fmt;
use regex::bytes::{Regex, RegexBuilder};
use bstr::{BStr, ByteSlice};
use lazy_static::lazy_static;

use crate::pos::{BytePos};

// This is a simple lexer that tries to keep most of the maintainability
// of the default lexer (though it is almost certainly nowhere near as fast).
//
// The following macro is an `each_x` style macro that associates each fixed
// string or regex with its lexical class, as well as a priority (which roughly
// corresponds to the number of `else`s before the rule in the LALRPOP default
// lexer).
macro_rules! with_each_terminal {
    ($mac:ident) => { $mac!{
        fixed=[
            [0, b",", Comma]
            [0, b"?", Question]
            [0, b":", Colon]
            [0, b";", Semicolon]
            [0, b"[", BracketOpen]
            [0, b"]", BracketClose]
            [0, b"{", BraceOpen]
            [0, b"}", BraceClose]
            [0, b"(", ParenOpen]
            [0, b")", ParenClose]
            [0, b"@", AtSign]
            [0, b"...", Ellipsis]
            [0, b".", Dot]
            [0, b"=", Eq]
            [0, b"+", Plus]
            [0, b"-", Minus]
            [0, b"*", Star]
            [0, b"/", Slash]
            [0, b"%", Percent]
            [0, b"^", Caret]
            [0, b"|", Or]
            [0, b"&", And]
            [0, b"+=", PlusEq]
            [0, b"-=", MinusEq]
            [0, b"*=", StarEq]
            [0, b"/=", SlashEq]
            [0, b"%=", PercentEq]
            [0, b"^=", CaretEq]
            [0, b"|=", OrEq]
            [0, b"&=", AndEq]
            [0, b"==", EqEq]
            [0, b"!=", NotEq]
            [0, b"<", Less]
            [0, b"<=", LessEq]
            [0, b">", Greater]
            [0, b">=", GreaterEq]
            [0, b"!", Not]
            [0, b"||", OrOr]
            [0, b"&&", AndAnd]
            [0, b"--", MinusMinus]
            [0, b"$", Cash]
            [0, b"anim", Anim]
            [0, b"ecli", Ecli]
            [0, b"meta", Meta]
            [0, b"sub", Sub]
            [0, b"timeline", Timeline]
            [0, b"script", Script]
            [0, b"entry", Entry]
            [0, b"var", Var]
            [0, b"int", Int]
            [0, b"float", Float]
            [0, b"void", Void]
            [0, b"inline", Inline]
            [0, b"insdef", Insdef]
            [0, b"return", Return]
            [0, b"goto", Goto]
            [0, b"loop", Loop]
            [0, b"if", If]
            [0, b"else", Else]
            [0, b"unless", Unless]
            [0, b"do", Do]
            [0, b"while", While]
            [0, b"times", Times]
            [0, b"break", Break]
            [0, b"switch", Switch]
            [0, b"case", Case]
            [0, b"default", Default]
            [0, b"async", Async]
            [0, b"global", Global]
            [0, b"false", False]
            [0, b"true", True]
        ]
        regex=[
            [0, r##""([^\\"]|\\.)*""##, LitString]
            [0, r"[0-9]+(\.([0-9]*f|[0-9]+)|f)", LitFloat]
            [0, r"rad\([-+]?[0-9]+(\.([0-9]*f|[0-9]+)|f)?\)", LitRad]
            [0, r"[0-9]+", LitIntDec]
            [0, r"0[xX][0-9a-fA-F]+", LitIntHex]
            [0, r"0[bB][0-1]+", LitIntBin]
            [0, r"![-*ENHLWXYZO4567]+", Difficulty]
            // Lower priority
            [1, r"[a-zA-Z_][a-zA-Z0-9_]*", Ident]
        ]
        // These correspond to `=> {}` patterns in the LALRPOP default lexer,
        // and all effectively have a priority of -1.
        whitespace=[
            [r"//[^\n\r]*[\n\r]*"] // line comments
            [r"/\*([^*]*\*+[^*/])*([^*]*\*+|[^*])*\*/"] // block comments
            [r"\s+"] // whitespace
        ]
    }};
}

macro_rules! define_token_enum {
    (
        fixed=[$([$f_prio:literal, $f_bytes:literal, $f_variant:ident])+]
        regex=[$([$r_prio:literal, $r_str:literal, $r_variant:ident])+]
        whitespace=[$([$s_str:literal])+]
    ) => {
        #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub enum Token<'a> {
            $($f_variant,)+

            $($r_variant(&'a BStr),)+

            /// Implementation detail. A virtual token used to select a nonterminal to parse.
            /// (part of a workaround to reduce LALRPOP output size)
            #[doc(hidden)]
            VirtualDispatch(crate::parse::AnythingTag),
        }
    };
}
with_each_terminal!(define_token_enum);

macro_rules! impl_token_helpers {
    (
        fixed=[$([$f_prio:literal, $f_bytes:literal, $f_variant:ident])+]
        regex=[$([$r_prio:literal, $r_str:literal, $r_variant:ident])+]
        whitespace=[$([$s_str:literal])+]
    ) => {
        impl<'a> Token<'a> {
            pub fn as_bstr(&self) -> &BStr {
                match *self {
                    $(Token::$f_variant => $f_bytes.as_bstr(),)+
                    $(Token::$r_variant(bytes) => bytes,)+
                    Token::VirtualDispatch(_) => b"".as_bstr(),
                }
            }

            pub fn len(&self) -> usize {
                self.as_bstr().len()
            }

            fn priority(&self) -> u32 {
                match *self {
                    $(Token::$f_variant => $f_prio,)+
                    $(Token::$r_variant(_) => $r_prio,)+
                    Token::VirtualDispatch(_) => 0,
                }
            }
        }
    };
}
with_each_terminal!(impl_token_helpers);

// This gets used by LALRPOP's error messages for unexpected tokens.
impl<'a> fmt::Display for Token<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.as_bstr().to_str_lossy(), f)
    }
}

#[derive(Debug, Clone)]
pub struct Lexer<'input> {
    offset: usize,
    remainder: &'input [u8],
    // a temporary kept around to reduce allocations
    matches_buf: Vec<Token<'input>>,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input [u8]) -> Lexer<'input> {
        Lexer {
            offset: 0,
            matches_buf: vec![],
            remainder: input,
        }
    }

    /// Get the current offset into the original input.
    pub fn offset(&self) -> usize { self.offset }
}

// FIXME: Replace this with a proper Error type.
//
// &'static str is simply the default used by LALRPOP.
pub type LexerError = &'static str;

macro_rules! impl_token_matchers {
    (
        fixed=[$([$f_prio:literal, $f_bytes:literal, $f_variant:ident])+]
        regex=[$([$r_prio:literal, $r_str:literal, $r_variant:ident])+]
        whitespace=[$([$s_str:literal])+]
    ) => {
        lazy_static!{
            static ref NORMAL_REGEXES: Vec<Regex> = {
                vec![ $({
                    RegexBuilder::new(&format!("^{}", $r_str))
                        .unicode(false).build().unwrap()
                },)+ ]
            };
            static ref WHITESPACE_REGEX: Regex = {
                // construct alternation of all whitespace regexes
                let mut pattern = "^(".to_string();
                $(
                    pattern.push_str($s_str);
                    pattern.push('|');
                )+
                pattern.pop(); // remove last '|'
                pattern.push(')');
                pattern.push('*'); // apply repeatedly
                RegexBuilder::new(&pattern)
                    .unicode(false).build().unwrap()
            };
        }
        static RE_TOKEN_CONSTRUCTORS: &'static [fn(&BStr) -> Token] = {
            &[$( |b: &BStr| -> Token { Token::$r_variant(b) }, )+]
        };

        impl<'a> Lexer<'a> {
            #[inline(never)] // show in profiler
            fn gather_fixed_matches(out: &mut Vec<Token<'a>>, input: &'a [u8]) {
                $(if input.starts_with($f_bytes) {
                    out.push(Token::$f_variant);
                })+
            }

            #[inline(never)] // show in profiler
            fn gather_regex_matches(out: &mut Vec<Token<'a>>, input: &'a [u8]) {
                for (re, &constructor) in NORMAL_REGEXES.iter().zip(RE_TOKEN_CONSTRUCTORS) {
                    if let Some(re_match) = re.find(input) {
                        let matched = &input[..re_match.end()];
                        out.push(constructor(matched.as_bstr()))
                    }
                }
            }
        }
    };
}
with_each_terminal!(impl_token_matchers);

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<(BytePos, Token<'a>, BytePos), LexerError>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(ws_match) = WHITESPACE_REGEX.find(self.remainder) {
            self.remainder = &self.remainder[ws_match.end()..];
            self.offset += ws_match.end();
        };

        if self.remainder.is_empty() {
            return None;
        }

        // Find all possible lexical classes at this point.
        assert!(self.matches_buf.is_empty()); // always emptied at end of method
        Self::gather_fixed_matches(&mut self.matches_buf, self.remainder);
        Self::gather_regex_matches(&mut self.matches_buf, self.remainder);
        if self.matches_buf.is_empty() {
            return Some(Err("bad token"));
        }

        // Longest match wins.
        let best_len = self.matches_buf.iter().map(|m| m.len()).max().unwrap();
        self.matches_buf.retain(|m| m.len() == best_len);

        // Break ties with priority.
        let best_prio = self.matches_buf.iter().map(|m| m.priority()).min().unwrap();
        self.matches_buf.retain(|m| m.priority() == best_prio);

        assert_eq!(
            self.matches_buf.len(), 1,
            "ambiguity detected in lexer (this is a BUG!): {:?}", self.matches_buf,
        );

        let token = self.matches_buf.pop().unwrap();
        let start = self.offset;
        self.offset += token.len();
        self.remainder = &self.remainder[token.len()..];
        Some(Ok((BytePos(start as u32), token, BytePos(self.offset as u32))))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tokenize(s: &str) -> Vec<(BytePos, Token<'_>, BytePos)> {
        Lexer::new(s.as_ref()).map(|res| res.unwrap()).collect::<Vec<_>>()
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
}
