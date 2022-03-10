
use crate::ast;
use crate::context::CompilerContext;
use crate::diagnostic::Diagnostic;
use crate::error::ErrorReported;
use crate::pos::{Sp, HasSpan, SourceStr};
use crate::parse::lexer::Location;
use crate::ident::Ident;

use lalrpop_util::lalrpop_mod;
use indexmap::IndexMap;

lalrpop_mod!(attrs_parser, "/parse/abi_attrs.rs");

define_token_enum! {
    #[derive(logos::Logos, Clone, Copy, Debug, PartialEq)]
    pub enum Token<'a> {
        #[token(",")] Comma,
        #[token("-")] Minus,
        #[token(";")] Semicolon,
        #[token("(")] ParenOpen,
        #[token(")")] ParenClose,
        #[token("=")] Eq,

        #[regex(r##""([^\\"]|\\.)*""##)] LitString(&'a str),
        #[regex(r##"[a-zA-Z_][a-zA-Z0-9_]*"##)] Ident(&'a str),
        #[regex(r##"[0-9]+|0[xX][0-9a-fA-F]+|0[bB][0-1]+"##)] LitInt(&'a str),

        #[error]
        #[regex(r##"\s+"##, logos::skip)] // whitespace
        #[doc(hidden)]
        /// Implementation detail. Basically, [`logos`] requires an error variant.
        /// [`Lexer`] never actually produces this variant, returning `Result::Err` instead.
        Error,
    }
}

type AttributeLexer<'input> = crate::parse::lexer::GenericLexer<'input, Token<'input>>;

use abi_ast::{Abi, Param, Scalar, AttributeRhs};
pub mod abi_ast {
    //! An AST for an ABI in a more abstract form, as a series of type characters with
    //! attribute dictionaries.
    use super::*;
    pub use ast::LitString;

    #[derive(Debug, Clone, PartialEq)]
    pub struct Abi {
        pub params: Vec<Param>,
    }

    #[derive(Debug, Clone, PartialEq)]
    pub struct Param {
        pub format_char: Sp<char>,
        pub attributes: IndexMap<Sp<Ident>, AttributeRhs>,
    }

    #[derive(Debug, Clone, PartialEq)]
    pub enum AttributeRhs {
        Flag,
        /// One or more values. (zero values is a parse error)
        Values(Vec<Sp<Scalar>>),
    }

    #[derive(Debug, Clone, PartialEq)]
    pub enum Scalar {
        Number(i32),
        String(LitString),
    }

    impl Param {
        pub fn deserialize_attributes<B, F>(
            self,
            callback: F,
            ctx: &CompilerContext<'_>,
        ) -> Result<B, ErrorReported>
        where
            F: FnOnce(&mut AttributeDeserializer) -> Result<B, ErrorReported>,
        {
            let mut deserializer = AttributeDeserializer {
                remaining_attributes: self.attributes,
                ctx,
            };
            let value = callback(&mut deserializer)?;
            deserializer.finish()?;
            Ok(value)
        }
    }

    impl Scalar {
        pub(super) fn descr(&self) -> &'static str {
            match self {
                Scalar::Number { .. } => "number",
                Scalar::String { .. } => "string",
            }
        }

        pub(super) fn format_as_literal(&self) -> String {
            match self {
                Scalar::Number(number) => format!("{}", number),
                Scalar::String(literal) => crate::fmt::stringify(&literal),
            }
        }
    }
}

pub fn parse_abi(
    mut text: SourceStr<'_>,
    ctx: &CompilerContext<'_>,
) -> Result<Abi, ErrorReported> {
    let mut params = vec![];

    let is_ws = |c: char| c.is_ascii_whitespace();

    // We alternate between reading individual chars to get param types, and using the
    // lexer & parser to get attributes.
    while let Some(next_char) = text.split_next_char() {
        if is_ws(next_char.value) {
            continue;
        }

        match next_char {
            paren @ sp_pat!('(') => return Err(ctx.emitter.emit(error!(
                message("unexpected '('"),
                primary(paren, ""),
            ))),

            format_char => {
                let next_non_ws = text.chars().filter(|&c| !is_ws(c)).next();
                let attributes = match next_non_ws {
                    // Type with attributes.
                    Some('(') => {
                        let attr_tokens = extract_attr_tokens(&mut text, ctx)?;
                        let ident_rhs_pairs = {
                            attrs_parser::AttributesParser::new().parse(attr_tokens)
                                .map_err(|e| ctx.emitter.emit(e))?
                        };
                        mapify_attributes(ident_rhs_pairs, ctx)?
                    },
                    // Type without attributes.
                    _ => Default::default(),
                };
                params.push(abi_ast::Param { format_char, attributes })
            },
        }
    }
    Ok(Abi { params })
}

/// Given a string whose first token is '(', extract tokens up to and including
/// a ')' token for an attribute list.
fn extract_attr_tokens<'input>(
    text: &mut SourceStr<'input>,
    ctx: &CompilerContext<'_>,
) -> Result<Vec<(Location, Token<'input>, Location)>, ErrorReported>  {
    let mut lexer = AttributeLexer::new(text.clone());

    let first_token = lexer.next().expect("should begin with open paren").unwrap();
    assert_eq!(first_token.1, Token::ParenOpen);
    let mut tokens = vec![first_token];

    // You can't nest parentheses in attributes so simply scan for a ')'.
    // However, because ')' can appear in strings we need to use the lexer.
    while tokens.last().map(|(_, tok, _)| tok) != Some(&Token::ParenClose) {
        match lexer.next() {
            None => {
                let (l, _, r) = tokens[0];
                let open_paren_span = crate::pos::Span::from_locs(l, r);
                return Err(ctx.emitter.emit(error!(
                    message("missing closing parenthesis for attribute list"),
                    primary(open_paren_span, "unclosed parenthesis"),
                )))
            },
            Some(Err(e)) => return Err(ctx.emitter.emit(e)),
            Some(Ok(token)) => tokens.push(token),
        }
    }
    let end = lexer.location().1;
    eprintln!("{:?}", text);
    *text = text.slice_from((end - text.span().start).0 as _);
    eprintln!("{:?}", text);
    Ok(tokens)
}

fn mapify_attributes(
    attrs: impl IntoIterator<Item=(Sp<Ident>, AttributeRhs)>,
    ctx: &CompilerContext<'_>,
) -> Result<IndexMap<Sp<Ident>, AttributeRhs>, ErrorReported> {
    let mut out = IndexMap::default();
    for (ident, rhs) in attrs {
        match out.entry(ident.clone()) {
            indexmap::map::Entry::Vacant(entry) => { entry.insert(rhs); },
            indexmap::map::Entry::Occupied(entry) => return Err(ctx.emitter.emit(error!(
                message("duplicate attribute {ident}"),
                primary(ident, ""),
                secondary(entry.key(), ""),
            ))),
        }
    }
    Ok(out)
}

// =============================================================================

/// Helper for validating the attributes of a specific ABI type.
pub struct AttributeDeserializer<'a, 'ctx> {
    remaining_attributes: IndexMap<Sp<Ident>, AttributeRhs>,
    ctx: &'a CompilerContext<'ctx>,
}

impl AttributeDeserializer<'_, '_> {
    /// Read a single attribute from the attribute list which takes no value.
    pub fn accept_flag(&mut self, ident: &Sp<Ident>) -> Result<bool, ErrorReported> {
        // reuse the FromAttribute machinery in `accept_value` to validate having no value
        let option: Option<()> = self.accept_value(ident)?;
        Ok(option.is_some())
    }

    /// Read a single attribute from the attribute list, validating it as having the desired type.
    pub fn accept_value<T: FromAttribute>(&mut self, ident: &Sp<Ident>) -> Result<Option<T>, ErrorReported> {
        match self.remaining_attributes.remove(ident) {
            None => Ok(None),
            Some(rhs) => Ok(Some(T::from_attribute(&rhs, ident).map_err(|e| self.ctx.emitter.emit(e))?)),
        }
    }

    /// Generate diagnostics on any attributes that were never accepted.
    #[inline(never)]
    pub fn finish(self) -> Result<(), ErrorReported> {
        for key in self.remaining_attributes.keys() {
            self.ctx.emitter.emit(warning!(
                message("unsupported or unknown attribute '{key}'"),
                primary(key, ""),
            )).ignore();
        }
        Ok(())
    }
}

pub trait FromScalar: Sized {
    fn from_scalar(scalar: &Sp<Scalar>, attr_name: &Sp<Ident>) -> Result<Self, Diagnostic>;
}

impl FromScalar for i32 {
    fn from_scalar(scalar: &Sp<Scalar>, attr_name: &Sp<Ident>) -> Result<Self, Diagnostic> {
        match &scalar.value {
            &Scalar::Number(number) => Ok(number),
            _ => Err(wrong_scalar_type(attr_name, "number", scalar)),
        }
    }
}

impl FromScalar for String {
    fn from_scalar(scalar: &Sp<Scalar>, attr_name: &Sp<Ident>) -> Result<Self, Diagnostic> {
        match &scalar.value {
            Scalar::String(str) => Ok(crate::fmt::stringify(str)),
            _ => Err(wrong_scalar_type(attr_name, "string", scalar)),
        }
    }
}

pub trait FromAttribute: Sized {
    fn from_attribute(rhs: &AttributeRhs, attr_name: &Sp<Ident>) -> Result<Self, Diagnostic>;
}

impl FromAttribute for () {
    fn from_attribute(rhs: &AttributeRhs, attr_name: &Sp<Ident>) -> Result<Self, Diagnostic> {
        match &rhs {
            AttributeRhs::Flag => Ok(()),
            AttributeRhs::Values(values) => match &values[..] {
                [] => unreachable!(),
                [value, ..] => Err(expected_no_value(attr_name, value)),
            },
        }
    }
}

impl<T: FromScalar> FromAttribute for T {
    fn from_attribute(rhs: &AttributeRhs, attr_name: &Sp<Ident>) -> Result<Self, Diagnostic> {
        let [value] = <[T; 1]>::from_attribute(rhs, attr_name)?;
        Ok(value)
    }
}

impl<T: FromScalar> FromAttribute for Vec<T> {
    fn from_attribute(rhs: &AttributeRhs, attr_name: &Sp<Ident>) -> Result<Self, Diagnostic> {
        match rhs {
            AttributeRhs::Flag => Err(missing_value(attr_name)),
            AttributeRhs::Values(values) => {
                values.iter()
                    .map(|x| FromScalar::from_scalar(x, attr_name))
                    .collect::<Result<_, _>>()
            },
        }
    }
}

impl<T: FromScalar, const N: usize> FromAttribute for [T; N] {
    fn from_attribute(rhs: &AttributeRhs, attr_name: &Sp<Ident>) -> Result<Self, Diagnostic> {
        let vec: Vec<T> = FromAttribute::from_attribute(rhs, attr_name)?;

        <[T; N]>::try_from(vec)
            .map_err(|vec| wrong_num_values(attr_name, N, &vec))
    }
}

fn missing_value(attr_name: &Sp<Ident>) -> Diagnostic {
    error!(
        message("attribute '{attr_name}' expects a value"),
        primary(attr_name, ""),
    )
}

fn expected_no_value(attr_name: &Sp<Ident>, value: &Sp<Scalar>) -> Diagnostic {
    error!(
        message("flag '{}' does not take a value", attr_name),
        primary(value, ""),
    )
}

fn wrong_scalar_type(attr_name: &Sp<Ident>, expected: &str, scalar: &Sp<Scalar>) -> Diagnostic {
    // this says "in attribute" rather than just "attribute" because the scalar might not
    // be the whole rhs if it is a sequence of values
    error!(
        message("in attribute '{attr_name}': expected {expected}, got {}", scalar.format_as_literal()),
        primary(scalar, ""),
    )
}

fn wrong_num_values<T>(attr_name: &Sp<Ident>, expected: usize, got: &[T]) -> Diagnostic {
    let expected_str = match expected {
        1 => format!("a single value"),
        n => format!("{n} values"),
    };
    error!(
        message("attribute '{attr_name}' expects {expected_str}, got {}", got.len()),
        primary(attr_name, ""),
    )
}

// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    trait LiteralScalar {
        fn into_scalar(self) -> Scalar;
    }

    impl LiteralScalar for i32 {
        fn into_scalar(self) -> Scalar { Scalar::Number(self) }
    }

    impl LiteralScalar for &'static str {
        fn into_scalar(self) -> Scalar { Scalar::String(self.into()) }
    }

    macro_rules! make_abi {
        ($( $format_char:tt ($($attr:tt)*) ),* $(,)?) => {
            Abi { params: vec![ $( make_abi_param!( $format_char($($attr)*) ), )* ] }
        };
    }

    macro_rules! make_abi_param {
        ($format_char:tt ($($attr:tt)*)) => {{
            let format_char_str = stringify!($format_char);

            assert_eq!(format_char_str.chars().count(), 1);
            let format_char = sp!(format_char_str.chars().next().unwrap());
            let attributes = make_attrs!( $($attr)* );
            Param { format_char, attributes }
        }};
    }

    macro_rules! make_attrs {
        ($(
            $ident:ident $([ $($rhs:tt)+ ])?
        ),* $(,)? ) => {
            vec![ $({
                let key = sp!(ident!(stringify!($ident)));
                let value = make_attr_rhs!( $([ $($rhs)+ ])? );
                (key, value)
            }),* ].into_iter().collect::<IndexMap<_, _>>()
        };
    }

    macro_rules! make_attr_rhs {
        () => {
            AttributeRhs::Flag
        };
        ([ $($lit:literal),+ ]) => {
            AttributeRhs::Values(vec![$(sp!($lit.into_scalar())),+])
        };
    }

    fn parse_test_input(
        input: &str,
    ) -> Abi {
        let mut scope = crate::Builder::new().build();
        let mut truth = scope.truth();
        let source_str = truth.register_source("<input>", input).unwrap();
        parse_abi(source_str, truth.ctx()).unwrap()
    }

    fn expect_parse_error(
        expected: &str,
        input: &str,
    ) -> String {
        let mut scope = crate::Builder::new().capture_diagnostics(true).build();
        let mut truth = scope.truth();
        let source_str = truth.register_source("<input>", input).unwrap();
        let _ = parse_abi(source_str, truth.ctx());

        let err_str = truth.get_captured_diagnostics().unwrap();
        if !err_str.contains(expected) {
            panic!("expected not found in error message!  error: `{}`  expected: {:?}", err_str, expected)
        }
        err_str
    }

    macro_rules! test_case {
        ($fn_name:ident, $text:literal, success[  $($expected_abi:tt)*  ]) => {
            #[test]
            fn $fn_name() {
                crate::setup_for_test_harness();

                let expected = make_abi!( $($expected_abi)* );
                let abi = parse_test_input($text);
                assert_eq!(abi, expected);
            }
        };

        ($fn_name:ident, $text:literal, error[  $expected_message:literal  ]) => {
            #[test]
            fn $fn_name() {
                crate::setup_for_test_harness();

                assert_snapshot!(expect_parse_error($expected_message, $text).trim());
            }
        };
    }

    test_case!(no_arg, r##""##, success[]);
    test_case!(simple, r##"aab"##, success[a(), a(), b()]);
    test_case!(empty_attr, r##"a()"##, success[a()]);
    test_case!(flag_attr, r##"a(bs)"##, success[a(bs)]);
    test_case!(flag_number, r##"a(bs=4)"##, success[a(bs[4])]);
    test_case!(flag_string, r##"a(bs="lol")"##, success[a(bs["lol"])]);
    test_case!(string_escape, r##"a(bs=" \n ")"##, success[a(bs[" \n "])]);
    test_case!(after_attr, r##"a()b"##, success[a(), b()]);
    test_case!(double_attr, r##"a()()"##, error["unexpected"]);
    test_case!(ws_before, r##"  ab"##, success[a(), b()]);
    test_case!(ws_after, r##"ab  \t "##, success[a(), b()]);
    test_case!(ws_between, r##"a  b"##, success[a(), b()]);
    test_case!(ws_only, r##"    \t"##, success[]);
    test_case!(ws_before_attr, r##"ab (bs)"##, success[a(), b(bs)]);
    test_case!(ws_after_attr, r##"a(bs) b"##, success[a(bs), b()]);
    test_case!(ws_inside_attr, r##"a( bs = 4 ; x = 3 , 2 )"##, success[a(bs[4], x[3, 2])]);
    test_case!(errant_quote, r##""""##, error["unexpected"]);
    test_case!(errant_close_paren, r##")"##, error["unexpected"]);
    test_case!(unclosed_paren, r##"a(bs=2"##, error["unclosed"]);
    test_case!(duplicate_attr, r##"a(bs=4; x=3; bs=2)"##, error["duplicate"]);
    test_case!(trick_close_paren_in_string, r##"S(enum=")""##, error["unclosed"]);
    test_case!(attr_only_comma, r##"a(bs=,)"##, error["unexpected"]);
    test_case!(attr_trailing_comma, r##"a(bs=3,)"##, error["unexpected"]);
}
