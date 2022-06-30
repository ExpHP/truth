
use crate::ast;
use crate::diagnostic::{Diagnostic, Emitter};
use crate::error::ErrorReported;
use crate::pos::{Sp, Span, SourceStr};
use crate::parse::lexer::Location;
use crate::ident::Ident;

use lalrpop_util::lalrpop_mod;
use indexmap::IndexMap;

lalrpop_mod!(attrs_lalrparser, "/parse/abi_attrs.rs");

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

pub type AttributeLexer<'input> = crate::parse::lexer::GenericLexer<'input, Token<'input>>;

use abi_ast::{Abi, Scalar, Attributes, AttributeRhs};
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
        pub attributes: Attributes,
    }

    pub type Attributes = IndexMap<Sp<Ident>, AttributeRhs>;

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
            emitter: &dyn Emitter,
            callback: F,
        ) -> Result<B, ErrorReported>
        where
            F: FnOnce(&mut AttributeDeserializer) -> Result<B, ErrorReported>,
        {
            let mut outer_name_buf = [0u8; 4];
            let outer_name = self.format_char.encode_utf8(&mut outer_name_buf);
            let outer_name = sp!(self.format_char.span => &*outer_name);

            let mut deserializer = AttributeDeserializer::new(outer_name, self.attributes, emitter);
            let value = callback(&mut deserializer)?;
            deserializer.finish()?;
            Ok(value)
        }
    }

    impl Scalar {
        #[allow(unused)]
        pub(super) fn descr(&self) -> &'static str {
            match self {
                Scalar::Number { .. } => "number",
                Scalar::String { .. } => "string",
            }
        }

        pub(super) fn format_as_literal(&self) -> String {
            match self {
                Scalar::Number(number) => format!("{number}"),
                Scalar::String(literal) => crate::fmt::stringify(&literal),
            }
        }
    }
}

/// Parse an ABI string into its AST.
pub fn parse_abi(
    mut text: SourceStr<'_>,
    emitter: &impl Emitter,
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
            format_char @ sp_pat!('a'..='z' | 'A'..='Z' | '_' | '-' | '0'..='9') => {
                let next_non_ws = text.chars().filter(|&c| !is_ws(c)).next();
                let attributes = match next_non_ws {
                    // Type with attributes.
                    Some('(') => extract_attributes_from_str(&mut text, emitter)?,
                    // Type without attributes.
                    _ => Default::default(),
                };
                params.push(abi_ast::Param { format_char, attributes })
            },

            bad_char => {
                let escaped: String = bad_char.escape_default().collect();
                return Err(emitter.emit(error!(
                    message("unexpected '{escaped}'"),
                    primary(bad_char, ""),
                )))
            },
        }
    }
    Ok(Abi { params })
}

/// Parse an `ins_intrinsic` string into its AST.
pub fn parse_intrinsic(
    text: SourceStr<'_>,
    emitter: &impl Emitter,
) -> Result<(Sp<Ident>, Attributes), ErrorReported> {
    let mut lexer = AttributeLexer::new(text.clone());

    let intrinsic_name_str = expect_token(&mut lexer, "identifier", emitter, |(l, token, r)| match token {
        Token::Ident(ident_str) => Some(sp!(Span::from_locs(l, r) => ident_str)),
        _ => None,
    })?;
    let intrinsic_name = match Ident::new_user(intrinsic_name_str.value) {
        Ok(ident) => sp!(intrinsic_name_str.span => ident),
        Err(_) => return Err(emitter.emit(error!(
            message("invalid identifier: {intrinsic_name_str}"),
            primary(intrinsic_name_str.span, ""),
        ))),
    };

    let attributes = extract_attributes(&mut lexer, emitter)?;

    if let Some((l, _, r)) = lexer.next().transpose().map_err(|e| emitter.emit(e))? {
        return Err(emitter.emit(error!(
            message("unexpected token after attributes"),
            primary(Span::from_locs(l, r), ""),
        )));
    }

    Ok((intrinsic_name, attributes))
}

/// Given a string that starts with '(', extract tokens up to and including
/// a ')' token and parse them into the AST for an attribute list.
fn extract_attributes_from_str<'input>(
    text: &mut SourceStr<'input>,
    emitter: &impl Emitter,
) -> Result<Attributes, ErrorReported>  {
    let mut lexer = AttributeLexer::new(text.clone());
    let attributes = extract_attributes(&mut lexer, emitter)?;
    let end = lexer.location().1;

    *text = text.slice_from((end - text.span().start).0 as _);
    Ok(attributes)
}

/// Given a lexer whose first token is '(', extract tokens up to and including
/// a ')' token and parse them into the AST for an attribute list.
///
/// (if first token is not `')'` this generates a user-facing error)
fn extract_attributes<'input>(
    lexer: &mut AttributeLexer<'input>,
    emitter: &impl Emitter,
) -> Result<Attributes, ErrorReported>  {
    let attr_tokens = extract_attr_tokens(lexer, emitter)?;
    let ident_rhs_pairs = {
        attrs_lalrparser::AttributesParser::new().parse(attr_tokens)
            .map_err(|e| emitter.emit(e))?
    };
    mapify_attributes(ident_rhs_pairs, emitter)
}

fn extract_attr_tokens<'input>(
    lexer: &mut AttributeLexer<'input>,
    emitter: &impl Emitter,
) -> Result<Vec<(Location, Token<'input>, Location)>, ErrorReported>  {
    let first_token = expect_token(lexer, "open parenthesis", emitter, |token| match token {
        token @ (_, Token::ParenOpen, _) => Some(token),
        _ => None,
    })?;
    let mut tokens = vec![first_token];

    // You can't nest parentheses in attributes so simply scan for a ')' token.
    while tokens.last().map(|(_, tok, _)| tok) != Some(&Token::ParenClose) {
        match lexer.next() {
            None => {
                let (l, _, r) = tokens[0];
                let open_paren_span = crate::pos::Span::from_locs(l, r);
                return Err(emitter.emit(error!(
                    message("missing closing parenthesis for attribute list"),
                    primary(open_paren_span, "unclosed parenthesis"),
                )));
            },
            Some(Err(e)) => return Err(emitter.emit(e)),
            Some(Ok(token)) => tokens.push(token),
        }
    }
    Ok(tokens)
}

fn mapify_attributes(
    attrs: impl IntoIterator<Item=(Sp<Ident>, AttributeRhs)>,
    emitter: &impl Emitter,
) -> Result<Attributes, ErrorReported> {
    let mut out = IndexMap::default();
    for (ident, rhs) in attrs {
        match out.entry(ident.clone()) {
            indexmap::map::Entry::Vacant(entry) => { entry.insert(rhs); },
            indexmap::map::Entry::Occupied(entry) => return Err(emitter.emit(error!(
                message("duplicate attribute {ident}"),
                primary(ident, ""),
                secondary(entry.key(), ""),
            ))),
        }
    }
    Ok(out)
}

/// Reads a token and calls a closure to determine whether the token is of the right kind.
///
/// If it is the right kind, the closure should produce `Some` (potentially with some payload of
/// interest).  Otherwise, it should return `None`, and a user-facing error will be emitted.
fn expect_token<'input, T>(
    lexer: &mut AttributeLexer<'input>,
    expected: &'static str,
    emitter: &impl Emitter,
    callback: impl FnOnce((Location, Token<'input>, Location)) -> Option<T>,
) -> Result<T, ErrorReported> {
    let option = lexer.next().transpose().map_err(|e| emitter.emit(e))?;

    // If there is a token, ask the callback if it's what we wanted.
    if let Some(token) = option {
        if let Some(successful_return_value) = callback(token) {
            return Ok(successful_return_value);
        }
    }

    // Otherwise it's either the wrong kind of token or EoF.
    let err_span = match option {
        Some((l, _, r)) => Span::from_locs(l, r),
        None => Span::from_locs(lexer.location(), lexer.location()),
    };
    Err(emitter.emit(error!(
        message("expected {expected}"),
        primary(err_span, ""),
    )))
}

// =============================================================================

/// Helper for validating the attributes of a specific ABI type.
pub struct AttributeDeserializer<'a> {
    /// Format character, or intrinsic name.
    outer_name: Sp<&'a str>,
    remaining_attributes: Attributes,
    emitter: &'a dyn Emitter,
}

impl<'a> AttributeDeserializer<'a> {
    pub fn new(outer_name: Sp<&'a str>, attributes: Attributes, emitter: &'a dyn Emitter) -> Self {
        AttributeDeserializer {
            outer_name,
            remaining_attributes: attributes,
            emitter,
        }
    }

    pub fn emitter(&self) -> &(impl Emitter + '_) { &self.emitter }
}

impl AttributeDeserializer<'_> {
    /// Read a single attribute from the attribute list which takes no value.
    pub fn accept_flag(&mut self, attr_name: &str) -> Result<Option<Span>, ErrorReported> {
        // reuse the FromAttribute machinery in `accept_value` to validate having no value
        let option: Option<Sp<()>> = self.accept_value(attr_name)?;
        Ok(option.map(|sp| sp.span))
    }

    /// Read a single attribute from the attribute list if present, validating it as having the desired type.
    pub fn accept_value<T: FromAttribute>(&mut self, attr_name: &str) -> Result<Option<Sp<T>>, ErrorReported> {
        match self.remaining_attributes.remove_entry(attr_name) {
            None => Ok(None),
            Some((key, rhs)) => {
                T::from_attribute(&rhs, &key)
                    .map_err(|e| self.emitter.as_sized().emit(e))
                    .map(|value| Some(sp!(key.span => value)))
            },
        }
    }

    /// Require an attribute to be present in the attribute list, validating it as having the desired type.
    pub fn expect_value<T: FromAttribute>(&mut self, attr_name: &str) -> Result<Sp<T>, ErrorReported> {
        match self.accept_value(attr_name)? {
            Some(value) => Ok(value),
            None => Err(self.error_missing(attr_name)),
        }
    }

    // /// Behaves either like [`Self::accept_value`] or [`Self::expect_value`] depending on whether a default exists.
    // ///
    // /// Useful for some cases where one format is an alias of another, but with a default set for something required.
    // pub fn maybe_expect_value<T: FromAttribute>(&mut self, attr_name: &str, default: Option<T>) -> Result<T, ErrorReported> {
    //     match (self.accept_value(attr_name)?, default) {
    //         (Some(value), _) => Ok(value.value),
    //         (None, Some(default)) => Ok(default),
    //         (None, None) => Err(self.error_missing(attr_name)),
    //     }
    // }

    pub fn error_missing(&mut self, attr_name: &str) -> ErrorReported {
        self.emitter.as_sized().emit(error!(
            message("missing attribute '{attr_name}' for '{}'", self.outer_name),
            primary(self.outer_name, ""),
        ))
    }

    /// Generate diagnostics on any attributes that were never accepted.
    #[inline(never)]
    pub fn finish(self) -> Result<(), ErrorReported> {
        for key in self.remaining_attributes.keys() {
            self.emitter.as_sized().emit(warning!(
                message("unsupported or unknown attribute '{key}' for '{}'", self.outer_name),
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

macro_rules! impl_from_scalar_for_other_ints {
    ($($int:ident),*) => {
        $(
            impl FromScalar for $int {
                fn from_scalar(scalar: &Sp<Scalar>, attr_name: &Sp<Ident>) -> Result<Self, Diagnostic> {
                    i32::from_scalar(scalar, attr_name)?
                        .try_into()
                        .map_err(|_| error!(
                            message("value out of range for '{attr_name}'"),
                            primary(scalar, ""),
                        ))
                }
            }
        )*
    }
}

impl_from_scalar_for_other_ints!{ u32, u8 }

impl FromScalar for String {
    fn from_scalar(scalar: &Sp<Scalar>, attr_name: &Sp<Ident>) -> Result<Self, Diagnostic> {
        match &scalar.value {
            Scalar::String(str) => Ok(str.string.clone()),
            _ => Err(wrong_scalar_type(attr_name, "string", scalar)),
        }
    }
}

impl FromScalar for Ident {
    fn from_scalar(scalar: &Sp<Scalar>, attr_name: &Sp<Ident>) -> Result<Self, Diagnostic> {
        FromScalar::from_scalar(scalar, attr_name)
            .and_then(|string: String| {
                Ident::new_user(&string).map_err(|e| error!(
                    message("{e}"),
                    primary(scalar, ""),
                ))
            })
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
        message("flag '{attr_name}' does not take a value"),
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
    use super::abi_ast::Param;

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
        parse_abi(source_str, truth.ctx().emitter).unwrap()
    }

    fn expect_parse_error(
        expected: &str,
        input: &str,
    ) -> String {
        let mut scope = crate::Builder::new().capture_diagnostics(true).build();
        let mut truth = scope.truth();
        let source_str = truth.register_source("<input>", input).unwrap();
        let _ = parse_abi(source_str, truth.ctx().emitter);

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
    test_case!(bad_token, r##"a(&)"##, error["invalid token"]);
    test_case!(flag, r##"a(bs)"##, success[a(bs)]);
    test_case!(number, r##"a(bs=4)"##, success[a(bs[4])]);
    test_case!(string, r##"a(bs="lol")"##, success[a(bs["lol"])]);
    test_case!(string_escape, r##"a(bs=" \n ")"##, success[a(bs[" \n "])]);
    test_case!(after_attr, r##"a()b"##, success[a(), b()]);
    test_case!(double_attr, r##"a()()"##, error["unexpected"]);
    test_case!(initial_paren, r##"()"##, error["unexpected"]);

    test_case!(ws_before, "  ab", success[a(), b()]);
    test_case!(ws_after, "ab  \t ", success[a(), b()]);
    test_case!(ws_between, "a  b", success[a(), b()]);
    test_case!(ws_only, "    \t", success[]);
    test_case!(ws_before_attr, "ab (bs)", success[a(), b(bs)]);
    test_case!(ws_after_attr, "a(bs) b", success[a(bs), b()]);
    test_case!(ws_inside_attr, "a( bs = 4 ; x = 3 , 2 )", success[a(bs[4], x[3, 2])]);

    test_case!(errant_quote, r##""""##, error["unexpected"]);
    test_case!(errant_close_paren, r##")"##, error["unexpected"]);
    test_case!(errant_eq, r##"="##, error["unexpected"]);
    test_case!(unclosed_paren, r##"a(bs=2"##, error["unclosed"]);
    test_case!(duplicate_attr, r##"a(bs=4; x=3; bs=2)"##, error["duplicate"]);
    test_case!(trick_close_paren_in_string, r##"S(enum=")""##, error["unclosed"]);
    test_case!(trick_escaped_quote_in_string, r##"S(enum="\")""##, error["unclosed"]);
    test_case!(attr_only_comma, r##"a(bs=,)"##, error["unexpected"]);
    test_case!(attr_trailing_comma, r##"a(bs=3,)"##, error["unexpected"]);
}
