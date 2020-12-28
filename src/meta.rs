use std::collections::HashSet;

use bstr::{BStr, BString, ByteSlice};
use indexmap::IndexMap as Map;
use thiserror::Error;
use crate::pos::Sp;
use crate::ident::Ident;
use crate::fmt::Formatter;

#[derive(Debug, Clone, PartialEq)]
pub enum Meta {
    Int(i32),
    Float(f32),
    String(BString),
    // { key: value, ... }
    Object(Sp<Fields>),
    // [ value, ... ]
    Array(Vec<Sp<Meta>>),
    // ident { key: value, ... }
    Variant {
        name: Sp<Ident>,
        fields: Sp<Fields>,
    },
}

pub type Fields = Map<Sp<Ident>, Sp<Meta>>;

// For error messages
impl std::fmt::Display for Meta {
    fn fmt(&self, std_fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut formatter = Formatter::new(vec![]);
        // these are panics and not Errs because std::fmt::Error is for errors in the underlying writer
        formatter.fmt(self).expect("unexpected formatting failure");
        let buf = formatter.into_inner().expect("unexpected formatting failure");

        write!(std_fmt, "{}", String::from_utf8_lossy(&buf))
    }
}

impl Meta {
    pub fn make_object() -> BuildObject { BuildObject {
        variant: None,
        map: Some(Map::new()),
    }}

    /// Add a field to a meta.
    pub fn make_variant(variant: impl AsRef<str>) -> BuildObject {
        let variant = variant.as_ref().parse::<Ident>().unwrap_or_else(|e| panic!("Bug: {}", e));
        BuildObject {
            variant: Some(Sp::null(variant)),
            map: Some(Map::new()),
        }
    }
}

pub trait FromMeta: Sized {
    fn from_meta(meta: &Sp<Meta>) -> Result<Self, FromMetaError<'_>>;
}
pub trait ToMeta {
    fn to_meta(&self) -> Meta;
}

#[derive(Error, Debug)]
pub enum FromMetaError<'a> {
    #[error("expected {}, got {}", .expected, .got)]
    TypeError {
        expected: &'static str,
        got: &'a Sp<Meta>,
    },
    #[error("object is missing field {:?}", .missing)]
    MissingField {
        fields: &'a Sp<Fields>,
        missing: &'static str,
    },
    #[error("unrecognized field '{}'", .invalid)]
    UnrecognizedField {
        invalid: &'a Sp<Ident>,
    },
    #[error("unrecognized variant '{}'. Valid choices: [{}]", .invalid, .valid_variants)]
    UnrecognizedVariant {
        invalid: &'a Sp<Ident>,
        valid_variants: String,
    },
}

impl<'a> FromMetaError<'a> {
    pub fn expected(expected: &'static str, got: &'a Sp<Meta>) -> Self {
        FromMetaError::TypeError { expected, got }
    }
}

impl From<FromMetaError<'_>> for crate::error::CompileError {
    fn from(e: FromMetaError<'_>) -> Self { match e {
        FromMetaError::TypeError { expected, got } => error!(
            message("metadata type error"),
            primary(got, "expected {}", expected),
        ),
        FromMetaError::MissingField { fields, missing } => error!(
            message("incomplete metadata object"),
            primary(fields, "missing field '{}'", missing),
        ),
        FromMetaError::UnrecognizedField { invalid } => error!(
            message("unexpected field in metadata"),
            primary(invalid, "not a valid field here"),
        ),
        FromMetaError::UnrecognizedVariant { invalid, valid_variants } => error!(
            message("unrecognized variant in metadata"),
            primary(invalid, "unrecognized variant"),
            note("valid choices: [{}]", valid_variants),
        ),
    }}
}

/// Used to parse an object.
pub struct ParseObject<'a> {
    map: &'a Sp<Fields>,
    valid_fields: HashSet<&'static str>,
}

/// Used to parse a variant.
pub struct ParseVariant<'a, T> {
    ident: &'a Sp<Ident>,
    map: &'a Sp<Fields>,
    result: Option<Result<T, FromMetaError<'a>>>,
    valid_variants: Vec<&'static str>,
}

impl Sp<Meta> {
    /// Call [`FromMeta::from_meta`] to parse a [`Meta`] into a value.
    pub fn parse<T: FromMeta>(&self) -> Result<T, FromMetaError<'_>> {
        T::from_meta(self)
    }

    /// Parse an object.
    ///
    /// Any field not parsed by the closure will produce an 'unrecognized field' error
    /// when the closure finishes.
    ///
    /// If you only have access to a [`Fields`] and not a [`Meta`], then see [`ParseObject::new`].
    pub fn parse_object<'a, T>(
        &'a self,
        func: impl FnOnce(&mut ParseObject<'a>) -> Result<T, FromMetaError<'a>>,
    ) -> Result<T, FromMetaError<'_>> {
        match &self.value {
            Meta::Object(map) => {
                let mut helper = ParseObject::new(map);
                let value = func(&mut helper)?;
                helper.finish()?;
                Ok(value)
            },
            _ => Err(FromMetaError::expected("an object", self)),
        }
    }

    pub fn parse_variant<T>(&self) -> Result<ParseVariant<'_, T>, FromMetaError<'_>> {
        match &self.value {
            Meta::Variant { name, fields } => Ok(ParseVariant {
                ident: name, map: fields, result: None,
                valid_variants: vec![],
            }),
            _ => Err(FromMetaError::expected("a variant", self)),
        }
    }
}

impl<'a> ParseObject<'a> {
    /// Construct from a [`Fields`].
    ///
    /// Please be sure to call [`ParseObject::finish`] when you are done.  If you have a [`Meta`]
    /// then it is preferable to use [`Meta::parse_object`] instead which will automatically call
    /// the `finish` method for you.
    pub fn new(map: &'a Sp<Fields>) -> Self {
        ParseObject { map, valid_fields: HashSet::new() }
    }

    pub fn get_field<T: FromMeta>(&mut self, field: &'static str) -> Result<Option<T>, FromMetaError<'a>> {
        self.valid_fields.insert(field);
        match self.map.get(field) {
            Some(x) => x.parse().map(Some),
            None => Ok(None),
        }
    }

    pub fn expect_field<T: FromMeta>(&mut self, field: &'static str) -> Result<T, FromMetaError<'a>> {
        self.get_field(field)?.ok_or(FromMetaError::MissingField { fields: &self.map, missing: field })
    }

    /// Check for any user-supplied fields that were not parsed and emit errors on them.
    pub fn finish(self) -> Result<(), FromMetaError<'a>> {
        for key in self.map.keys() {
            if !self.valid_fields.iter().map(|x| -> &str { x.as_ref() }).any(|x| x == key) {
                return Err(FromMetaError::UnrecognizedField { invalid: key });
            }
        }
        Ok(())
    }
}

impl<'a, T> ParseVariant<'a, T> {
    pub fn variant(
        &mut self,
        variant: &str,
        handler: impl FnOnce(&mut ParseObject<'a>) -> Result<T, FromMetaError<'a>>,
    ) -> &mut Self {
        if self.ident == variant {
            self.result = Some(handler(&mut ParseObject::new(&self.map)));
        }
        self
    }

    pub fn finish(&mut self) -> Result<T, FromMetaError<'a>> {
        match self.result.take() {
            Some(out) => out,
            None => Err(FromMetaError::UnrecognizedVariant {
                invalid: self.ident,
                valid_variants: self.valid_variants.join(", "),
            }),
        }
    }
}

/// Builder pattern for an object or variant.
#[derive(Debug, Clone)]
pub struct BuildObject {
    /// `None` for an object, `Some` for a variant.
    variant: Option<Sp<Ident>>,
    /// This is taken by `build()`, poisoning the `BuildObject`.
    map: Option<Fields>,
}

impl BuildObject {
    fn get_map(&mut self) -> &mut Fields {
        self.map.as_mut().expect("(bug!) BuildObject used after .build()!")
    }

    /// Add a field to a meta.
    pub fn field(&mut self, key: impl AsRef<str>, value: &(impl ?Sized + ToMeta)) -> &mut Self {
        let ident = key.as_ref().parse::<Ident>().unwrap_or_else(|e| panic!("Bug: {}", e));
        self.get_map().insert(Sp::null(ident), Sp::null(value.to_meta()));
        self
    }

    /// Add a field if the option is `Some(_)`.
    pub fn opt_field(&mut self, key: impl AsRef<str>, value: Option<impl ToMeta>) -> &mut Self {
        if let Some(value) = value {
            self.field(key, &value);
        }
        self
    }

    /// Add a field if it's not equal to a default.
    pub fn field_default<T>(&mut self, key: impl AsRef<str>, value: &T, default: &T) -> &mut Self
    where T: ToMeta + PartialEq,
    {
        if value != default {
            self.field(key, value);
        }
        self
    }

    /// This helper lets you do whatever to a `BuildObject` without breaking the method chain.
    ///
    /// # Example
    /// ```
    /// use ecl_parser::meta::{Meta, BuildObject};
    ///
    /// fn add_options(b: &mut BuildObject) { /* ... */ }
    ///
    /// let meta = Meta::make_object()
    ///     .field("difficulty", &3)
    ///     .field("color", "blue")
    ///     .with_mut(|b| add_options(b))
    ///     .build();
    /// # let _ = meta;
    /// ```
    pub fn with_mut(&mut self, func: impl FnOnce(&mut BuildObject)) -> &mut Self {
        func(self);
        self
    }

    /// Build either a `Meta::Object` or a `Meta::Variant`.
    ///
    /// This will poison the builder.  Please clone it if you want to call more methods.
    pub fn build(&mut self) -> Meta {
        let fields = Sp::null(self.build_fields());
        match self.variant.take() {
            Some(name) => Meta::Variant { name, fields },
            None => Meta::Object(fields),
        }
    }

    /// Build a `Fields`.
    ///
    /// This will poison the builder.  Please clone it if you want to call more methods.
    pub fn build_fields(&mut self) -> Fields {
        self.map.take().expect("(bug!) BuildObject::build called multiple times!")
    }
}

// =============================================================================

impl FromMeta for i32 {
    fn from_meta(meta: &Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
        match meta.value {
            Meta::Int(x) => Ok(x),
            _ => Err(FromMetaError::expected("an integer", meta)),
        }
    }
}

impl FromMeta for u32 {
    fn from_meta(meta: &Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
        Ok(i32::from_meta(meta)? as u32)
    }
}

impl FromMeta for f32 {
    fn from_meta(meta: &Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
        match &meta.value {
            Meta::Int(x) => Ok(*x as f32),
            Meta::Float(x) => Ok(*x),
            _ => Err(FromMetaError::expected("a number", meta)),
        }
    }
}

impl FromMeta for BString {
    fn from_meta(meta: &Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
        match &meta.value {
            Meta::String(x) => Ok(x.clone()),
            _ => Err(FromMetaError::expected("a string", meta)),
        }
    }
}

impl<T: FromMeta> FromMeta for Vec<T> {
    fn from_meta(meta: &Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
        match &meta.value {
            Meta::Array(xs) => xs.into_iter().map(|x| x.parse()).collect(),
            _ => Err(FromMetaError::expected("an array", meta)),
        }
    }
}

impl<T: FromMeta> FromMeta for [T; 2] {
    fn from_meta(meta: &Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
        match &meta.value {
            Meta::Array(xs) => match xs.len() {
                2 => Ok([xs[0].parse()?, xs[1].parse()?]),
                _ => Err(FromMetaError::expected("an array of length 2", meta)),
            },
            _ => Err(FromMetaError::expected("an array", meta)),
        }
    }
}

impl<T: FromMeta> FromMeta for [T; 3] {
    fn from_meta(meta: &Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
        match &meta.value {
            Meta::Array(xs) => match xs.len() {
                3 => Ok([xs[0].parse()?, xs[1].parse()?, xs[2].parse()?]),
                _ => Err(FromMetaError::expected("an array of length 3", meta)),
            },
            _ => Err(FromMetaError::expected("an array", meta)),
        }
    }
}

impl<T: FromMeta> FromMeta for [T; 4] {
    fn from_meta(meta: &Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
        match &meta.value {
            Meta::Array(xs) => match xs.len() {
                4 => Ok([xs[0].parse()?, xs[1].parse()?, xs[2].parse()?, xs[3].parse()?]),
                _ => Err(FromMetaError::expected("an array of length 4", meta)),
            },
            _ => Err(FromMetaError::expected("an array", meta)),
        }
    }
}

impl<T: ToMeta + ?Sized> ToMeta for &T {
    fn to_meta(&self) -> Meta { ToMeta::to_meta(&**self) }
}
impl<T: ToMeta + ?Sized> ToMeta for Box<T> {
    fn to_meta(&self) -> Meta { ToMeta::to_meta(&**self) }
}
impl ToMeta for i32 {
    fn to_meta(&self) -> Meta { Meta::Int(*self) }
}
impl ToMeta for u32 {
    fn to_meta(&self) -> Meta { Meta::Int(*self as i32) }
}
impl ToMeta for f32 {
    fn to_meta(&self) -> Meta { Meta::Float(*self) }
}
impl ToMeta for BString {
    fn to_meta(&self) -> Meta { Meta::String(self.clone()) }
}
impl ToMeta for BStr {
    fn to_meta(&self) -> Meta { Meta::String(self.to_owned()) }
}
impl ToMeta for String {
    fn to_meta(&self) -> Meta { Meta::String(self.as_bytes().as_bstr().to_owned()) }
}
impl ToMeta for str {
    fn to_meta(&self) -> Meta { Meta::String(self.as_bytes().as_bstr().to_owned()) }
}
impl<T: ToMeta> ToMeta for Vec<T> {
    fn to_meta(&self) -> Meta { Meta::Array(self.iter().map(ToMeta::to_meta).map(Sp::null).collect()) }
}
impl<T: ToMeta> ToMeta for [T; 2] {
    fn to_meta(&self) -> Meta { Meta::Array(self.iter().map(ToMeta::to_meta).map(Sp::null).collect()) }
}
impl<T: ToMeta> ToMeta for [T; 3] {
    fn to_meta(&self) -> Meta { Meta::Array(self.iter().map(ToMeta::to_meta).map(Sp::null).collect()) }
}
impl<T: ToMeta> ToMeta for [T; 4] {
    fn to_meta(&self) -> Meta { Meta::Array(self.iter().map(ToMeta::to_meta).map(Sp::null).collect()) }
}

// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[track_caller]
    fn str_meta(s: &str) -> Sp<Meta> {
        let mut files = crate::pos::Files::new();
        files.parse("<input>", s.as_bytes()).unwrap()
    }

    #[derive(Debug, PartialEq, Eq)]
    struct Outer { abc: i32, def: Inner, opt: i32 }
    #[derive(Debug, PartialEq, Eq)]
    struct Inner { x: i32 }
    #[derive(Debug, PartialEq, Eq)]
    enum Enum {
        A { a: i32 },
        B { b: i32 },
    }

    impl FromMeta for Outer {
        fn from_meta(meta: &Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
            meta.parse_object(|m| Ok(Outer {
                abc: m.expect_field("abc")?,
                def: m.expect_field("def")?,
                opt: m.get_field("opt")?.unwrap_or(0),
            }))
        }
    }
    impl FromMeta for Inner {
        fn from_meta(meta: &Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
            meta.parse_object(|m| Ok(Inner { x: m.expect_field("x")? }))
        }
    }
    impl FromMeta for Enum {
        fn from_meta(meta: &Sp<Meta>) -> Result<Self, FromMetaError<'_>> {
            meta.parse_variant()?
                .variant("A", |m| Ok(Enum::A { a: m.expect_field("a")? }))
                .variant("B", |m| Ok(Enum::B { b: m.expect_field("b")? }))
                .finish()
        }
    }

    #[test]
    fn parse_object() {
        assert_eq!(
            str_meta(r"{ abc: 123, def: { x: 4 } }").parse::<Outer>().unwrap(),
            Outer { abc: 123, def: Inner { x: 4 }, opt: 0 },
        );

        assert_eq!(
            str_meta(r"{ abc: 123, def: { x: 4 }, opt: 10 }").parse::<Outer>().unwrap(),
            Outer { abc: 123, def: Inner { x: 4 }, opt: 10 },
        );

        assert!(matches!(
            str_meta(r"{ def: { x: 4 } }").parse::<Outer>(),
            Err(FromMetaError::MissingField { .. }),
        ));

        assert!(matches!(
            str_meta(r"{ abc: 123, def: { y: 4 } }").parse::<Outer>(),
            Err(FromMetaError::MissingField { .. }),
        ));

        assert!(matches!(
            str_meta(r"{ abc: 123, def: { x: 4, y: 3 } }").parse::<Outer>(),
            Err(FromMetaError::UnrecognizedField { .. }),
        ));

        assert!(matches!(
            str_meta(r#"{ abc: "123", def: { x: 4 } }"#).parse::<Outer>(),
            Err(FromMetaError::TypeError { .. }),
        ));
    }

    #[test]
    fn parse_variant() {
        assert!(matches!(
            str_meta(r#"A { a: 1 }"#).parse::<Enum>().unwrap(),
            Enum::A { a: 1 },
        ));

        assert!(matches!(
            str_meta(r#"C { a: 1 }"#).parse::<Enum>(),
            Err(FromMetaError::UnrecognizedVariant { .. }),
        ));
    }
}
