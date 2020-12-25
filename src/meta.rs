use bstr::{BStr, BString};
use indexmap::IndexMap as Map;
use thiserror::Error;
use crate::ident::Ident;
use crate::fmt::Formatter;

#[derive(Debug, Clone, PartialEq)]
pub enum Meta {
    Int(i32),
    Float(f32),
    String(BString),
    Object(Map<Ident, Meta>),
    Array(Vec<Meta>),
}

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
    pub fn parse<T: FromMeta>(&self) -> Result<T, FromMetaError<'_>> {
        T::from_meta(self)
    }
    pub fn get_field<'a, T: FromMeta>(&'a self, field: &'a str) -> Result<Option<T>, FromMetaError<'a>> {
        match self {
            Meta::Object(map) => match map.get(field) {
                Some(x) => x.parse().map(Some),
                None => Ok(None),
            },
            _ => Err(FromMetaError::expected("an object", self)),
        }
    }
    pub fn expect_field<'a, T: FromMeta>(&'a self, field: &'a str) -> Result<T, FromMetaError<'a>> {
        self.get_field(field)?.ok_or(FromMetaError::MissingField { field })
    }
    pub fn make_object() -> BuildObject { BuildObject { map: Map::new() } }
}

/// Builder pattern for an object.
pub struct BuildObject {
    map: Map<Ident, Meta>,
}

impl BuildObject {
    pub fn field(mut self, key: impl AsRef<str>, value: &impl ToMeta) -> Self {
        let ident = key.as_ref().parse().unwrap_or_else(|e| panic!("Bug: {}", e));
        self.map.insert(ident, value.to_meta());
        self
    }
    pub fn field_default<T>(mut self, key: impl AsRef<str>, value: &T, default: &T) -> Self
    where T: ToMeta + PartialEq,
    {
        if value != default {
            let ident = key.as_ref().parse().unwrap_or_else(|e| panic!("Bug: {}", e));
            self.map.insert(ident, value.to_meta());
        }
        self
    }
    pub fn build(self) -> Meta { Meta::Object(self.map) }
}

impl<'a> FromMetaError<'a> {
    pub fn expected(expected: &'static str, got: &'a Meta) -> Self {
        FromMetaError::TypeError { expected, got }
    }
}
#[derive(Error, Debug)]
pub enum FromMetaError<'a> {
    #[error("expected {}, got {}", .expected, .got)]
    TypeError {
        expected: &'static str,
        got: &'a Meta,
    },
    #[error("object is missing field {:?}", .field)]
    MissingField { field: &'a str },
}

pub trait FromMeta: Sized {
    fn from_meta(meta: &Meta) -> Result<Self, FromMetaError<'_>>;
}
pub trait ToMeta {
    fn to_meta(&self) -> Meta;
}

impl FromMeta for i32 {
    fn from_meta(meta: &Meta) -> Result<Self, FromMetaError<'_>> {
        match meta {
            Meta::Int(x) => Ok(*x),
            _ => Err(FromMetaError::expected("an integer", meta)),
        }
    }
}

impl FromMeta for u32 {
    fn from_meta(meta: &Meta) -> Result<Self, FromMetaError<'_>> {
        Ok(i32::from_meta(meta)? as u32)
    }
}

impl FromMeta for f32 {
    fn from_meta(meta: &Meta) -> Result<Self, FromMetaError<'_>> {
        match meta {
            Meta::Int(x) => Ok(*x as f32),
            Meta::Float(x) => Ok(*x),
            _ => Err(FromMetaError::expected("a number", meta)),
        }
    }
}

impl FromMeta for BString {
    fn from_meta(meta: &Meta) -> Result<Self, FromMetaError<'_>> {
        match meta {
            Meta::String(x) => Ok(x.clone()),
            _ => Err(FromMetaError::expected("a string", meta)),
        }
    }
}

impl<T: FromMeta> FromMeta for Vec<T> {
    fn from_meta(meta: &Meta) -> Result<Self, FromMetaError<'_>> {
        match meta {
            Meta::Array(xs) => xs.into_iter().map(|x| x.parse()).collect(),
            _ => Err(FromMetaError::expected("an array", meta)),
        }
    }
}

impl<T: FromMeta> FromMeta for [T; 2] {
    fn from_meta(meta: &Meta) -> Result<Self, FromMetaError<'_>> {
        match meta {
            Meta::Array(xs) => match xs.len() {
                2 => Ok([xs[0].parse()?, xs[1].parse()?]),
                _ => Err(FromMetaError::expected("an array of length 2", meta)),
            },
            _ => Err(FromMetaError::expected("an array", meta)),
        }
    }
}

impl<T: FromMeta> FromMeta for [T; 3] {
    fn from_meta(meta: &Meta) -> Result<Self, FromMetaError<'_>> {
        match meta {
            Meta::Array(xs) => match xs.len() {
                3 => Ok([xs[0].parse()?, xs[1].parse()?, xs[2].parse()?]),
                _ => Err(FromMetaError::expected("an array of length 3", meta)),
            },
            _ => Err(FromMetaError::expected("an array", meta)),
        }
    }
}

impl<T: FromMeta> FromMeta for [T; 4] {
    fn from_meta(meta: &Meta) -> Result<Self, FromMetaError<'_>> {
        match meta {
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
impl<T: ToMeta> ToMeta for Vec<T> {
    fn to_meta(&self) -> Meta { Meta::Array(self.iter().map(ToMeta::to_meta).collect()) }
}
impl<T: ToMeta> ToMeta for [T; 2] {
    fn to_meta(&self) -> Meta { Meta::Array(self.iter().map(ToMeta::to_meta).collect()) }
}
impl<T: ToMeta> ToMeta for [T; 3] {
    fn to_meta(&self) -> Meta { Meta::Array(self.iter().map(ToMeta::to_meta).collect()) }
}
impl<T: ToMeta> ToMeta for [T; 4] {
    fn to_meta(&self) -> Meta { Meta::Array(self.iter().map(ToMeta::to_meta).collect()) }
}
