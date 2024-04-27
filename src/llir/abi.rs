use core::fmt;

use crate::ast;
use crate::pos::{Sp, Span, SourceStr};
use crate::diagnostic::{Diagnostic, Emitter};
use crate::error::ErrorReported;
use crate::context::{CompilerContext, defs::{self, TypeColor, auto_enum_names}};
use crate::value::{self, ScalarType};
use crate::game::{Game, LanguageKey};
use crate::parse::abi::abi_ast;

use ArgEncoding as Enc;

/// A signature for an instruction. (typically parsed from a string in a mapfile)
///
/// The signature of an instruction describes not only the types of its arguments, but also
/// can provide information on how to encode them in binary (e.g. integer width, string padding)
/// and how to present them in a decompiled file (e.g. hexadecimal for colors).
///
/// Like in thtk, signatures are derived from strings.  Parse a signature using [`std::str::FromStr`].
#[derive(Debug, Clone, PartialEq)]
pub struct InstrAbi {
    encodings: Vec<ArgEncoding>,
}

/// Type of an argument to an instruction.
///
/// This is a bit more nuanced compared to [`ScalarType`].  Arguments with the same type
/// may have different encodings based on how they are either stored in the file, or on how they
/// may be written in a source file.
///
/// By this notion, [`ArgEncoding`] tends to be more relevant for immediate/literal arguments, while
/// [`ScalarType`] tends to be more relevant for variables.
#[derive(Debug, Clone, PartialEq)]
pub enum ArgEncoding {
    /// `S`, `s`, or `c` in mapfile. Integer immediate or register.  Displayed as signed.
    /// `U`, `u`, or `b` in mapfile. Integer immediate or register.  Displayed as unsigned.
    /// `C` in mapfile. 4-byte integer immediate or register, printed as hex when immediate.
    ///
    /// May be decompiled as an enum or const based on its value.
    ///
    /// The first argument may have `arg0` if it is two bytes large.  This indicates that the argument is
    /// stored in the arg0 header field of the instruction in EoSD and PCB ECL. (which is mapped to the
    /// `@arg0` pseudo-argument in raw instruction syntax)
    Integer {
        size: u8,
        ty_color: Option<TypeColor>,
        arg0: bool,
        immediate: bool,
        extend: bool,
        format: ast::IntFormat
    },
    /// `o` in mapfile. Max of one per instruction. Is decoded to a label.
    JumpOffset,
    /// `t` in mapfile. Max of one per instruction, and requires an accompanying `o` arg.
    JumpTime,
    /// `_` in mapfile. Unused 4-byte space.
    /// `-` in mapfile. Unused 1-byte space.
    Padding { size: u8 },
    /// `f` in mapfile. Single-precision float.
    Float { immediate: bool },
    /// `z(bs=<int>)`, `m(bs=<int>;mask=<int>,<int>,<int>)`, or `m(len=<int>;mask=<int>,<int>,<int>)` in mapfile.
    ///
    /// See [`StringArgSize`] about the size args.
    ///
    /// The string can be encoded with an accelerating XOR mask. The three integers supplied to
    /// `mask` are the initial mask value, the initial velocity, and acceleration.
    ///
    /// Adding `;furibug` replicates a strange quirk in TH12+ MSG files related to strings that represent furigana.
    String {
        size: StringArgSize,
        mask: AcceleratingByteMask,
        furibug: bool,
    },
    /*
    /// `g` in mapfile. Single typed argument
    /// 'G' in mapfile. Double typed argument
    TypedArg {
        is_double: bool,
    },
    /// `v` in mapfile.
    Variadic {
        pattern: Option<Vec<ArgEncoding>>
    },
    */
}

#[derive(Debug, Copy, Clone, PartialEq, PartialOrd)]
pub enum StringArgSize {
    /// A string arg that uses `len=`.
    ///
    /// A fixed length string buffer. Typically a trailing null is required to be present INSIDE the
    /// buffer as in some cases it may be copied to another buffer of identical length.
    /// `;nulless` may be added for specific cases where it is known that the lack of a trailing
    /// null is not an issue.
    Fixed { len: usize, nulless: bool },
    /// A string arg that uses `bs=`.
    ///
    /// A null-terminated string argument which **can only be the final argument**, and
    /// consists of all remaining bytes. When written, a null terminator is appended and it is padded
    /// to a multiple of `bs` bytes.
    ToBlobEnd { block_size: usize },
    /// A string arg that uses the `p` type to be length-prefixed.
    ///
    /// This is a Pascal-type string which stores the total length (including null + padding) followed
    /// by the data.  When written, a null terminator is appended and it is padded to a multiple of
    /// `bs` bytes.
    Pascal { block_size: usize },
}

impl ArgEncoding {
    pub fn dword() -> Self { ArgEncoding::Integer { size: 4, ty_color: None, arg0: false, immediate: false, extend: false, format: ast::IntFormat { unsigned: false, radix: ast::IntRadix::Dec } } }

    pub fn static_descr(&self) -> &'static str {
        match self {
            Self::Integer { size: 1, .. } => "byte-sized integer",
            Self::Integer { size: 2, .. } => "word-sized integer",
            Self::Integer { size: 4, .. } => "dword integer",
            //Self::Integer { size: 8, .. } => "qword integer",
            Self::Integer { size: _, .. } => "integer",
            Self::JumpOffset => "jump offset",
            Self::JumpTime => "jump time",
            Self::Padding { size: 4 } => "dword padding",
            Self::Padding { size: 1 } => "byte padding",
            Self::Padding { size: _ } => "padding",
            Self::Float { .. } => "float",
            Self::String { .. } => "string",
            //Self::TypedArg { .. } => "type cast argument",
            //Self::Variadic { .. } => "variadic",
        }
    }

    pub fn descr(&self) -> impl fmt::Display + '_ {
        struct Impl<'a>(&'a Enc);

        impl fmt::Display for Impl<'_> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                match self.0 {
                    Enc::Integer { arg0: true, .. } => {
                        let mut temp = self.0.clone();
                        write!(f, "{} (in timeline arg0)", match &mut temp {
                            Enc::Integer { arg0, .. } => { *arg0 = false; temp },
                            _ => unreachable!(),
                        }.descr())
                    },
                    Enc::Integer { ty_color: Some(en), size: 4, .. } => write!(f, "{}", en.descr()),
                    Enc::Integer { ty_color: Some(en), size, .. } => write!(f, "{size}-byte {}", en.descr()),
                    Enc::Integer { ty_color: None, size: 1, .. } => write!(f, "byte-sized integer"),
                    Enc::Integer { ty_color: None, size: 2, .. } => write!(f, "word-sized integer"),
                    Enc::Integer { ty_color: None, size: 4, .. } => write!(f, "dword integer"),
                    //Enc::Integer { ty_color: None, size: 8, .. } => write!(f, "qword integer"),
                    Enc::Integer { ty_color: None, size, .. } => write!(f, "{size}-byte integer"),
                    enc => write!(f, "{}", enc.static_descr()),
                }
            }
        }

        Impl(self)
    }

    pub fn contributes_to_param_mask(&self) -> bool {
        !matches!(self, Self::Padding { .. })
    }
    
    pub fn is_always_immediate(&self) -> bool {
        match self {
            | Self::String { .. }
            | Self::JumpOffset
            | Self::JumpTime
            | Self::Padding { .. }
            | Self::Integer { immediate: true, .. }
            | Self::Float { immediate: true, .. }
            => true,

            | Self::Integer { immediate: false, .. }
            | Self::Float { immediate: false, .. }
            //| Self::TypedArg { .. }
            //| Self::Variadic { .. }
            => false,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AcceleratingByteMask { pub mask: u8, pub vel: u8, pub accel: u8 }

impl AcceleratingByteMask {
    /// Returns a bit mask where every byte has the same mask.
    pub fn constant(mask: u8) -> Self {
        AcceleratingByteMask { mask, vel: 0, accel: 0 }
    }
}

impl Iterator for AcceleratingByteMask {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        let value = self.mask;
        self.mask = u8::wrapping_add(self.mask, self.vel);
        self.vel = u8::wrapping_add(self.vel, self.accel);
        Some(value)
    }
}

impl InstrAbi {
    pub fn from_encodings(span: Span, encodings: Vec<ArgEncoding>) -> Result<Self, Diagnostic> {
        validate(span, &encodings)?;
        Ok(InstrAbi { encodings })
    }

    pub fn arg_encodings(&self) -> impl crate::VeclikeIterator<Item=&'_ ArgEncoding> + '_ {
        self.encodings.iter()
    }

    pub fn create_signature(&self, abi_span: Span, ctx: &mut CompilerContext) -> defs::Signature {
        abi_to_signature(self, abi_span, ctx)
    }

    pub fn validate_against_language(&self, abi_span: Span, game: Game, language: LanguageKey, emitter: &dyn Emitter) -> Result<(), ErrorReported> {
        // NOTE: Normally the authority on timeline extra arguments is InstrFormat, but we want
        //       this check to run long before any InstrFormats are created.
        //
        //       Hence, we check based on the language instead.
        let invalid_signature = |message| emitter.as_sized().emit(error!(
            message("{message}"),
            primary(abi_span, ""),
        ));
        let sig_has_arg0 = matches!(self.encodings.get(0), Some(ArgEncoding::Integer { arg0: true, .. }));
        let lang_has_arg0 = language == LanguageKey::Timeline && game < Game::Th08;
        if sig_has_arg0 && !lang_has_arg0 {
            return Err(invalid_signature("arg0 args are only valid in th06 and th07 timelines"));
        }
        Ok(())
    }

    pub fn parse(s: SourceStr<'_>, emitter: &dyn Emitter) -> Result<Self, ErrorReported> {
        let abi_ast = crate::parse::abi::parse_abi(s, &emitter)?;
        InstrAbi::from_encodings(s.span(), {
            abi_ast.params.iter()
                .map(|param| arg_encoding_from_attrs(&param, emitter))
                .collect::<Result<_, _>>()?
        }).map_err(|e| emitter.as_sized().emit(e))
    }
}

impl ArgEncoding {
    pub fn expr_type(&self) -> ScalarType {
        match self {
            | ArgEncoding::JumpOffset
            | ArgEncoding::JumpTime
            | ArgEncoding::Padding { .. }
            | ArgEncoding::Integer { .. }
            => ScalarType::Int,

            | ArgEncoding::Float { .. }
            => ScalarType::Float,

            | ArgEncoding::String { .. }
            => ScalarType::String,
        }
    }
}

// =============================================================================

fn arg_encoding_from_attrs(param: &abi_ast::Param, emitter: &dyn Emitter) -> Result<ArgEncoding, ErrorReported> {
    if let Some(encoding) = int_from_attrs(param, emitter)? {
        Ok(encoding)
    } else if let Some(encoding) = float_from_attrs(param, emitter)? {
        Ok(encoding)
    } else if let Some(encoding) = string_from_attrs(param, emitter)? {
        Ok(encoding)
    } else if let Some(encoding) = other_from_attrs(param, emitter)? {
        Ok(encoding)
    } else {
        Err(emitter.as_sized().emit(error!(
            message("unknown arg format '{}'", param.format_char),
            primary(param.format_char, ""),
        )))
    }
}

fn int_from_attrs(param: &abi_ast::Param, emitter: &dyn Emitter) -> Result<Option<ArgEncoding>, ErrorReported> {
    let (size, unsigned, mut hex_radix, default_ty_color) = match param.format_char.value {
        // FIXME: Uu should be unsigned but I'm not sure yet if I want  `i(signed)`, `i(unsigned)`, or `i(sign=1)`
        'S' => (4u8, false, false, None),
        's' => (2u8, false, false, None),
        'c' => (1u8, false, false, None),
        'U' => (4u8, true, false, None),
        'u' => (2u8, true, false, None),
        'b' => (1u8, true, false, None),
        'n' => (4u8, false, false, Some(TypeColor::Enum(auto_enum_names::anm_sprite()))),
        'N' => (4u8, false, false, Some(TypeColor::Enum(auto_enum_names::anm_script()))),
        'E' => (4u8, false, false, Some(TypeColor::Enum(auto_enum_names::ecl_sub()))),
        'C' => (4u8, true, true, None),
        _ => return Ok(None),  // not an integer
    };

    param.clone().deserialize_attributes(emitter, |de| {
        let user_ty_color = de.accept_value("enum")?.map(|ident| TypeColor::Enum(ident.value));
        let arg0 = de.accept_flag("arg0")?;
        let imm = de.accept_flag("imm")?;
        let is_hex = de.accept_flag("hex")?;
        let extend = de.accept_flag("extend")?;

        if let Some(arg0_flag) = arg0 {
            if size.wrapping_sub(1) >= 2 {
                return Err(emitter.as_sized().emit(error!(
                    message("timeline arg0 must be word-sized or less ('s', 'u', 'c', or 'b')"),
                    primary(arg0_flag, ""),
                )));
            }
        }
        
        if is_hex.is_some() {
            hex_radix = true;
        }

        let radix = match hex_radix {
            false => ast::IntRadix::Dec,
            true => ast::IntRadix::Hex,
        };

        Ok(Some(ArgEncoding::Integer {
            size,
            ty_color: user_ty_color.or(default_ty_color),
            arg0: arg0.is_some(),
            immediate: imm.is_some(),
            extend: extend.is_some(),
            format: ast::IntFormat { unsigned, radix },
        }))
    })
}

fn float_from_attrs(param: &abi_ast::Param, emitter: &dyn Emitter) -> Result<Option<ArgEncoding>, ErrorReported> {
    match param.format_char.value {
        'f' => param.clone().deserialize_attributes(emitter, |de| {
            //let user_ty_color = de.accept_value("enum")?.map(|ident| TypeColor::Enum(ident.value));
            let imm = de.accept_flag("imm")?;

            Ok(Some(ArgEncoding::Float {
                //ty_color: user_ty_color.or(default_ty_color),
                immediate: imm.is_some(),
            }))
        }),
        _ => Ok(None)
    }
}

fn string_from_attrs(param: &abi_ast::Param, emitter: &dyn Emitter) -> Result<Option<ArgEncoding>, ErrorReported> {
    struct LenPrefixed(bool); // self-documenting bool

    let (default_mask, is_len_prefixed) = match param.format_char.value {
        'z' => (Some([0,0,0]), LenPrefixed(false)),
        'm' => (None, LenPrefixed(false)),
        'p' => (Some([0,0,0]), LenPrefixed(true)),
        'P' => (Some([0,0,0]), LenPrefixed(true)),
        _ => return Ok(None),  // not a string
    };

    param.clone().deserialize_attributes(emitter, |de| {
        let user_mask = de.accept_value::<[u8; 3]>("mask")?;
        let furibug = de.accept_flag("furibug")?;
        let size = {
            let user_len = de.accept_value::<u32>("len")?;
            let user_bs = de.accept_value::<u32>("bs")?;
            match (user_len, user_bs, is_len_prefixed) {
                (None, Some(bs), LenPrefixed(false)) => StringArgSize::ToBlobEnd {
                    block_size: bs.value as _,
                },
                (None, Some(bs), LenPrefixed(true)) => StringArgSize::Pascal {
                    block_size: bs.value as _,
                },
                (Some(len), None, LenPrefixed(false)) => StringArgSize::Fixed {
                    len: len.value as _,
                    nulless: de.accept_flag("nulless")?.is_some(),
                },
                (Some(len), None, LenPrefixed(true)) => return Err(emitter.as_sized().emit(error!(
                    message("'len' attribute is not supported by '{}'", param.format_char),
                    primary(len, ""),
                ))),
                (None, None, _) => return Err(emitter.as_sized().emit(error!(
                    message("missing length attribute ('len' or 'bs') for '{}'", param.format_char),
                    primary(param.format_char, ""),
                ))),
                (Some(len), Some(bs), _) => return Err(emitter.as_sized().emit(error!(
                    message("mutually exclusive attributes 'len' and 'bs' in '{}' format", param.format_char),
                    primary(len, ""),
                    primary(bs, ""),
                ))),
            }
        };

        Ok(Some(ArgEncoding::String {
            mask: {
                user_mask.map(|sp| sp.value).or(default_mask)
                    .ok_or_else(|| de.error_missing("mask"))
                    .map(|[mask, vel, accel]| AcceleratingByteMask { mask, vel, accel })?
            },
            size,
            furibug: furibug.is_some(),
        }))
    })
}

fn other_from_attrs(param: &abi_ast::Param, _emitter: &dyn Emitter) -> Result<Option<ArgEncoding>, ErrorReported> {
    match param.format_char.value {
        'o' => Ok(Some(ArgEncoding::JumpOffset)),
        't' => Ok(Some(ArgEncoding::JumpTime)),
        '_' => Ok(Some(ArgEncoding::Padding { size: 4 })),
        '-' => Ok(Some(ArgEncoding::Padding { size: 1 })),
        //'g' => Ok(Some(ArgEncoding::TypedArg { is_double: false })),
        //'G' => Ok(Some(ArgEncoding::TypedArg { is_double: true })),
        //'v' => 
        _ => Ok(None),
    }
}

fn validate(abi_span: Span, encodings: &[ArgEncoding]) -> Result<(), Diagnostic> {
    let err = |message: String| Err(error!(
        message("bad signature: {message}"),
        primary(abi_span, ""),
    ));
    let o_count = encodings.iter().filter(|&c| c == &Enc::JumpOffset).count();
    let t_count = encodings.iter().filter(|&c| c == &Enc::JumpTime).count();

    for &(char, count) in &[('o', o_count), ('t', t_count)][..] {
        if count > 1 {
            return err(format!("signature has multiple '{char}' args"));
        }
    }
    if t_count == 1 && o_count == 0 {
        return err(format!("signature has a 't' arg without an 'o' arg"));
    }

    if encodings.iter().skip(1).any(|c| matches!(c, Enc::Integer { arg0: true, .. })) {
        return err(format!("'(arg0)' arguments may only appear at the beginning of a signature"));
    }

    if encodings.iter().rev().skip(1).any(|c| matches!(c, Enc::String { size: StringArgSize::ToBlobEnd { .. }, .. })) {
        return err(format!("'z' or 'm' arguments with 'bs=' can only appear at the very end"));
    }
    Ok(())
}

// =============================================================================

fn abi_to_signature(abi: &InstrAbi, abi_span: Span, ctx: &mut CompilerContext<'_>) -> defs::Signature {
    struct Info {
        ty: ScalarType,
        ty_color: Option<TypeColor>,
        default: Option<Sp<ast::Expr>>,
        reg_ok: bool,
    }

    defs::Signature {
        return_ty: sp!(value::ExprType::Void),
        params: abi.encodings.iter().filter(|enc| !matches!(*enc, ArgEncoding::Padding { .. })).enumerate().flat_map(|(index, enc)| {
            let Info { ty, default, reg_ok, ty_color } = match *enc {
                | ArgEncoding::Integer { arg0: false, ref ty_color, .. }
                => Info { ty: ScalarType::Int, default: None, reg_ok: true, ty_color: ty_color.clone() },

                | ArgEncoding::Integer { arg0: true, ref ty_color, .. }
                => Info { ty: ScalarType::Int, default: None, reg_ok: false, ty_color: ty_color.clone() },

                | ArgEncoding::JumpOffset
                | ArgEncoding::JumpTime
                => Info { ty: ScalarType::Int, default: None, reg_ok: false, ty_color: None },

                | ArgEncoding::Padding { .. }
                => Info { ty: ScalarType::Int, default: Some(sp!(0.into())), reg_ok: false, ty_color: None },

                | ArgEncoding::Float { .. }
                => Info { ty: ScalarType::Float, default: None, reg_ok: true, ty_color: None },

                | ArgEncoding::String { .. }
                => Info { ty: ScalarType::String, default: None, reg_ok: true, ty_color: None },
            };
            let name = sp!(abi_span => ctx.resolutions.attach_fresh_res(ident!("arg_{}", index + 1)));
            let var_ty = value::VarType::Typed(ty);
            ctx.define_local(name.clone(), var_ty);

            let const_arg_reason = (!reg_ok).then(|| crate::context::defs::ConstArgReason::Encoding(enc.clone()));
            let qualifier = None; // irrelevant, there's no function body for an instruction

            let ty = sp!(abi_span => var_ty);
            let ty_color = ty_color.map(|x| sp!(abi_span => x));

            Some(defs::SignatureParam {
                default, ty, qualifier, const_arg_reason, ty_color,
                name: Some(name), useful_span: Span::NULL,
            })
        }).collect(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(s: &str) -> Result<InstrAbi, ErrorReported> {
        let emitter = crate::diagnostic::RootEmitter::new_captured();
        let (file_id, s) = emitter.files.add("<input>", s.as_bytes()).unwrap();
        InstrAbi::parse(SourceStr::from_full_source(file_id, &s), &emitter)
    }

    #[test]
    fn test_parse() {
        assert_eq!(parse("SSf").unwrap(), InstrAbi::from_encodings(Span::NULL, vec![Enc::dword(), Enc::dword(), Enc::Float { immediate: false }]).unwrap());
    }

    #[test]
    fn offset_time_restrictions() {
        assert!(parse("SSot").is_ok());
        assert!(parse("SSt").is_err());
        assert!(parse("SSo").is_ok());
        assert!(parse("SSoto").is_err());
        assert!(parse("SSott").is_err());
    }

    #[test]
    fn string_must_be_at_end() {
        assert!(parse("z(bs=4)").is_ok());
        assert!(parse("m(bs=4;mask=0,0,0)").is_ok());
        assert!(parse("SSz(bs=4)").is_ok());
        assert!(parse("SSm(bs=4;mask=0,0,0)").is_ok());
        assert!(parse("Sz(bs=4)S").is_err());
        assert!(parse("Sm(bs=4;mask=0,0,0)S").is_err());
    }

    #[test]
    fn timeline_must_be_at_beginning() {
        assert!(parse("s(arg0)S").is_ok());
        assert!(parse("s(arg0)").is_ok());
        assert!(parse("Ss(arg0)").is_err());
    }
}
