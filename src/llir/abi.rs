use crate::ast;
use crate::pos::{Sp, Span};
use crate::diagnostic::{Diagnostic, Emitter};
use crate::error::ErrorReported;
use crate::context::{CompilerContext, defs::{self, EnumKey}};
use crate::value::{self, ScalarType};
use crate::game::{Game, LanguageKey};

use ArgEncoding as Enc;

/// A signature for an instruction. (typically parsed from a string in a mapfile)
///
/// The signature of an instruction describes not only the types of its arguments, but also
/// can provide information on how to encode them in binary (e.g. integer width, string padding)
/// and how to present them in a decompiled file (e.g. hexadecimal for colors).
///
/// Like in thtk, signatures are derived from strings.  Parse a signature using [`std::str::FromStr`].
#[derive(Debug, Clone, PartialEq, Eq)]
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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ArgEncoding {
    /// `S` or `s` in mapfile. 4-byte or 2-byte integer immediate or register.  Displayed as signed.
    Integer { size: u8, enum_key: Option<EnumKey> },
    /// `o` in mapfile. Max of one per instruction. Is decoded to a label.
    JumpOffset,
    /// `t` in mapfile. Max of one per instruction, and requires an accompanying `o` arg.
    JumpTime,
    /// `_` in mapfile. Unused 4-byte space after script arguments, optionally displayed as integer in text.
    ///
    /// Only exists in pre-StB STD where instructions have fixed sizes.
    Padding,
    /// `C` in mapfile. 4-byte integer immediate or register, printed as hex when immediate.
    Color,
    /// `f` in mapfile. Single-precision float.
    Float,
    /// `z(bs=<int>)`, `m(bs=<int>;mask=<int>,<int>,<int>)`, or  `m(len=<int>;mask=<int>,<int>,<int>)` in mapfile.
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
    /// `T`. Extra argument for timeline.
    ///
    /// Such an argument may only appear as the first argument in the AST form.
    /// Effectively it makes the first argument sugar for `@arg0=`.
    ///
    /// In the binary encoding, it is stored in the instruction header rather than the args blob.
    TimelineArg(TimelineArgKind),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    /// consists of all remaining bytes. When written, it is padded to a multiple of `bs` bytes.
    Block { block_size: usize },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TimelineArgKind {
    /// `T(s)`.  Timeline argument that is just an integer.
    Word,
    /// `T(_)`.  Unused timeline argument that won't appear in the AST signature.
    ///
    /// It can still be explicitly set via `@arg0=`.
    Unused,
    /// `T(e)`, `T(m)`.  Timeline argument that is an ECL or MSG sub index.
    ///
    /// This mostly impacts decompilation, as it will try to decompile this arg to a symbol name.
    Enum(EnumKey),
}

impl ArgEncoding {
    pub fn dword() -> Self { ArgEncoding::Integer { size: 4, enum_key: None } }

    pub fn descr(&self) -> &'static str {
        match self {
            Self::Integer { size: 2, .. } => "word-sized integer",
            Self::Integer { size: 4, .. } => "dword integer",
            Self::Integer { size: _, .. } => "integer",
            Self::JumpOffset => "jump offset",
            Self::JumpTime => "jump time",
            Self::Padding => "padding",
            Self::Color => "hex integer",
            Self::Float => "float",
            Self::String { .. } => "string",
            Self::TimelineArg { .. } => "timeline arg0",
        }
    }

    pub fn heavy_descr(&self) -> String {
        match self {
            Self::Integer { enum_key: Some(en), size: 4 } => format!("{}", en.heavy_descr()),
            Self::Integer { enum_key: Some(en), size } => format!("{}-byte {}", size, en.heavy_descr()),
            Self::Integer { enum_key: None, size: 2 } => format!("word-sized integer"),
            Self::Integer { enum_key: None, size: 4 } => format!("dword integer"),
            Self::Integer { enum_key: None, size } => format!("{}-byte integer", size),
            Self::TimelineArg(TimelineArgKind::Enum(en)) => format!("{} (in timeline arg0)", en.heavy_descr()),
            _ => self.descr().to_string(),
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

    pub fn create_signature(&self, ctx: &mut CompilerContext) -> defs::Signature {
        abi_to_signature(self, ctx)
    }

    pub fn validate_against_language(&self, abi_span: Span, game: Game, language: LanguageKey, emitter: &dyn Emitter) -> Result<(), ErrorReported> {
        // NOTE: Normally the authority on timeline extra arguments is InstrFormat, but we want
        //       this check to run long before any InstrFormats are created.
        //
        //       Hence, we check based on the language instead.
        let invalid_signature = |message| emitter.as_sized().emit(error!(
            message("{}", message),
            primary(abi_span, "{}", message),
        ));
        let sig_has_arg0 = matches!(self.encodings.get(0), Some(ArgEncoding::TimelineArg { .. }));
        let lang_has_arg0 = language == LanguageKey::Timeline && game < Game::Th08;
        if sig_has_arg0 && !lang_has_arg0 {
            return Err(invalid_signature("T(...) is only valid in th06 and th07 timelines"));
        } else if !sig_has_arg0 && lang_has_arg0 {
            return Err(invalid_signature("timeline instruction is missing T(...) argument"));
        }
        Ok(())
    }

    pub fn parse(span: Span, s: &str, emitter: &dyn Emitter) -> Result<Self, ErrorReported> {
        use crate::parse::lalrparser_util::PanicDisplay;

        InstrAbi::from_encodings(span, {
            // collector for diagnostics without any spans
            let mut diagnostics = vec![];
            let result = crate::parse::abi::PARSER.parse(&mut diagnostics, s);

            // if there's an error payload from LALRPOP itself, add that too
            let result = result.map_err(|e| {
                match e {
                    // one of our own errors; the payload is already in the vec
                    lalrpop_util::ParseError::User { error: PanicDisplay } => {},

                    e => diagnostics.push(error!("{}", e)),
                }
                ErrorReported
            });

            // now emit all of them, pointing to this span
            for mut diagnostic in diagnostics {
                diagnostic.primary(span, format!(""));
                // they may be a mix of warnings and errors, ignore them all and trust `result`
                emitter.as_sized().emit(diagnostic).ignore();
            }

            result?
        }).map_err(|validation_err| emitter.as_sized().emit(validation_err))
    }
}

impl ArgEncoding {
    pub fn expr_type(&self) -> ScalarType {
        match self {
            | ArgEncoding::JumpOffset
            | ArgEncoding::JumpTime
            | ArgEncoding::Padding
            | ArgEncoding::Color
            | ArgEncoding::Integer { .. }
            | ArgEncoding::TimelineArg { .. }
            => ScalarType::Int,

            | ArgEncoding::Float
            => ScalarType::Float,

            | ArgEncoding::String { .. }
            => ScalarType::String,
        }
    }
}

fn validate(abi_span: Span, encodings: &[ArgEncoding]) -> Result<(), Diagnostic> {
    let err = |message: String| Err(error!(
        message("bad signature: {}", message),
        primary(abi_span, "{}", message),
    ));
    let o_count = encodings.iter().filter(|&c| c == &Enc::JumpOffset).count();
    let t_count = encodings.iter().filter(|&c| c == &Enc::JumpTime).count();

    for &(char, count) in &[('o', o_count), ('t', t_count)][..] {
        if count > 1 {
            return err(format!("signature has multiple '{}' args", char));
        }
    }
    if t_count == 1 && o_count == 0 {
        return err(format!("signature has a 't' arg without an 'o' arg"));
    }

    if encodings.iter().skip(1).any(|c| matches!(c, Enc::TimelineArg { .. })) {
        return err(format!("'T()' arguments may only appear at the beginning of a signature"));
    }

    if encodings.iter().rev().skip(1).any(|c| matches!(c, Enc::String { size: StringArgSize::Block { .. }, .. })) {
        return err(format!("'z' or 'm' arguments with 'bs=' can only appear at the very end"));
    }

    let trailing_pad_count = encodings.iter().rev().take_while(|c| matches!(c, Enc::Padding)).count();
    let total_pad_count = encodings.iter().filter(|c| matches!(c, Enc::Padding)).count();
    if total_pad_count != trailing_pad_count {
        // this restriction is required because Padding produces signatures with optional args.
        return err(format!("non-'_' arguments cannot come after '_' arguments"));
    }
    Ok(())
}

fn abi_to_signature(abi: &InstrAbi, ctx: &mut CompilerContext<'_>) -> defs::Signature {
    struct Info {
        ty: ScalarType,
        default: Option<Sp<ast::Expr>>,
        reg_ok: bool,
    }

    defs::Signature {
        return_ty: sp!(value::ExprType::Void),
        params: abi.encodings.iter().enumerate().flat_map(|(index, enc)| {
            let Info { ty, default, reg_ok } = match *enc {
                | ArgEncoding::Integer { .. }
                | ArgEncoding::Color
                => Info { ty: ScalarType::Int, default: None, reg_ok: true },

                | ArgEncoding::JumpOffset
                | ArgEncoding::JumpTime
                | ArgEncoding::TimelineArg(TimelineArgKind::Word)
                | ArgEncoding::TimelineArg(TimelineArgKind::Enum(_))
                => Info { ty: ScalarType::Int, default: None, reg_ok: false },

                | ArgEncoding::TimelineArg(TimelineArgKind::Unused)
                => return None,  // leave out of the signature

                | ArgEncoding::Padding
                => Info { ty: ScalarType::Int, default: Some(sp!(0.into())), reg_ok: true },

                | ArgEncoding::Float
                => Info { ty: ScalarType::Float, default: None, reg_ok: true },

                | ArgEncoding::String { .. }
                => Info { ty: ScalarType::String, default: None, reg_ok: true },
            };
            let name = sp!(ctx.resolutions.attach_fresh_res(format!("arg_{}", index + 1).parse().unwrap()));
            let var_ty = value::VarType::Typed(ty);
            ctx.define_local(name.clone(), var_ty);

            let const_arg_reason = (!reg_ok).then(|| crate::context::defs::ConstArgReason::Encoding(enc.clone()));
            let qualifier = None; // irrelevant, there's no function body for an instruction

            Some(defs::SignatureParam { default, name, ty: sp!(var_ty), qualifier, const_arg_reason })
        }).collect(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(s: &str) -> Result<InstrAbi, ErrorReported> {
        let emitter = crate::diagnostic::RootEmitter::new_captured();
        let (file_id, s) = emitter.files.add("<input>", s.as_bytes()).unwrap();
        InstrAbi::parse(Span::of_full_source(file_id, &s), &s, &emitter)
    }

    #[test]
    fn test_parse() {
        assert_eq!(parse("SSf").unwrap(), InstrAbi::from_encodings(Span::NULL, vec![Enc::dword(), Enc::dword(), Enc::Float]).unwrap());
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
        assert!(parse("T(_)S").is_ok());
        assert!(parse("T(e)").is_ok());
        assert!(parse("ST(e)").is_err());
    }
}
