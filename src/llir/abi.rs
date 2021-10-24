use crate::pos::Span;
use crate::diagnostic::{Diagnostic, Emitter};
use crate::error::ErrorReported;
use crate::context::{CompilerContext, defs};
use crate::value::{self, ScalarType};
use crate::game::InstrLanguage;

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
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArgEncoding {
    /// `S` in mapfile. 4-byte integer immediate or register.  Displayed as signed.
    Dword,
    /// `s` in mapfile. 2-byte integer immediate.  Displayed as signed.
    Word,
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
    /// `N` in mapfile. Dword index of an anm script.  When decompiled, prefers to use the name of that script.
    Script,
    /// `n` in mapfile. Dword index of an anm sprite.  When decompiled, prefers to use the name of that sprite.
    Sprite,
    /// `E` in mapfile. Dword index of an olde-format ECL sub.  When decompiled, prefers to use the name of that sub.
    Sub,
    /// `z(bs=<int>)` or `m(bs=<int>;mask=<int>,<int>,<int>)` in mapfile.
    ///
    /// A null-terminated string argument which must be the last argument in the signature and
    /// consists of all remaining bytes. When written, it is padded to a multiple of `bs`
    /// bytes.
    ///
    /// The string can be encoded with an accelerating XOR mask. The three integers supplied to
    /// `mask` are the initial mask value, the initial velocity, and acceleration.
    ///
    /// Adding `;furibug` replicates a strange quirk in TH12+ MSG files related to strings that represent furigana.
    String {
        block_size: usize,
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
pub enum TimelineArgKind {
    /// `T(_)`.  Unused timeline argument that won't appear in the AST signature.
    ///
    /// It can still be explicitly set via `@arg0=`.
    Unused,
    /// `T(e)`.  Timeline argument that is an ECL sub index.
    ///
    /// This mostly impacts decompilation, as it will try to decompile this arg to a symbol name.
    EclSub,
    /// `T(m)`.  Timeline argument that is a MSG script index.
    MsgSub,
}

impl ArgEncoding {
    pub fn descr(&self) -> &'static str {
        match self {
            Self::Dword => "dword integer",
            Self::Word => "word-sized integer",
            Self::JumpOffset => "jump offset",
            Self::JumpTime => "jump time",
            Self::Padding => "padding",
            Self::Color => "hex integer",
            Self::Float => "float",
            Self::Script => "script id",
            Self::Sprite => "sprite id",
            Self::Sub => "sub id",
            Self::String { .. } => "string",
            Self::TimelineArg { .. } => "timeline arg0",
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

    pub fn arg_encodings(&self) -> impl crate::VeclikeIterator<Item=ArgEncoding> + '_ {
        self.encodings.iter().copied()
    }

    pub fn create_signature(&self, ctx: &mut CompilerContext) -> defs::Signature {
        abi_to_signature(self, ctx)
    }

    pub fn validate_against_language(&self, language: InstrLanguage, emitter: &dyn Emitter) -> Result<(), ErrorReported> {
        // NOTE: Normally the authority on timeline extra arguments is InstrFormat, but we want
        //       this check to run long before any InstrFormats are created.
        //
        //       Hence, we check based on the language instead.
        let sig_has_arg0 = matches!(self.encodings.get(0), Some(ArgEncoding::TimelineArg { .. }));
        let lang_has_arg0 = language == InstrLanguage::Timeline;
        if sig_has_arg0 && !lang_has_arg0 {
            return Err(emitter.as_sized().emit(error!("T(...) is invalid outside of timeline languages")));
        } else if !sig_has_arg0 && lang_has_arg0 {
            return Err(emitter.as_sized().emit(error!("timeline instruction is missing T(...) argument")));
        }
        Ok(())
    }

    pub fn parse(span: Span, s: &str, emitter: &dyn Emitter) -> Result<Self, ErrorReported> {
        InstrAbi::from_encodings(span, {
            crate::parse::abi::PARSER.parse(emitter, s)
                .map_err(|syntax_err| emitter.as_sized().emit(error!(
                    message("signature syntax error: {}", syntax_err),
                    primary(span, "{}", syntax_err),
                )))?
        }).map_err(|validation_err| emitter.as_sized().emit(validation_err))
    }
}

impl ArgEncoding {
    pub fn expr_type(self) -> ScalarType {
        match self {
            | ArgEncoding::JumpOffset
            | ArgEncoding::JumpTime
            | ArgEncoding::Padding
            | ArgEncoding::Color
            | ArgEncoding::Word
            | ArgEncoding::Sprite
            | ArgEncoding::Script
            | ArgEncoding::Sub
            | ArgEncoding::Dword
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
    let o_count = encodings.iter().filter(|&&c| c == Enc::JumpOffset).count();
    let t_count = encodings.iter().filter(|&&c| c == Enc::JumpTime).count();

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

    if encodings.iter().rev().skip(1).any(|c| matches!(c, Enc::String { .. })) {
        return err(format!("'z' or 'm' arguments can only appear at the very end"));
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
    defs::Signature {
        return_ty: sp!(value::ExprType::Void),
        params: abi.encodings.iter().enumerate().flat_map(|(index, &enc)| {
            let (ty, default) = match enc {
                | ArgEncoding::Dword
                | ArgEncoding::Word
                | ArgEncoding::Color
                | ArgEncoding::JumpOffset
                | ArgEncoding::JumpTime
                | ArgEncoding::Sprite
                | ArgEncoding::Script
                | ArgEncoding::Sub
                | ArgEncoding::TimelineArg(TimelineArgKind::EclSub)
                | ArgEncoding::TimelineArg(TimelineArgKind::MsgSub)
                => (ScalarType::Int, None),

                | ArgEncoding::TimelineArg(TimelineArgKind::Unused)
                => return None,

                | ArgEncoding::Padding
                => (ScalarType::Int, Some(sp!(0.into()))),

                | ArgEncoding::Float
                => (ScalarType::Float, None),

                | ArgEncoding::String { .. }
                => (ScalarType::String, None),
            };
            let name = sp!(ctx.resolutions.attach_fresh_res(format!("arg_{}", index + 1).parse().unwrap()));
            let var_ty = value::VarType::Typed(ty);
            ctx.define_local(name.clone(), var_ty);

            Some(defs::SignatureParam { default, name, ty: sp!(var_ty) })
        }).collect(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(s: &str) -> Result<InstrAbi, ErrorReported> {
        let emitter = crate::diagnostic::RootEmitter::new_captured();
        InstrAbi::parse(Span::NULL, s, &emitter)
    }

    #[test]
    fn test_parse() {
        assert_eq!(parse("SSf").unwrap(), InstrAbi::from_encodings(Span::NULL, vec![Enc::Dword, Enc::Dword, Enc::Float]).unwrap());
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
