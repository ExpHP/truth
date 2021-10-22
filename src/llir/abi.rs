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
    pub fn from_encodings(encodings: Vec<ArgEncoding>) -> Result<Self, Diagnostic> {
        validate(&encodings)?;
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
        //       this check to run long before any InsrFormats are created.
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

    pub fn parse(s: &str, emitter: &dyn Emitter) -> Result<Self, ErrorReported> {
        InstrAbi::from_encodings({
            crate::parse::abi::PARSER.parse(emitter, s)
                .map_err(|e| emitter.as_sized().emit(error!("{}", e)))?
        }).map_err(|e| emitter.as_sized().emit(e))
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


fn validate(encodings: &[ArgEncoding]) -> Result<(), Diagnostic> {
    let o_count = encodings.iter().filter(|&&c| c == Enc::JumpOffset).count();
    let t_count = encodings.iter().filter(|&&c| c == Enc::JumpTime).count();

    for &(char, count) in &[('o', o_count), ('t', t_count)][..] {
        if count > 1 {
            return Err(error!("signature has multiple '{}' args", char));
        }
    }
    if t_count == 1 && o_count == 0 {
        return Err(error!("signature has a 't' arg without an 'o' arg"));
    }

    if encodings.iter().skip(1).any(|c| matches!(c, Enc::TimelineArg { .. })) {
        return Err(error!("'T()' arguments may only appear at the beginning of a signature"));
    }

    if encodings.iter().rev().skip(1).any(|c| matches!(c, Enc::String { .. })) {
        return Err(error!("'z' or 'm' arguments can only appear at the very end"));
    }

    let trailing_pad_count = encodings.iter().rev().take_while(|c| matches!(c, Enc::Padding)).count();
    let total_pad_count = encodings.iter().filter(|c| matches!(c, Enc::Padding)).count();
    if total_pad_count != trailing_pad_count {
        // this restriction is required because Padding produces signatures with optional args.
        return Err(error!("non-'_' arguments cannot come after '_' arguments"));
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

/// Helper for inspecting the signature of a jump related intrinsic to determine the
/// order of the arguments.  (which varies from language to language)
pub struct JumpIntrinsicArgOrder<T> {
    pub offset: T,
    /// This will be `None` if the signature has no time arguments. (basically just TH06 ANM)
    pub time: Option<T>,
    /// The rest of the args in the order they were found.
    pub other_args: Vec<T>,
    /// Encodings of `other_args`.
    pub other_arg_encodings: Vec<ArgEncoding>,
}

impl<T> JumpIntrinsicArgOrder<T> {
    /// Pull out the items in an iterator that correspond to jump arguments.
    pub fn from_iter(args: impl ExactSizeIterator<Item=T>, abi: &InstrAbi, expected_extra_args: usize) -> Result<Self, Diagnostic> {
        if args.len() != abi.arg_encodings().len() {
            return Err(error!(
                "jump intrinsic got {} args but its signature has {}. (signature is probably wrong)",
                args.len(), abi.arg_encodings().len(),
            ));
        }

        let mut offset = None;
        let mut time = None;
        let mut other_args = vec![];
        let mut other_arg_encodings = vec![];
        for (arg, encoding) in args.zip(abi.arg_encodings()) {
            match encoding {
                ArgEncoding::JumpOffset => offset = Some(arg),
                ArgEncoding::JumpTime => time = Some(arg),
                _ => {
                    other_args.push(arg);
                    other_arg_encodings.push(encoding);
                },
            }
        }

        if other_args.len() != expected_extra_args {
            let hint = if other_args.len() == expected_extra_args + 1 && time.is_none() {
                r#" (possibly missing "t" in signature)"#
            } else {
                ""
            };
            return Err(error!(
                "jump intrinsic expected {} non-jump args but got {}{}",
                expected_extra_args, other_args.len(), hint
            ));
        }

        match offset {
            Some(offset) => Ok(JumpIntrinsicArgOrder { offset, time, other_args, other_arg_encodings }),
            _ => Err(error!("jump intrinsic signature is missing offset argument")),
        }
    }

    /// Use the given signature to convert this into a list of arguments.
    ///
    /// `other_arg_encodings` does not need to be populated.
    pub fn into_vec(self, abi: &InstrAbi) -> Result<Vec<T>, Diagnostic>
    where T: Clone, // HACK, shouldn't be necessary, we're only cloning a const None
    {
        let nargs = abi.arg_encodings().len();

        let mut out_things = vec![None; nargs];

        // "Clever." Use JumpIntrinsicArgs::from_iter on an iterator of `Item=&mut Option<T>`.
        // Then assign those Options to fill in the vec.
        let mut out_jump = JumpIntrinsicArgOrder::from_iter(out_things.iter_mut(), abi, self.other_args.len())?;
        *out_jump.offset = Some(self.offset);
        for (out_time, time) in out_jump.time.iter_mut().zip(self.time) {
            **out_time = Some(time);
        }
        for (out_arg, arg) in out_jump.other_args.iter_mut().zip(self.other_args) {
            **out_arg = Some(arg);
        }

        // all items should be filled now
        Ok(out_things.into_iter().map(|opt| opt.unwrap()).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(s: &str) -> Result<InstrAbi, ErrorReported> {
        let emitter = crate::diagnostic::RootEmitter::new_captured();
        InstrAbi::parse(s, &emitter)
    }

    #[test]
    fn test_parse() {
        assert_eq!(parse("SSf").unwrap(), InstrAbi::from_encodings(vec![Enc::Dword, Enc::Dword, Enc::Float]).unwrap());
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
