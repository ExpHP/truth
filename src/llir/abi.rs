use crate::diagnostic::{Diagnostic, Emitter};
use crate::error::ErrorReported;
use crate::context::{CompilerContext, defs};
use crate::value::{self, ScalarType};

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
    /// `z(bs=<int>)` or `m(bs=<int>;mask=<int>,<int>,<int>)` in mapfile.
    ///
    /// A null-terminated string argument which must be the last argument in the signature and
    /// consists of all remaining bytes. When written, it is padded to a multiple of `bs`
    /// bytes.
    ///
    /// The string can be encoded with an accelerating XOR mask. The three integers supplied to
    /// `mask` are the initial mask value, the initial velocity, and acceleration.
    String {
        block_size: usize,
        mask: AcceleratingByteMask,
    },
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
            | ArgEncoding::Dword
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
        params: abi.encodings.iter().enumerate().map(|(index, &enc)| {
            let (ty, default) = match enc {
                | ArgEncoding::Dword
                | ArgEncoding::Word
                | ArgEncoding::Color
                | ArgEncoding::JumpOffset
                | ArgEncoding::JumpTime
                | ArgEncoding::Sprite
                | ArgEncoding::Script
                => (ScalarType::Int, None),

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

            defs::SignatureParam { default, name, ty: sp!(var_ty) }
        }).collect(),
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
}
