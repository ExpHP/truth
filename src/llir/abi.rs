use crate::diagnostic::Diagnostic;
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
    /// `z` or `m` in mapfile.
    ///
    /// A null-terminated string argument which must be the last argument in the signature and
    /// consists of all remaining bytes. When written, it is padded to a multiple of `block_size`
    /// bytes.
    ///
    /// Using `m` results `mask: 0x77`.  This masks the string in the binary file by xor-ing
    /// every byte (including the null terminator and padding) with the mask.
    String {
        block_size: usize,
        mask: u8,
    },
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

impl std::str::FromStr for InstrAbi {
    type Err = Diagnostic;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut iter = s.bytes().peekable();

        let mut encodings = vec![];
        while let Some(b) = iter.next() {
            let enc = match b {
                b'S' => ArgEncoding::Dword,
                b's' => ArgEncoding::Word,
                b'C' => ArgEncoding::Color,
                b'o' => ArgEncoding::JumpOffset,
                b't' => ArgEncoding::JumpTime,
                b'f' => ArgEncoding::Float,
                b'_' => ArgEncoding::Padding,
                b'n' => ArgEncoding::Sprite,
                b'N' => ArgEncoding::Script,
                b'z' => ArgEncoding::String { block_size: 4, mask: 0 },
                b'm' => ArgEncoding::String { block_size: 4, mask: 0x77 },
                0x80..=0xff => return Err(error!("non-ascii byte in signature: {:#04x}", b)),
                _ => return Err(error!("bad signature character: {:?}", b as char))
            };
            encodings.push(enc);
        }
        InstrAbi::from_encodings(encodings)
    }
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

#[test]
fn test_parse() {
    let parse = <str>::parse::<InstrAbi>;

    assert_eq!(parse("SSf").unwrap(), InstrAbi::from_encodings(vec![Enc::Dword, Enc::Dword, Enc::Float]).unwrap());
}

#[test]
fn offset_time_restrictions() {
    let parse = <str>::parse::<InstrAbi>;

    assert!(parse("SSot").is_ok());
    assert!(parse("SSt").is_err());
    assert!(parse("SSo").is_ok());
    assert!(parse("SSoto").is_err());
    assert!(parse("SSott").is_err());
}

#[test]
fn string_must_be_at_end() {
    let parse = <str>::parse::<InstrAbi>;

    assert!(parse("z").is_ok());
    assert!(parse("m").is_ok());
    assert!(parse("SSz").is_ok());
    assert!(parse("SSm").is_ok());
    assert!(parse("SzS").is_err());
    assert!(parse("SmS").is_err());
}
