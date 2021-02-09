use crate::error::SimpleError;
use crate::type_system::{ScalarType, Signature, SignatureParam, TypeSystem};

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
    pub fn from_encodings(encodings: Vec<ArgEncoding>) -> Result<Self, SimpleError> {
        validate(&encodings)?;
        Ok(InstrAbi { encodings })
    }

    pub fn arg_encodings(&self) -> impl crate::VeclikeIterator<Item=ArgEncoding> + '_ {
        self.encodings.iter().copied()
    }

    // /// Get the minimum number of args allowed in the AST.
    // pub fn min_args(&self) -> usize { self.count_args_incl_padding() - self.count_padding() }
    // /// Get the maximum number of args allowed in the AST.
    // pub fn max_args(&self) -> usize { self.count_args_incl_padding() }
    //
    // fn count_args_incl_padding(&self) -> usize {
    //     self.encodings.len()
    // }
    //
    // fn count_padding(&self) -> usize {
    //     self.arg_encodings().rev().position(|c| c != Enc::Padding)
    //         .unwrap_or(self.count_args_incl_padding())
    // }
    //
    // pub fn split_padding<'a, T>(&self, args: &'a [T]) -> Option<(&'a [T], &'a [T])> {
    //     let i = self.count_args_incl_padding() - self.count_padding();
    //     if i <= args.len() {
    //         Some(args.split_at(i))
    //     } else { None }
    // }

    pub fn create_signature(&self, ty_ctx: &mut TypeSystem) -> Signature {
        abi_to_signature(self, ty_ctx)
    }
}

impl ArgEncoding {
    pub fn expr_type(self) -> ScalarType {
        match self {
            ArgEncoding::JumpOffset |
            ArgEncoding::JumpTime |
            ArgEncoding::Padding |
            ArgEncoding::Color |
            ArgEncoding::Word |
            ArgEncoding::Dword => ScalarType::Int,
            ArgEncoding::Float => ScalarType::Float,
            ArgEncoding::String { .. } => ScalarType::String,
        }
    }
}


fn validate(encodings: &[ArgEncoding]) -> Result<(), SimpleError> {
    let o_count = encodings.iter().filter(|&&c| c == Enc::JumpOffset).count();
    let t_count = encodings.iter().filter(|&&c| c == Enc::JumpTime).count();

    for &(char, count) in &[('o', o_count), ('t', t_count)][..] {
        if count > 1 {
            anyhow::bail!("signature has multiple '{}' args", char);
        }
    }
    if t_count == 1 && o_count == 0 {
        anyhow::bail!("signature has a 't' arg without an 'o' arg");
    }

    if encodings.iter().rev().skip(1).any(|c| matches!(c, Enc::String { .. })) {
        anyhow::bail!("'z' or 'm' arguments can only appear at the very end");
    }

    let trailing_pad_count = encodings.iter().rev().take_while(|c| matches!(c, Enc::Padding)).count();
    let total_pad_count = encodings.iter().filter(|c| matches!(c, Enc::Padding)).count();
    if total_pad_count != trailing_pad_count {
        // this restriction is required because Padding produces signatures with optional args.
        anyhow::bail!("non-'_' arguments cannot come after '_' arguments");
    }
    Ok(())
}

impl std::str::FromStr for InstrAbi {
    type Err = SimpleError;

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
                b'n' => ArgEncoding::Dword, // FIXME sprite
                b'N' => ArgEncoding::Dword, // FIXME script
                b'z' => ArgEncoding::String { block_size: 4, mask: 0 },
                b'm' => ArgEncoding::String { block_size: 4, mask: 0x77 },
                0x80..=0xff => anyhow::bail!("non-ascii byte in signature: {:#04x}", b),
                _ => anyhow::bail!("bad signature character: {:?}", b as char)
            };
            encodings.push(enc);
        }
        InstrAbi::from_encodings(encodings)
    }
}

fn abi_to_signature(abi: &InstrAbi, ty_ctx: &mut TypeSystem) -> Signature {
    Signature {
        return_ty: None,
        params: abi.encodings.iter().enumerate().map(|(index, &enc)| {
            let (ty, default) = match enc {
                | ArgEncoding::Dword
                | ArgEncoding::Word
                | ArgEncoding::Color
                | ArgEncoding::JumpOffset
                | ArgEncoding::JumpTime
                => (ScalarType::Int, None),

                | ArgEncoding::Padding
                => (ScalarType::Int, Some(sp!(0.into()))),

                | ArgEncoding::Float
                => (ScalarType::Float, None),

                | ArgEncoding::String { .. }
                => (ScalarType::String, None),
            };
            let name = format!("arg_{}", index + 1).parse().unwrap();
            let name = ty_ctx.add_local(sp!(name), Some(ty));

            SignatureParam { default, name, ty: sp!(ty) }
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
