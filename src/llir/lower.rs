use std::collections::{HashMap};

use super::{unsupported, SimpleArg};
use crate::llir::{RawInstr, InstrFormat, ArgEncoding, ScalarType};
use crate::error::{GatherErrorIteratorExt, CompileError};
use crate::pos::{Sp, Span};
use crate::ast;
use crate::resolve::DefId;
use crate::ident::{Ident};
use crate::context::{CompilerContext, Defs};
use crate::io::{Encoded, DEFAULT_ENCODING};

mod stackless;

/// An intermediate representation that is only used during lowering.
///
/// In addition to instructions, it has a couple of extra things that are handled via
/// some post-processing steps.
#[derive(Debug, Clone, PartialEq)]
enum LowerStmt {
    /// Represents a single instruction in the compiled file.
    Instr(LowerInstr),
    /// An intrinsic that represents a label that can be jumped to.
    Label { time: i32, label: Sp<Ident> },
    /// An intrinsic that begins the scope of a register-allocated local.
    RegAlloc { def_id: DefId, cause: Span },
    /// An intrinsic that ends the scope of a register-allocated local.
    RegFree { def_id: DefId },
}

/// An instruction that needs just a bit more postprocessing to convert it into a [`RawInstr`].
#[derive(Debug, Clone, PartialEq)]
struct LowerInstr {
    time: i32,
    opcode: u16,
    /// Value provided by user via `@mask=`, which will override the automatically-computed param mask.
    user_param_mask: Option<u16>,
    args: LowerArgs,
}

#[derive(Debug, Clone, PartialEq)]
enum LowerArgs {
    /// The user provided normal arguments, which at this point we have largely reduced down to immediate
    /// values and registers.
    Known(Vec<Sp<LowerArg>>),
    /// The user provided `@blob=`.  In this case, it is okay for the instruction's ABI to not be known.
    Unknown(Sp<Vec<u8>>),
}

#[derive(Debug, Clone, PartialEq)]
enum LowerArg {
    /// A fully encoded argument (an immediate or a register).
    ///
    /// All arguments are eventually lowered to this form.
    Raw(SimpleArg),
    /// A reference to a register-allocated local.
    Local { def_id: DefId, read_ty: ScalarType },
    /// A label that has not yet been converted to an integer argument.
    Label(Ident),
    /// A `timeof(label)` that has not yet been converted to an integer argument.
    TimeOf(Ident),
}

impl LowerArg {
    /// Call this at a time when the arg is known to have a fully resolved value.
    ///
    /// Such times are:
    /// * During decompilation.
    /// * Within [`InstrFormat::write_instr`].
    #[track_caller]
    pub fn expect_raw(&self) -> &SimpleArg {
        match self {
            LowerArg::Raw(x) => x,
            _ => panic!("unexpected unresolved argument (bug!): {:?}", self),
        }
    }
}

pub fn lower_sub_ast_to_instrs(
    instr_format: &dyn InstrFormat,
    code: &[Sp<ast::Stmt>],
    ctx: &mut CompilerContext<'_>,
) -> Result<Vec<RawInstr>, CompileError> {
    use stackless::{Lowerer, assign_registers};

    let mut lowerer = Lowerer {
        out: vec![],
        intrinsic_instrs: instr_format.intrinsic_instrs(),
        ctx,
        instr_format,
    };
    lowerer.lower_sub_ast(code)?;
    let mut out = lowerer.out;

    // And now postprocess
    encode_labels(&mut out, instr_format, 0, &ctx.defs)?;
    assign_registers(&mut out, instr_format, &ctx)?;

    out.into_iter().filter_map(|x| match x {
        LowerStmt::Instr(instr) => Some(encode_args(&instr, &ctx.defs)),
        LowerStmt::Label { .. } => None,
        LowerStmt::RegAlloc { .. } => None,
        LowerStmt::RegFree { .. } => None,
    }).collect_with_recovery()
}

// =============================================================================

/// Eliminates all `LowerArg::Label`s by replacing them with their dword values.
fn encode_labels(
    code: &mut [LowerStmt],
    format: &dyn InstrFormat,
    initial_offset: u64,
    defs: &Defs,
) -> Result<(), CompileError> {
    let label_info = gather_label_info(format, initial_offset, code, defs)?;

    code.iter_mut().map(|thing| {
        match thing {
            LowerStmt::Instr(LowerInstr { args: LowerArgs::Known(args), .. } ) => for arg in args {
                match arg.value {
                    | LowerArg::Label(ref label)
                    | LowerArg::TimeOf(ref label)
                    => match label_info.get(label) {
                        Some(info) => match arg.value {
                            LowerArg::Label(_) => arg.value = LowerArg::Raw((format.encode_label(info.offset) as i32).into()),
                            LowerArg::TimeOf(_) => arg.value = LowerArg::Raw(info.time.into()),
                            _ => unreachable!(),
                        },
                        None => return Err(error!{
                            message("undefined label '{}'", label),
                            primary(arg, "there is no label by this name"),
                        }),
                    },
                    _ => {},
                }
            },
            _ => {},
        }
        Ok(())
    }).collect_with_recovery()
}

struct RawLabelInfo {
    time: i32,
    offset: u64,
}
fn gather_label_info(
    format: &dyn InstrFormat,
    initial_offset: u64,
    code: &[LowerStmt],
    defs: &Defs,
) -> Result<HashMap<Sp<Ident>, RawLabelInfo>, CompileError> {
    use std::collections::hash_map::Entry;

    let mut offset = initial_offset;
    let mut out = HashMap::new();
    code.iter().map(|thing| {
        match *thing {
            LowerStmt::Instr(ref instr) => {
                offset += precompute_instr_size(instr, format, defs)? as u64;
            },
            LowerStmt::Label { time, ref label } => {
                match out.entry(label.clone()) {
                    Entry::Vacant(e) => {
                        e.insert(RawLabelInfo { time, offset });
                    },
                    Entry::Occupied(e) => {
                        return Err(error!{
                            message("duplicate label '{}'", label),
                            primary(label, "redefined here"),
                            secondary(e.key(), "originally defined here"),
                        });
                    },
                }
            },
            _ => {},
        }
        Ok(())
    }).collect_with_recovery()?;

    Ok(out)
}

// =============================================================================

// FIXME the existence of this still bothers me but I don't currently see a better solution
//
/// Determine what the final total size of the instruction will be based on the arguments and signature.
///
/// Typically we work with [`InstrRaw`] when we need to know the size of an instruction, but
/// fixing jump labels requires us to know the size before the args are fully encoded.
///
/// Unlike [`encode_args`], this has to deal with variants of [`LowerArg`] that are not the raw argument.
fn precompute_instr_size(instr: &LowerInstr, instr_format: &dyn InstrFormat, defs: &Defs) -> Result<usize, CompileError> {
    let arg_size = precompute_instr_args_size(instr, defs)?;

    Ok(instr_format.instr_header_size() + arg_size)
}

fn precompute_instr_args_size(instr: &LowerInstr, defs: &Defs) -> Result<usize, CompileError> {
    let args = match &instr.args {
        LowerArgs::Known(args) => args,
        LowerArgs::Unknown(blob) => {
            assert!(blob.len() % 4 == 0);  // should be checked already
            return Ok(blob.len());
        },
    };

    let abi = defs.ins_abi(instr.opcode).expect("(bug!) how did this typecheck with no signature?");

    let mut size = 0;
    for (arg, enc) in zip!(args, abi.arg_encodings()) {
        match arg.value {
            LowerArg::Raw(_) => match enc {
                | ArgEncoding::Dword
                | ArgEncoding::Color
                | ArgEncoding::Float
                | ArgEncoding::JumpOffset
                | ArgEncoding::JumpTime
                | ArgEncoding::Padding
                | ArgEncoding::Script
                | ArgEncoding::Sprite
                => size += 4,

                | ArgEncoding::Word
                => size += 2,

                | ArgEncoding::String { block_size, mask: _ }
                => {
                    // blech, we have to encode the string (which allocates) just to compute the correct length!
                    let string = arg.expect_raw().expect_string();
                    let encoded = Encoded::encode(&sp!(arg.span => string), DEFAULT_ENCODING)?;
                    let string_len = encoded.len();
                    size += crate::io::cstring_num_bytes(string_len, block_size);
                },
            },
            LowerArg::Local { .. } => size += 4,
            LowerArg::Label { .. } => size += 4,
            LowerArg::TimeOf { .. } => size += 4,
        }
    }

    for enc in abi.arg_encodings().skip(args.len()) {
        assert_eq!(enc, ArgEncoding::Padding);
        size += 4;
    }

    Ok(size)
}

fn encode_args(instr: &LowerInstr, defs: &Defs) -> Result<RawInstr, CompileError> {
    use crate::io::BinWrite;

    let args = match &instr.args {
        LowerArgs::Known(args) => args,
        LowerArgs::Unknown(blob) => {
            return Ok(RawInstr {
                time: instr.time,
                opcode: instr.opcode,
                param_mask: instr.user_param_mask.unwrap_or(0),
                args_blob: blob.value.clone(),
            });
        },
    };

    let abi = defs.ins_abi(instr.opcode).expect("(bug!) we already checked sigs for known args");

    let mut args_blob = std::io::Cursor::new(vec![]);
    for (arg, enc) in zip!(args, abi.arg_encodings()) {
        match enc {
            | ArgEncoding::Dword
            | ArgEncoding::Color
            | ArgEncoding::JumpOffset
            | ArgEncoding::JumpTime
            | ArgEncoding::Padding
            | ArgEncoding::Script
            | ArgEncoding::Sprite
            => args_blob.write_i32(arg.expect_raw().expect_int()).expect("Cursor<Vec> failed?!"),

            | ArgEncoding::Float
            => args_blob.write_f32(arg.expect_raw().expect_float()).expect("Cursor<Vec> failed?!"),

            | ArgEncoding::Word
            => args_blob.write_i16(arg.expect_raw().expect_int() as _).expect("Cursor<Vec> failed?!"),

            | ArgEncoding::String { block_size, mask }
            => {
                let string = arg.expect_raw().expect_string();
                let encoded = Encoded::encode(&sp!(arg.span => string), DEFAULT_ENCODING)?;
                args_blob.write_cstring_masked(&encoded, block_size, mask)?
            },
        }
    }

    for enc in abi.arg_encodings().skip(args.len()) {
        assert_eq!(enc, ArgEncoding::Padding);
        args_blob.write_u32(0).expect("Cursor<Vec> failed?!");
    }

    Ok(RawInstr {
        time: instr.time,
        opcode: instr.opcode,
        param_mask: match instr.user_param_mask {
            Some(user_provided_mask) => user_provided_mask,
            None => compute_param_mask(&args)?,
        },
        args_blob: args_blob.into_inner(),
    })
}

fn compute_param_mask(args: &[Sp<LowerArg>]) -> Result<u16, CompileError> {
    if args.len() > 16 {
        return Err(error!(
            message("too many arguments in instruction!"),
            primary(args[16], "too many arguments"),
        ));
    }
    let mut mask = 0;
    for arg in args.iter().rev(){
        let bit = match &arg.value {
            LowerArg::Raw(raw) => raw.is_reg as u16,
            LowerArg::TimeOf { .. } |
            LowerArg::Label { .. } => 0,
            LowerArg::Local { .. } => 1,
        };
        mask *= 2;
        mask += bit;
    }
    Ok(mask)
}

#[test]
fn test_precomputed_string_len() {
    use crate::value::ScalarValue;
    use encoding_rs::SHIFT_JIS;

    // the point of this test is to make sure the precomputed length of string arguments
    // uses the correct encoding instead of UTF-8.
    let str = "ｶﾀｶﾅｶﾀｶﾅｶﾀｶﾅｶﾀｶﾅ";
    let utf8_len = str.len();
    let sjis_len = SHIFT_JIS.encode(str).0.len();
    assert_ne!(utf8_len, sjis_len);

    let arg = LowerArg::Raw(SimpleArg { value: ScalarValue::String(str.into()), is_reg: false });
    let instr = LowerInstr { time: 0, opcode: 1, user_param_mask: None, args: LowerArgs::Known(vec![sp!(arg)]) };

    let scope = crate::Scope::new();
    let mut ctx = CompilerContext::new(&scope, crate::diagnostic::DiagnosticEmitter::new_stderr());

    ctx.set_ins_abi(1, "m".parse().unwrap());

    let actual = precompute_instr_args_size(&instr, &ctx.defs).unwrap();
    let expected = encode_args(&instr, &ctx.defs).unwrap().args_blob.len();
    assert_eq!(actual, expected);

    // the written length should be *slightly more* than sjis_len because there's the null terminator
    // and padding.  That's not too well-defined to check, though.
    //
    // However, we can be sure of the following, because the SJIS string is so much shorter than the
    // UTF8 encoding.
    assert!(actual < utf8_len);
}
