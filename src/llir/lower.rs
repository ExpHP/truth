use std::collections::{HashMap};

use super::{unsupported, SimpleArg};
use crate::llir::{RawInstr, InstrFormat};
use crate::error::{GatherErrorIteratorExt, CompileError};
use crate::pos::{Sp, Span};
use crate::ast;
use crate::ident::Ident;
use crate::var::{LocalId};
use crate::type_system::{TypeSystem, ArgEncoding, ScalarType};

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
    RegAlloc { local_id: LocalId, cause: Span },
    /// An intrinsic that ends the scope of a register-allocated local.
    RegFree { local_id: LocalId },
}

/// An instruction that needs just a bit more postprocessing to convert it into a [`RawInstr`].
#[derive(Debug, Clone, PartialEq)]
pub struct LowerInstr {
    pub time: i32,
    pub opcode: u16,
    pub args: Vec<LowerArg>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LowerArg {
    /// A fully encoded argument (an immediate or a register).
    ///
    /// All arguments are eventually lowered to this form.
    Raw(SimpleArg),
    /// A reference to a register-allocated local.
    Local { local_id: LocalId, read_ty: ScalarType },
    /// A label that has not yet been converted to an integer argument.
    Label(Sp<Ident>),
    /// A `timeof(label)` that has not yet been converted to an integer argument.
    TimeOf(Sp<Ident>),
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
    ty_ctx: &mut TypeSystem,
) -> Result<Vec<RawInstr>, CompileError> {
    use stackless::{get_used_regs, Lowerer, assign_registers};

    let used_regs = get_used_regs(code);

    let mut lowerer = Lowerer {
        out: vec![],
        intrinsic_instrs: instr_format.intrinsic_instrs(),
        ty_ctx,
        instr_format,
    };
    lowerer.lower_sub_ast(code)?;
    let mut out = lowerer.out;

    // And now postprocess
    encode_labels(&mut out, instr_format, 0, ty_ctx)?;
    assign_registers(&mut out, &used_regs, instr_format, ty_ctx)?;

    out.into_iter().filter_map(|x| match x {
        LowerStmt::Instr(instr) => Some(encode_args(&instr, ty_ctx)),
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
    ty_ctx: &TypeSystem,
) -> Result<(), CompileError> {
    let label_info = gather_label_info(format, initial_offset, code, ty_ctx)?;

    code.iter_mut().map(|thing| {
        match thing {
            LowerStmt::Instr(instr) => for arg in &mut instr.args {
                match *arg {
                    | LowerArg::Label(ref label)
                    | LowerArg::TimeOf(ref label)
                    => match label_info.get(label) {
                        Some(info) => match arg {
                            LowerArg::Label(_) => *arg = LowerArg::Raw((format.encode_label(info.offset) as i32).into()),
                            LowerArg::TimeOf(_) => *arg = LowerArg::Raw(info.time.into()),
                            _ => unreachable!(),
                        },
                        None => return Err(error!{
                            message("undefined label '{}'", label),
                            primary(label, "there is no label by this name"),
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
    ty_ctx: &TypeSystem,
) -> Result<HashMap<Sp<Ident>, RawLabelInfo>, CompileError> {
    use std::collections::hash_map::Entry;

    let mut offset = initial_offset;
    let mut out = HashMap::new();
    code.iter().map(|thing| {
        match *thing {
            LowerStmt::Instr(ref instr) => {
                offset += precompute_instr_size(instr, format, ty_ctx)? as u64;
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
        Ok::<_, CompileError>(())
    }).collect_with_recovery()?;

    Ok(out)
}

// =============================================================================

// FIXME the existence of this still bothers me but I don't currently see a better solution
//
/// Determine what the final total size of the instruction will be based on the arguments and signature.
///
/// Typically we work with InstrRaw when we need to know the size of an instruction, but
/// fixing jump labels requires us to know the size before the args are fully encoded.
///
/// Unlike [`encode_args`], this has to deal with variants of [`LowerArg`] that are not the raw argument.
fn precompute_instr_size(instr: &LowerInstr, instr_format: &dyn InstrFormat, ty_ctx: &TypeSystem) -> Result<usize, CompileError> {
    let siggy = {
        ty_ctx.regs_and_instrs.ins_signature(instr.opcode).ok_or_else(|| error!(
            message("signature for opcode {} not known", instr.opcode),  // FIXME: span
        ))?
    };

    let mut size = instr_format.instr_header_size();
    for (arg, enc) in zip!(&instr.args, siggy.arg_encodings()) {
        match arg {
            LowerArg::Raw(_) => match enc {
                | ArgEncoding::Dword
                | ArgEncoding::Color
                | ArgEncoding::Float
                | ArgEncoding::JumpOffset
                | ArgEncoding::JumpTime
                | ArgEncoding::Padding
                => size += 4,

                | ArgEncoding::Word
                => size += 2,
            },
            LowerArg::Local { .. } => size += 4,
            LowerArg::Label { .. } => size += 4,
            LowerArg::TimeOf { .. } => size += 4,
        }
    }

    for enc in siggy.arg_encodings().skip(instr.args.len()) {
        assert_eq!(enc, ArgEncoding::Padding);
        size += 4;
    }

    Ok(size)
}

fn encode_args(instr: &LowerInstr, ty_ctx: &TypeSystem) -> Result<RawInstr, CompileError> {
    use crate::binary_io::BinWrite;

    let siggy = {
        ty_ctx.regs_and_instrs.ins_signature(instr.opcode)
            .expect("(bug!) wasn't this checked to exist earlier?")
    };

    let mut args_blob = std::io::Cursor::new(vec![]);
    for (arg, enc) in zip!(&instr.args, siggy.arg_encodings()) {
        match enc {
            | ArgEncoding::Dword
            | ArgEncoding::Color
            | ArgEncoding::JumpOffset
            | ArgEncoding::JumpTime
            | ArgEncoding::Padding
            => args_blob.write_i32(arg.expect_raw().expect_int())?,

            | ArgEncoding::Float
            => args_blob.write_f32(arg.expect_raw().expect_float())?,

            | ArgEncoding::Word
            => args_blob.write_i16(arg.expect_raw().expect_int() as _)?,
        }
    }

    for enc in siggy.arg_encodings().skip(instr.args.len()) {
        assert_eq!(enc, ArgEncoding::Padding);
        args_blob.write_u32(0)?;
    }

    Ok(RawInstr {
        time: instr.time,
        opcode: instr.opcode,
        param_mask: compute_param_mask(&instr.args)?,
        args_blob: args_blob.into_inner(),
    })
}

fn compute_param_mask(args: &[LowerArg]) -> Result<u16, CompileError> {
    if args.len() > 16 {
        // FIXME need span info
        return Err(error!("too many arguments in instruction!"));
    }
    let mut mask = 0;
    for arg in args.iter().rev(){
        let bit = match arg {
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
