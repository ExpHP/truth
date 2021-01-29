use std::collections::{HashMap};

use super::unsupported;
use crate::llir::{RawInstr, Instr, InstrFormat, InstrArg};
use crate::error::{GatherErrorIteratorExt, CompileError};
use crate::pos::{Sp, Span};
use crate::ast;
use crate::ident::Ident;
use crate::var::{LocalId};
use crate::type_system::{TypeSystem, ArgEncoding};

mod stackless;

/// An intermediate representation that is only used during lowering.
///
/// In addition to instructions, it has a couple of extra things that are handled via
/// some post-processing steps.
#[derive(Debug, Clone, PartialEq)]
enum LowLevelStmt {
    /// Represents a single instruction in the compiled file.
    Instr(Instr),
    /// An intrinsic that represents a label that can be jumped to.
    Label { time: i32, label: Sp<Ident> },
    /// An intrinsic that begins the scope of a register-allocated local.
    RegAlloc { local_id: LocalId, cause: Span },
    /// An intrinsic that ends the scope of a register-allocated local.
    RegFree { local_id: LocalId },
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
        LowLevelStmt::Instr(instr) => Some(encode_args(&instr, ty_ctx)),
        LowLevelStmt::Label { .. } => None,
        LowLevelStmt::RegAlloc { .. } => None,
        LowLevelStmt::RegFree { .. } => None,
    }).collect_with_recovery()
}

// =============================================================================

/// Eliminates all `InstrArg::Label`s by replacing them with their dword values.
fn encode_labels(
    code: &mut [LowLevelStmt],
    format: &dyn InstrFormat,
    initial_offset: u64,
    ty_ctx: &TypeSystem,
) -> Result<(), CompileError> {
    let label_info = gather_label_info(format, initial_offset, code, ty_ctx)?;

    code.iter_mut().map(|thing| {
        match thing {
            LowLevelStmt::Instr(instr) => for arg in &mut instr.args {
                match *arg {
                    | InstrArg::Label(ref label)
                    | InstrArg::TimeOf(ref label)
                    => match label_info.get(label) {
                        Some(info) => match arg {
                            InstrArg::Label(_) => *arg = InstrArg::Raw(format.encode_label(info.offset).into()),
                            InstrArg::TimeOf(_) => *arg = InstrArg::Raw(info.time.into()),
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
    code: &[LowLevelStmt],
    ty_ctx: &TypeSystem,
) -> Result<HashMap<Sp<Ident>, RawLabelInfo>, CompileError> {
    use std::collections::hash_map::Entry;

    let mut offset = initial_offset;
    let mut out = HashMap::new();
    code.iter().map(|thing| {
        match *thing {
            LowLevelStmt::Instr(ref instr) => {
                offset += precompute_instr_size(instr, format, ty_ctx)? as u64;
            },
            LowLevelStmt::Label { time, ref label } => {
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
/// Unlike [`encode_args`], this has to deal with variants of [`InstrArg`] that are not the raw argument.
fn precompute_instr_size(instr: &Instr, instr_format: &dyn InstrFormat, ty_ctx: &TypeSystem) -> Result<usize, CompileError> {
    let siggy = {
        ty_ctx.regs_and_instrs.ins_signature(instr.opcode).ok_or_else(|| error!(
            message("signature for opcode {} not known", instr.opcode),  // FIXME: span
        ))?
    };

    let mut size = instr_format.instr_header_size();
    for (arg, enc) in zip!(&instr.args, siggy.arg_encodings()) {
        match arg {
            InstrArg::Raw(_) => match enc {
                | ArgEncoding::Dword
                | ArgEncoding::Color
                | ArgEncoding::Float
                | ArgEncoding::JumpOffset
                | ArgEncoding::JumpTime
                | ArgEncoding::Padding
                => size += 4,
            },
            InstrArg::Local { .. } => size += 4,
            InstrArg::Label { .. } => size += 4,
            InstrArg::TimeOf { .. } => size += 4,
        }
    }
    Ok(size)
}

fn encode_args(instr: &Instr, ty_ctx: &TypeSystem) -> Result<RawInstr, CompileError> {
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
            | ArgEncoding::Float
            | ArgEncoding::JumpOffset
            | ArgEncoding::JumpTime
            | ArgEncoding::Padding
                => args_blob.write_u32(arg.expect_raw().bits)?,
        }

    }
    Ok(RawInstr {
        time: instr.time,
        opcode: instr.opcode,
        param_mask: compute_param_mask(&instr.args)?,
        args_blob: args_blob.into_inner(),
    })
}

fn compute_param_mask(args: &[InstrArg]) -> Result<u16, CompileError> {
    if args.len() > 16 {
        // FIXME need span info
        return Err(anyhow::anyhow!("too many arguments in instruction!").into());
    }
    let mut mask = 0;
    for arg in args.iter().rev(){
        let bit = match *arg {
            InstrArg::Raw(raw) => raw.is_reg as u16,
            InstrArg::TimeOf { .. } |
            InstrArg::Label { .. } => 0,
            InstrArg::Local { .. } => 1,
        };
        mask *= 2;
        mask += bit;
    }
    Ok(mask)
}
