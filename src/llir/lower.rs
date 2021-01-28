use std::collections::{HashMap};

use super::unsupported;
use crate::llir::{Instr, InstrFormat, InstrArg};
use crate::error::{GatherErrorIteratorExt, CompileError};
use crate::pos::{Sp, Span};
use crate::ast;
use crate::ident::Ident;
use crate::var::{LocalId};
use crate::type_system::{TypeSystem};

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
) -> Result<Vec<Instr>, CompileError> {
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
    encode_labels(&mut out, instr_format, 0)?;
    assign_registers(&mut out, &used_regs, instr_format, ty_ctx)?;

    Ok(out.into_iter().filter_map(|x| match x {
        LowLevelStmt::Instr(instr) => Some(instr),
        LowLevelStmt::Label { .. } => None,
        LowLevelStmt::RegAlloc { .. } => None,
        LowLevelStmt::RegFree { .. } => None,
    }).collect())
}

// =============================================================================

/// Eliminates all `InstrArg::Label`s by replacing them with their dword values.
fn encode_labels(
    code: &mut [LowLevelStmt],
    format: &dyn InstrFormat,
    initial_offset: u64,
) -> Result<(), CompileError> {
    let label_info = gather_label_info(format, initial_offset, code)?;

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
    code: &[LowLevelStmt]
) -> Result<HashMap<Sp<Ident>, RawLabelInfo>, CompileError> {
    use std::collections::hash_map::Entry;

    let mut offset = initial_offset;
    let mut out = HashMap::new();
    code.iter().map(|thing| {
        match *thing {
            LowLevelStmt::Instr(ref instr) => {
                offset += format.instr_size(instr) as u64;
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
