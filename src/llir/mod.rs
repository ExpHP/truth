use std::collections::HashMap;

use anyhow::{bail, Context};
use enum_map::EnumMap;

use crate::ast;
use crate::binary_io::{BinRead, BinWrite, ReadResult, WriteResult};
use crate::error::{CompileError};
use crate::ident::Ident;
use crate::pos::{Sp, Span};
use crate::var::{LocalId, RegId};
use crate::type_system::ScalarType;

pub use lower::lower_sub_ast_to_instrs;
mod lower;

pub use raise::raise_instrs_to_sub_ast;
mod raise;

#[derive(Debug, Clone, PartialEq)]
pub struct RawInstr {
    pub time: i32,
    pub opcode: u16,
    pub param_mask: u16,
    pub args_blob: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Instr {
    pub time: i32,
    pub opcode: u16,
    pub args: Vec<InstrArg>,
}
#[derive(Debug, Clone, PartialEq)]
pub enum InstrArg {
    /// A fully encoded argument (an immediate or a register).
    Raw(RawArg),
    /// A reference to a register-allocated local.
    ///
    /// This may be present in the input to [`InstrFormat::instr_size`], but will be replaced with
    /// a raw dword before [`InstrFormat::write_instr`] is called.
    Local { local_id: LocalId, read_ty: ScalarType },
    /// A label that has not yet been converted to an integer argument.
    ///
    /// This may be present in the input to [`InstrFormat::instr_size`], but will be replaced with
    /// a raw dword before [`InstrFormat::write_instr`] is called.
    Label(Sp<Ident>),
    /// A `timeof(label)` that has not yet been converted to an integer argument.
    ///
    /// This may be present in the input to [`InstrFormat::instr_size`], but will be replaced with
    /// a raw dword before [`InstrFormat::write_instr`] is called.
    TimeOf(Sp<Ident>),
}

/// An untyped dword argument, exactly as it will (or did) appear in the binary file.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct RawArg {
    /// The encoded value.  It contains the bits of either an `i32` or an `f32`.
    pub bits: u32,
    /// A single bit from the param mask.
    pub is_reg: bool,
}

impl InstrArg {
    /// Call this at a time when the arg is known to have a fully resolved value.
    ///
    /// Such times are:
    /// * During decompilation.
    /// * Within [`InstrFormat::write_instr`].
    #[track_caller]
    pub fn expect_raw(&self) -> RawArg {
        match *self {
            InstrArg::Raw(x) => x,
            _ => panic!("unexpected unresolved argument (bug!): {:?}", self),
        }
    }

    #[track_caller]
    pub fn expect_immediate_int(&self) -> i32 {
        match *self {
            InstrArg::Raw(x) => {
                assert!(!x.is_reg);
                x.bits as i32
            },
            _ => panic!("unexpected unresolved argument (bug!): {:?}", self),
        }
    }

    #[track_caller]
    pub fn expect_immediate_float(&self) -> f32 {
        match *self {
            InstrArg::Raw(x) => {
                assert!(!x.is_reg);
                f32::from_bits(x.bits)
            },
            _ => panic!("unexpected unresolved argument (bug!): {:?}", self),
        }
    }
}

impl RawArg {
    pub fn from_reg(reg: RegId, ty: ScalarType) -> RawArg {
        let bits = match ty {
            ScalarType::Int => reg.0 as u32,
            ScalarType::Float => (reg.0 as f32).to_bits(),
        };
        RawArg { bits, is_reg: true }
    }
}

impl From<u32> for RawArg {
    fn from(x: u32) -> RawArg { RawArg { bits: x, is_reg: false } }
}

impl From<i32> for RawArg {
    fn from(x: i32) -> RawArg { RawArg { bits: x as u32, is_reg: false } }
}

impl From<f32> for RawArg {
    fn from(x: f32) -> RawArg { RawArg { bits: x.to_bits(), is_reg: false } }
}

fn unsupported(span: &crate::pos::Span, what: &str) -> CompileError {
    error!(
        message("feature not supported by format"),
        primary(span, "{} not supported by format", what),
    )
}

// =============================================================================

/// Reads the instructions of a complete script, attaching useful information on errors.
///
/// Though it primarily uses the `None` output of [`InstrFormat::read_instr`] to determine when to stop reading
/// instructions, it also may be given an end offset. This will cause it to stop with a warning if it lands on this
/// offset without receiving a `None` result, or to fail outright if it goes past this offset.  This enables the
/// reading of TH095's `front.anm`, which contains the only ANM scripts in existence to have no end marker.  *Sigh.*
#[inline(never)]
pub fn read_instrs(
    f: &mut dyn BinRead,
    format: &dyn InstrFormat,
    starting_offset: u64,
    end_offset: Option<u64>,
) -> ReadResult<Vec<RawInstr>> {
    let mut script = vec![];
    let mut offset = starting_offset;
    for index in 0.. {
        if let Some(instr) = format.read_instr(f).with_context(|| format!("in instruction {} (offset {:#x})", index, offset))? {
            offset += format.instr_size(&instr) as u64;
            script.push(instr);

            if let Some(end_offset) = end_offset {
                match offset.cmp(&end_offset) {
                    std::cmp::Ordering::Less => {},
                    std::cmp::Ordering::Equal => {
                        fast_warning!("original file is missing an end-of-script marker; one will be added on recompilation");
                        break;
                    },
                    std::cmp::Ordering::Greater => {
                        bail!("script read past expected end at offset {:#x} (we're now at offset {:#x}!)", end_offset, offset);
                    },
                }
            }
        } else {
            break;  // no more instructions
        }
    }
    Ok(script)
}

/// Writes the instructions of a complete script, attaching useful information on errors.
#[inline(never)]
pub fn write_instrs(
    f: &mut dyn BinWrite,
    format: &dyn InstrFormat,
    instrs: &[RawInstr],
) -> WriteResult {
    for (index, instr) in instrs.iter().enumerate() {
        format.write_instr(f, instr).with_context(|| format!("while writing instruction {}", index))?;
    }
    format.write_terminal_instr(f).with_context(|| format!("while writing the script end marker"))?;
    Ok(())
}

// =============================================================================

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntrinsicInstrKind {
    /// Like `goto label @ t;` (and `goto label;`)
    ///
    /// Args: `label, t`.
    Jmp,
    /// Like `interrupt[n]:`
    ///
    /// Args: `n`.
    InterruptLabel,
    /// Like `a = b;` or `a += b;`
    ///
    /// Args: `a, b`.
    AssignOp(ast::AssignOpKind, ScalarType),
    /// Like `a = b + c;`
    ///
    /// Args: `a, b, c`.
    Binop(ast::BinopKind, ScalarType),
    /// Like `a = sin(b);` (or `a = -a;`, but it seems no formats actually have this?)
    ///
    /// This is not used for casts like `a = _S(b);`.  Casts have no explicit representation in
    /// a compiled script; they're just a fundamental part of how the engine reads variables.
    ///
    /// Args: `a, b`.
    Unop(ast::UnopKind, ScalarType),
    /// Like `if (--x) goto label @ t`.
    ///
    /// Args: `x, label, t`.
    CountJmp,
    /// Like `if (a == c) goto label @ t;`
    ///
    /// Args: `a, b, label, t`
    CondJmp(ast::BinopKind, ScalarType),
}

pub struct IntrinsicInstrs {
    intrinsic_opcodes: HashMap<IntrinsicInstrKind, u16>,
    opcode_intrinsics: HashMap<u16, IntrinsicInstrKind>,
}
impl IntrinsicInstrs {
    pub fn from_pairs(pairs: impl IntoIterator<Item=(IntrinsicInstrKind, u16)>) -> Self {
        let intrinsic_opcodes: HashMap<_, _> = pairs.into_iter().collect();
        let opcode_intrinsics = intrinsic_opcodes.iter().map(|(&k, &v)| (v, k)).collect();
        IntrinsicInstrs { opcode_intrinsics, intrinsic_opcodes }
    }

    pub fn get_opcode(&self, intrinsic: IntrinsicInstrKind, span: Span, descr: &str) -> Result<u16, CompileError> {
        match self.intrinsic_opcodes.get(&intrinsic) {
            Some(&opcode) => Ok(opcode),
            None => Err(error!(
                message("feature not supported by format"),
                primary(span, "{} not supported in this game", descr),
            )),
        }
    }

    pub fn get_intrinsic(&self, opcode: u16) -> Option<IntrinsicInstrKind> {
        self.opcode_intrinsics.get(&opcode).copied()
    }
}

/// Add intrinsic pairs for binary operations in `a = b op c` form in their canonical order,
/// which is `+, -, *, /, %`, with each operator having an int version and a float version.
pub fn register_binary_ops(pairs: &mut Vec<(IntrinsicInstrKind, u16)>, start: u16) {
    use ast::BinopKind as B;

    let mut opcode = start;
    for op in vec![B::Add, B::Sub, B::Mul, B::Div, B::Rem] {
        for ty in vec![ScalarType::Int, ScalarType::Float] {
            pairs.push((IntrinsicInstrKind::Binop(op, ty), opcode));
            opcode += 1;
        }
    }
}

/// Add intrinsic pairs for assign ops in their cannonical order: `=, +=, -=, *=, /=, %=`,
/// with each operator having an int version and a float version.
pub fn register_assign_ops(pairs: &mut Vec<(IntrinsicInstrKind, u16)>, start: u16) {
    use ast::AssignOpKind as As;

    let mut opcode = start;
    for op in vec![As::Assign, As::Add, As::Sub, As::Mul, As::Div, As::Rem] {
        for ty in vec![ScalarType::Int, ScalarType::Float] {
            pairs.push((IntrinsicInstrKind::AssignOp(op, ty), opcode));
            opcode += 1;
        }
    }
}

/// Add intrinsic pairs for conditional jumps in their cannonical order: `==, !=, <, <=, >, >=`,
/// with each operator having an int version and a float version.
pub fn register_cond_jumps(pairs: &mut Vec<(IntrinsicInstrKind, u16)>, start: u16) {
    use ast::BinopKind as B;

    let mut opcode = start;
    for op in vec![B::Eq, B::Ne, B::Lt, B::Le, B::Gt, B::Ge] {
        for ty in vec![ScalarType::Int, ScalarType::Float] {
            pairs.push((IntrinsicInstrKind::CondJmp(op, ty), opcode));
            opcode += 1;
        }
    }
}

pub trait InstrFormat {
    fn intrinsic_instrs(&self) -> IntrinsicInstrs {
        IntrinsicInstrs::from_pairs(self.intrinsic_opcode_pairs())
    }

    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, u16)>;

    /// Get the number of bytes in the binary encoding of an instruction.
    fn instr_header_size(&self) -> usize;

    /// Read a single script instruction from an input stream.
    ///
    /// Should return `None` when it reaches the marker that indicates the end of the script.
    /// When this occurs, it may leave the `Cursor` in an indeterminate state.
    fn read_instr(&self, f: &mut dyn BinRead) -> ReadResult<Option<RawInstr>>;

    /// Write a single script instruction into an output stream.
    fn write_instr(&self, f: &mut dyn BinWrite, instr: &RawInstr) -> WriteResult;

    /// Write a marker that goes after the final instruction in a function or script.
    fn write_terminal_instr(&self, f: &mut dyn BinWrite) -> WriteResult;

    // ---------------------------------------------------
    // Special purpose functions only overridden by a few formats

    /// List of registers available for scratch use in formats without a stack.
    fn general_use_regs(&self) -> EnumMap<ScalarType, Vec<RegId>> {
        enum_map::enum_map!(_ => vec![])
    }

    /// Should return `true` if this instruction implicitly uses registers not mentioned in the
    /// argument list.  This will disable scratch register allocation.
    ///
    /// This is used for ANM ins_509 which copies all variables from the parent.  (basically,
    /// a script in the middle of a `grandparent->parent->child` ancestry could be using it to
    /// communicate registers it doesn't even mention, if both `parent` and `child` are using it!)
    fn instr_disables_scratch_regs(&self, _opcode: u16) -> bool { false }

    /// Indicates that [`IntrinsicInstrKind::Jmp`] takes two arguments, where the second is time.
    ///
    /// TH06 ANM has no time arg. (it always sets the script clock to the destination's time)
    fn jump_has_time_arg(&self) -> bool { true }

    /// Used by TH06 to indicate that an instruction must be the last instruction in the script.
    fn is_th06_anm_terminating_instr(&self, _opcode: u16) -> bool { false }

    // Most formats encode labels as offsets from the beginning of the script (in which case
    // these functions are trivial), but early STD is a special snowflake that writes the
    // instruction *index* instead.
    fn encode_label(&self, offset: u64) -> u32 { offset as _ }
    fn decode_label(&self, bits: u32) -> u64 { bits as _ }

    // FIXME: remove this
    fn instr_size(&self, instr: &RawInstr) -> usize { self.instr_header_size() + instr.args_blob.len() }
}

/// An implementation of InstrFormat for testing the raising and lowering phases of compilation.
#[derive(Debug, Clone, Default)]
pub struct TestFormat {
    pub intrinsic_opcode_pairs: Vec<(IntrinsicInstrKind, u16)>,
    pub general_use_int_regs: Vec<RegId>,
    pub general_use_float_regs: Vec<RegId>,
    /// For simulating the existence of an instruction like ANM ins_509
    pub anti_scratch_opcode: Option<u16>,
}
impl InstrFormat for TestFormat {
    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, u16)> {
        self.intrinsic_opcode_pairs.clone()
    }

    fn instr_header_size(&self) -> usize { 4 }
    fn read_instr(&self, _: &mut dyn BinRead) -> ReadResult<Option<RawInstr>> { panic!("TestInstrFormat does not implement reading or writing") }
    fn write_instr(&self, _: &mut dyn BinWrite, _: &RawInstr) -> WriteResult { panic!("TestInstrFormat does not implement reading or writing") }
    fn write_terminal_instr(&self, _: &mut dyn BinWrite) -> WriteResult { panic!("TestInstrFormat does not implement reading or writing")  }

    fn instr_disables_scratch_regs(&self, opcode: u16) -> bool {
        self.anti_scratch_opcode == Some(opcode)
    }

    fn general_use_regs(&self) -> EnumMap<ScalarType, Vec<RegId>> {
        enum_map::enum_map!{
            ScalarType::Int => self.general_use_int_regs.clone(),
            ScalarType::Float => self.general_use_float_regs.clone(),
        }
    }
}
