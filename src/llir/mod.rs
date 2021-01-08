use std::collections::HashMap;

use anyhow::{bail, Context};
use enum_map::EnumMap;

use crate::ast;
use crate::binary_io::{BinRead, BinWrite, ReadResult, WriteResult};
use crate::error::{CompileError, SimpleError};
use crate::ident::Ident;
use crate::pos::{Sp, Span};
use crate::scope::VarId;
use crate::type_system::ScalarType;

pub use lower::lower_sub_ast_to_instrs;
mod lower;

pub use raise::raise_instrs_to_sub_ast;
mod raise;

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
    /// A register-allocated local.
    Local(VarId),
    /// A label that has not yet been converted to an integer argument.
    ///
    /// This may be present in the input to [`InstrFormat::instr_size`], but will be replaced with
    /// a dword before [`InstrFormat::write_instr`] is called.
    Label(Sp<Ident>),
    /// A `timeof(label)` that has not yet been converted to an integer argument.
    ///
    /// This may be present in the input to [`InstrFormat::instr_size`], but will be replaced with
    /// a dword before [`InstrFormat::write_instr`] is called.
    TimeOf(Sp<Ident>),
}
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct RawArg {
    pub bits: u32,
    pub is_var: bool,
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
                assert!(!x.is_var);
                x.bits as i32
            },
            _ => panic!("unexpected unresolved argument (bug!): {:?}", self),
        }
    }

    #[track_caller]
    pub fn expect_immediate_float(&self) -> f32 {
        match *self {
            InstrArg::Raw(x) => {
                assert!(!x.is_var);
                f32::from_bits(x.bits)
            },
            _ => panic!("unexpected unresolved argument (bug!): {:?}", self),
        }
    }
}

impl RawArg {
    pub fn from_reg(number: i32, ty: ScalarType) -> RawArg {
        let bits = match ty {
            ScalarType::Int => number as u32,
            ScalarType::Float => (number as f32).to_bits(),
        };
        RawArg { bits, is_var: true }
    }
}

impl From<u32> for RawArg {
    fn from(x: u32) -> RawArg { RawArg { bits: x, is_var: false } }
}

impl From<i32> for RawArg {
    fn from(x: i32) -> RawArg { RawArg { bits: x as u32, is_var: false } }
}

impl From<f32> for RawArg {
    fn from(x: f32) -> RawArg { RawArg { bits: x.to_bits(), is_var: false } }
}

fn unsupported(span: &crate::pos::Span) -> CompileError {
    error!(
        message("feature not supported by format"),
        primary(span, "not supported by format"),
    )
}

// =============================================================================

/// Reads the instructions of a complete script, attaching useful information on errors.
///
/// Though it primarily uses the `None` output of [`InstrFormat::read_instr`] to determine when to stop reading
/// instructions, it also may be given an end offset. This will cause it to stop with a warning if it lands on this
/// offset without receiving a `None` result, or to fail outright if it goes past this offset.  This enables the
/// reading of TH095's `front.anm`, which contains the only ANM script in existence to have no end marker.  *Sigh.*
pub fn read_instrs(
    f: &mut dyn BinRead,
    format: &dyn InstrFormat,
    starting_offset: usize,
    end_offset: Option<usize>,
) -> ReadResult<Vec<Instr>> {
    let mut script = vec![];
    let mut offset = starting_offset;
    for index in 0.. {
        if let Some(instr) = format.read_instr(f).with_context(|| format!("in instruction {} (offset {:#x})", index, offset))? {
            offset += format.instr_size(&instr);
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
pub fn write_instrs(
    f: &mut dyn BinWrite,
    format: &dyn InstrFormat,
    instrs: &[Instr],
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
    /// Like `a = sin(b);`
    ///
    /// Args: `a, b`.
    TransOp(TransOpKind),
    /// Like `if (x--) goto label @ t`.
    ///
    /// Args: `x, label, t`.
    CountJmp,
    /// Like `if (a == c) goto label @ t;`
    ///
    /// Args: `a, b, label, t`
    CondJmp(ast::BinopKind, ScalarType),
}

/// Transcendental functions available in at least one game.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TransOpKind { Sin, Cos, Tan, Acos, Atan }

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
    /// Get the number of bytes in the binary encoding of an instruction.
    fn instr_size(&self, instr: &Instr) -> usize;

    fn intrinsic_instrs(&self) -> IntrinsicInstrs {
        IntrinsicInstrs::from_pairs(self.intrinsic_opcode_pairs())
    }

    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, u16)>;

    /// Read a single script instruction from an input stream.
    ///
    /// Should return `None` when it reaches the marker that indicates the end of the script.
    /// When this occurs, it may leave the `Cursor` in an indeterminate state.
    fn read_instr(&self, f: &mut dyn BinRead) -> ReadResult<Option<Instr>>;

    /// Write a single script instruction into an output stream.
    fn write_instr(&self, f: &mut dyn BinWrite, instr: &Instr) -> WriteResult;

    /// Write a marker that goes after the final instruction in a function or script.
    fn write_terminal_instr(&self, f: &mut dyn BinWrite) -> WriteResult;

    // ---------------------------------------------------
    // Special purpose functions only overridden by a few formats

    /// List of registers available for scratch use in formats without a stack.
    fn general_use_regs(&self) -> EnumMap<ScalarType, Vec<i32>> {
        enum_map::enum_map!(_ => vec![])
    }

    /// Indicates that [`IntrinsicInstrKind::Jmp`] takes two arguments, where the second is time.
    ///
    /// TH06 ANM has no time arg. (it always sets the script clock to the destination's time)
    fn jump_has_time_arg(&self) -> bool { true }

    /// Used by TH06 to indicate that an instruction must be the last instruction in the script.
    fn is_th06_anm_terminating_instr(&self, _opcode: u16) -> bool { false }

    // Most formats encode labels as offsets from the beginning of the script (in which case
    // these functions are trivial), but early STD is a special snowflake that writes the
    // instruction *index* instead.
    fn encode_label(&self, offset: usize) -> u32 { offset as _ }
    fn decode_label(&self, bits: u32) -> usize { bits as _ }
}

/// Helper to help implement `InstrFormat::read_instr`.
///
/// Reads `size` bytes into `size/4` dword arguments and sets their `is_var` flags according to
/// the parameter mask.  (it takes `size` instead of a count to help factor out divisibility checks,
/// as a size is often what you have to work with given the format)
pub fn read_dword_args_upto_size(
    f: &mut dyn BinRead,
    size: usize,
    mut param_mask: u16,
) -> ReadResult<Vec<InstrArg>> {
    if size % 4 != 0 {
        bail!("size not divisible by 4: {}", size);
    }
    let nargs = size/4;

    let out = (0..nargs).map(|_| {
        let bits = f.read_u32()?;
        let is_var = param_mask % 2 == 1;
        param_mask /= 2;
        Ok(InstrArg::Raw(RawArg { bits, is_var }))
    }).collect::<ReadResult<_>>()?;

    if param_mask != 0 {
        fast_warning!(
            "unused bits in param_mask! (arg {} is a variable, but there are only {} args!)",
            param_mask.trailing_zeros() + nargs as u32 + 1, nargs,
        );
    }
    Ok(out)
}

impl Instr {
    pub fn compute_param_mask(&self) -> Result<u16, SimpleError> {
        if self.args.len() > 16 {
            bail!("too many arguments in instruction!");
        }
        let mut mask = 0;
        for arg in self.args.iter().rev(){
            let bit = match *arg {
                InstrArg::Raw(RawArg { is_var, .. }) => is_var as u16,
                InstrArg::TimeOf(_) |
                InstrArg::Label(_) => 0,
                InstrArg::Local(_) => 1,
            };
            mask *= 2;
            mask += bit;
        }
        Ok(mask)
    }
}
