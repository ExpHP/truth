use std::collections::HashMap;

use enum_map::EnumMap;

use crate::ast;
use crate::io::{BinReader, BinWriter, ReadResult, WriteResult, ErrLocation};
use crate::error::CompileError;
use crate::pos::{Span};
use crate::value::{ScalarValue, ScalarType};
use crate::resolve::{RegId};

pub use abi::{InstrAbi, ArgEncoding};
mod abi;

pub use lower::lower_sub_ast_to_instrs;
mod lower;

pub use raise::Raiser;
mod raise;

/// The lowest level representation of an instruction that is common between all games.
///
/// This is the type used to represent instructions in types like [`crate::formats::anm::AnmFile`].
///
/// The arguments to the instruction are fully encoded in a blob of bytes, exactly as they would
/// appear in the binary file.  The reason for this is so that the functions that perform binary
/// reading and writing of these files do not require access to type system information like
/// instruction signatures.
///
/// * Compile the AST into these using [`lower_sub_ast_to_instrs`].
/// * Decompile these into AST statements using [`raise_instrs_to_sub_ast`].
/// * Read from a binary file using [`read_instrs`].
/// * Write to a binary file using [`write_instrs`].
#[derive(Debug, Clone, PartialEq)]
pub struct RawInstr {
    pub time: i32,
    pub opcode: u16,
    pub param_mask: u16,
    pub args_blob: Vec<u8>,
}

/// A simple argument, which is either an immediate or a register reference.
#[derive(Debug, Clone, PartialEq)]
pub struct SimpleArg {
    /// Immediate value or register ID.
    pub value: ScalarValue,
    /// The bit from the param mask that lets us tell whether it's a register ID.
    pub is_reg: bool,
}

impl SimpleArg {
    #[track_caller]
    pub fn expect_immediate_int(&self) -> i32 {
        assert!(!self.is_reg);
        self.expect_int()
    }

    #[track_caller]
    pub fn expect_int(&self) -> i32 {
        match self.value {
            ScalarValue::Int(x) => x,
            _ => panic!("{:?}", self),
        }
    }

    #[track_caller]
    pub fn expect_float(&self) -> f32 {
        match self.value {
            ScalarValue::Float(x) => x,
            _ => panic!("{:?}", self),
        }
    }

    #[track_caller]
    pub fn expect_string(&self) -> &String {
        match self.value {
            ScalarValue::String(ref x) => x,
            _ => panic!("{:?}", self),
        }
    }
}

impl SimpleArg {
    pub fn from_reg(reg: RegId, ty: ScalarType) -> SimpleArg {
        let value = match ty {
            ScalarType::Int => ScalarValue::Int(reg.0),
            ScalarType::Float => ScalarValue::Float(reg.0 as f32),
            _ => panic!("tried to compile register argument from {}", ty.descr())
        };
        SimpleArg { value, is_reg: true }
    }

    /// Recover the register id.  `None` for immediates.
    pub fn get_reg_id(&self) -> Option<RegId> {
        if !self.is_reg { return None; }
        match self.value {
            ScalarValue::Int(x) => Some(RegId(x)),
            ScalarValue::Float(x) => {
                assert!(x == x.round(), "{}", x);
                Some(RegId(x as i32))
            },
            _ => panic!("{:?}", self)
        }
    }
}

impl From<i32> for SimpleArg {
    fn from(x: i32) -> SimpleArg { SimpleArg { value: ScalarValue::Int(x), is_reg: false } }
}

impl From<f32> for SimpleArg {
    fn from(x: f32) -> SimpleArg { SimpleArg { value: ScalarValue::Float(x), is_reg: false } }
}

impl From<String> for SimpleArg {
    fn from(x: String) -> SimpleArg { SimpleArg { value: ScalarValue::String(x), is_reg: false } }
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
    f: &mut BinReader,
    format: &dyn InstrFormat,
    starting_offset: u64,
    end_offset: Option<u64>,
) -> ReadResult<Vec<RawInstr>> {
    let mut script = vec![];
    let mut offset = starting_offset;
    for index in 0.. {
        let instr = f.push_location(ErrLocation::InNumbered { what: "instruction", number: index }, |f| {
            format.read_instr(f)
        })?;
        if let Some(instr) = instr {
            offset += format.instr_size(&instr) as u64;
            script.push(instr);

            if let Some(end_offset) = end_offset {
                match offset.cmp(&end_offset) {
                    std::cmp::Ordering::Less => {},
                    std::cmp::Ordering::Equal => {
                        f.warning("missing end-of-script marker will be added on recompilation");
                        break;
                    },
                    std::cmp::Ordering::Greater => {
                        return Err(f.error(format_args!("script read past expected end at offset {:#x} (we're now at offset {:#x}!)", end_offset, offset)));
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
    f: &mut BinWriter,
    format: &dyn InstrFormat,
    instrs: &[RawInstr],
) -> WriteResult {
    for (index, instr) in instrs.iter().enumerate() {
        f.push_location(ErrLocation::InNumbered { what: "instruction", number: index }, |f| {
            format.write_instr(f, instr)
        })?;
    }
    f.push_location(ErrLocation::In { what: "end marker" }, |f| {
        format.write_terminal_instr(f)
    })
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

    /// Get the number of bytes in the binary encoding of an instruction's header (before the arguments).
    fn instr_header_size(&self) -> usize;

    /// Read a single script instruction from an input stream.
    ///
    /// Should return `None` when it reaches the marker that indicates the end of the script.
    /// When this occurs, it may leave the `Cursor` in an indeterminate state.
    fn read_instr(&self, f: &mut BinReader) -> ReadResult<Option<RawInstr>>;

    /// Write a single script instruction into an output stream.
    fn write_instr(&self, f: &mut BinWriter, instr: &RawInstr) -> WriteResult;

    /// Write a marker that goes after the final instruction in a function or script.
    fn write_terminal_instr(&self, f: &mut BinWriter) -> WriteResult;

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

    /// Helper method that returns the total instruction size, including the arguments.
    /// There should be no need to override this.
    fn instr_size(&self, instr: &RawInstr) -> usize { self.instr_header_size() + instr.args_blob.len() }
}

/// An implementation of InstrFormat for testing the raising and lowering phases of compilation.
#[derive(Debug, Clone, Default)]
pub struct TestFormat {
    pub intrinsic_opcode_pairs: Vec<(IntrinsicInstrKind, u16)>,
    pub general_use_int_regs: Vec<RegId>,
    pub general_use_float_regs: Vec<RegId>,
    /// For simulating the existence of an instruction like ANM `ins_509`
    pub anti_scratch_opcode: Option<u16>,
}
impl InstrFormat for TestFormat {
    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, u16)> {
        self.intrinsic_opcode_pairs.clone()
    }

    fn instr_header_size(&self) -> usize { 4 }
    fn read_instr(&self, _: &mut BinReader) -> ReadResult<Option<RawInstr>> { panic!("TestInstrFormat does not implement reading or writing") }
    fn write_instr(&self, _: &mut BinWriter, _: &RawInstr) -> WriteResult { panic!("TestInstrFormat does not implement reading or writing") }
    fn write_terminal_instr(&self, _: &mut BinWriter) -> WriteResult { panic!("TestInstrFormat does not implement reading or writing")  }

    fn instr_disables_scratch_regs(&self, opcode: u16) -> bool {
        self.anti_scratch_opcode == Some(opcode)
    }

    fn general_use_regs(&self) -> EnumMap<ScalarType, Vec<RegId>> {
        enum_map::enum_map!{
            ScalarType::Int => self.general_use_int_regs.clone(),
            ScalarType::Float => self.general_use_float_regs.clone(),
            ScalarType::String => vec![],
        }
    }
}
