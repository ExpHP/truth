use std::collections::HashMap;

use enum_map::EnumMap;

use crate::ast;
use crate::io::{BinReader, BinWriter, ReadResult, WriteResult};
use crate::diagnostic::{Diagnostic, Emitter};
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

fn unsupported(span: &crate::pos::Span, what: &str) -> Diagnostic {
    error!(
        message("feature not supported by format"),
        primary(span, "{} not supported by format", what),
    )
}

// =============================================================================

/// Reads the instructions of a complete script, attaching useful information on errors.
///
/// The tricky part here is determining the end of the script.  All scripting languages
/// have a dummy "terminal instruction" that is inserted after the end of each script,
/// but sometimes this instruction is indistinguishable from legitimate code.
/// In this case, the function must be given an "end offset" or may be read to EoF.
///
/// (there's also the evil case of TH095's `front.anm`, which contains the only ANM scripts
/// in existence to have no terminal instruction.)
///
/// More details can be found in the documentation of [`ReadInstr`].
#[inline(never)]
pub fn read_instrs(
    r: &mut BinReader,
    emitter: &impl Emitter,
    format: &dyn InstrFormat,
    starting_offset: u64,
    end_offset: Option<u64>,
) -> ReadResult<Vec<RawInstr>> {
    let mut possible_terminal = None;
    let mut cur_offset = starting_offset;
    let mut instrs = vec![];

    // this has to be checked in two places (because detecting EoF requires us to make a read attempt,
    // but we don't want to read if we're at end_offset)
    let warn_missing_end_of_script = || {
        emitter.emit(warning!("missing end-of-script marker will be added on recompilation")).ignore()
    };

    for index in 0.. {
        if let Some(end_offset) = end_offset {
            match cur_offset.cmp(&end_offset) {
                std::cmp::Ordering::Less => {},
                std::cmp::Ordering::Equal => {
                    if possible_terminal.is_none() {
                        warn_missing_end_of_script();
                    }
                    break;
                },
                std::cmp::Ordering::Greater => {
                    return Err(emitter.emit(error!(
                        "script read past expected end at offset {:#x} (we're now at offset {:#x}!)",
                        end_offset, cur_offset,
                    )));
                },
            }
        }

        let instr_kind = emitter.chain_with(|f| write!(f, "in instruction {}", index), |emitter| {
            format.read_instr(r, emitter)
        })?;

        let is_maybe_terminal = matches!(instr_kind, ReadInstr::MaybeTerminal(_));
        match instr_kind {
            ReadInstr::EndOfFile => {
                if possible_terminal.is_none() {
                    warn_missing_end_of_script();
                }
                break;
            },

            ReadInstr::MaybeTerminal(instr) |
            ReadInstr::Instr(instr) => {
                if let Some(prev_instr) = possible_terminal.take() {
                    // since we read another instr, this previous one wasn't the terminal
                    instrs.push(prev_instr);
                }
                cur_offset += format.instr_size(&instr) as u64;

                if is_maybe_terminal {
                    possible_terminal = Some(instr);
                } else {
                    instrs.push(instr);
                }
            },

            ReadInstr::Terminal => break,
        }
    }
    Ok(instrs)
}

/// Writes the instructions of a complete script, attaching useful information on errors.
#[inline(never)]
pub fn write_instrs(
    f: &mut BinWriter,
    emitter: &impl Emitter,
    format: &dyn InstrFormat,
    instrs: &[RawInstr],
) -> WriteResult {
    for (index, instr) in instrs.iter().enumerate() {
        emitter.chain_with(|f| write!(f, "in instruction {}", index), |emitter| {
            format.write_instr(f, emitter, instr)
        })?;
    }
    emitter.chain_with(|f| write!(f, "writing script end marker"), |emitter| {
        format.write_terminal_instr(f, emitter)
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

    pub fn get_opcode(&self, intrinsic: IntrinsicInstrKind, span: Span, descr: &str) -> Result<u16, Diagnostic> {
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

#[derive(Debug)]
pub enum ReadInstr {
    /// A regular instruction was read that belongs in the script.
    Instr(RawInstr),
    /// A terminal instruction was read.  This is a dummy instruction at the end of every script
    /// that can be easily distinguished from real instructions, due to e.g. an opcode of -1
    /// or similar.
    ///
    /// When this is returned, the read cursor may be left in an indeterminate state.
    Terminal,
    /// In some formats, the terminal instruction is indistinguishable from a real instruction.
    /// (e.g. it is all zeros).  In that case, this variant is returned instead of [`Self::Terminal`].
    ///
    /// The script reader will only consider this to be the terminal instruction if it ends at
    /// the expected "script end offset" (or if it is followed by [`Self::EoF`]).
    MaybeTerminal(RawInstr),
    /// No instruction was read because we are at EOF.
    ///
    /// (This is only for EOF at the *beginning* of an instruction; EOF in the middle of an
    /// instruction should report `Err` instead.)
    ///
    /// Implementations of [`InstrFormat::read_instr`] are only required to report this if they
    /// use [`Self::MaybeTerminal`].  Otherwise, it is preferred to return `Err`.
    EndOfFile,
}

pub trait InstrFormat {
    fn intrinsic_instrs(&self) -> IntrinsicInstrs {
        IntrinsicInstrs::from_pairs(self.intrinsic_opcode_pairs())
    }

    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, u16)>;

    /// Get the number of bytes in the binary encoding of an instruction's header (before the arguments).
    fn instr_header_size(&self) -> usize;

    /// Read a single script instruction from an input stream, which may be a terminal instruction.
    fn read_instr(&self, f: &mut BinReader, emitter: &dyn Emitter) -> ReadResult<ReadInstr>;

    /// Write a single script instruction into an output stream.
    fn write_instr(&self, f: &mut BinWriter, emitter: &dyn Emitter, instr: &RawInstr) -> WriteResult;

    /// Write a marker that goes after the final instruction in a function or script.
    fn write_terminal_instr(&self, f: &mut BinWriter, emitter: &dyn Emitter) -> WriteResult;

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
    fn read_instr(&self, _: &mut BinReader, _: &dyn Emitter) -> ReadResult<ReadInstr> { panic!("TestInstrFormat does not implement reading or writing") }
    fn write_instr(&self, _: &mut BinWriter, _: &dyn Emitter, _: &RawInstr) -> WriteResult { panic!("TestInstrFormat does not implement reading or writing") }
    fn write_terminal_instr(&self, _: &mut BinWriter, _: &dyn Emitter) -> WriteResult { panic!("TestInstrFormat does not implement reading or writing")  }

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

#[cfg(test)]
mod test_reader {
    #![allow(non_snake_case)]
    use super::*;
    use crate::error::ErrorReported;

    struct SimpleInstrReader {
        iter: std::cell::RefCell<std::vec::IntoIter<ReadInstr>>
    }

    impl SimpleInstrReader {
        fn new(vec: Vec<ReadInstr>) -> Self {
            SimpleInstrReader { iter: std::cell::RefCell::new(vec.into_iter()) }
        }
    }

    impl InstrFormat for SimpleInstrReader {
        fn instr_header_size(&self) -> usize { 0x10 }
        fn read_instr(&self, _: &mut BinReader, _: &dyn Emitter) -> ReadResult<ReadInstr> {
            Ok(self.iter.borrow_mut().next().expect("instr reader tried to read too many instrs!"))
        }
        fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, u16)> { vec![] }
        fn write_instr(&self, _: &mut BinWriter, _: &dyn Emitter, _: &RawInstr) -> WriteResult { panic!("SimpleInstrReader does not implement reading or writing") }
        fn write_terminal_instr(&self, _: &mut BinWriter, _: &dyn Emitter) -> WriteResult { panic!("SimpleInstrReader does not implement reading or writing")  }
    }

    fn simple_instr(opcode: u16) -> RawInstr {
        RawInstr { opcode, time: 0, param_mask: 0, args_blob: vec![] }
    }

    struct TestInput {
        instrs: Vec<ReadInstr>,
        end_offset: Option<u64>,
    }

    #[derive(Debug)]
    struct SuccessfulOutput {
        output: Vec<RawInstr>,
        warnings: String,
    }

    impl TestInput {
        fn run(self) -> Result<SuccessfulOutput, String> {
            let mut scope = crate::Builder::new().capture_diagnostics(true).build();
            let mut truth = scope.truth();
            let ctx = truth.ctx();
            let result = read_instrs(
                &mut BinReader::from_reader(ctx.emitter, "unused", std::io::empty()),
                ctx.emitter,
                &SimpleInstrReader::new(self.instrs),
                0x100, // starting_offset
                self.end_offset, // end_offset
            );
            let diagnostic_str = truth.get_captured_diagnostics().unwrap();
            match result {
                Err(ErrorReported) => Err(diagnostic_str),
                Ok(output) => Ok(SuccessfulOutput { output, warnings: diagnostic_str }),
            }
        }
    }

    #[test]
    fn terminal() {
        let results = TestInput {
            instrs: vec![
                ReadInstr::Instr(simple_instr(0)),
                ReadInstr::Instr(simple_instr(1)),
                ReadInstr::Terminal,
            ],
            end_offset: None,
        }.run().unwrap();
        assert_eq!(results.output, (0..=1).map(simple_instr).collect::<Vec<_>>());
        assert_eq!(results.warnings, String::new());
    }

    #[test]
    fn maybe_terminal__eof() {
        let results = TestInput {
            instrs: vec![
                ReadInstr::Instr(simple_instr(0)),
                ReadInstr::MaybeTerminal(simple_instr(1)),
                ReadInstr::Instr(simple_instr(2)),
                ReadInstr::MaybeTerminal(simple_instr(3)),
                ReadInstr::MaybeTerminal(simple_instr(4)),  // not included in output
                ReadInstr::EndOfFile,
            ],
            end_offset: None,
        }.run().unwrap();
        assert_eq!(results.output, (0..=3).map(simple_instr).collect::<Vec<_>>());
        assert_eq!(results.warnings, String::new());
    }

    #[test]
    fn maybe_terminal__end_offset() {
        let results = TestInput {
            instrs: vec![
                ReadInstr::Instr(simple_instr(0)),
                ReadInstr::MaybeTerminal(simple_instr(1)),
                ReadInstr::Instr(simple_instr(2)),
                ReadInstr::MaybeTerminal(simple_instr(3)),
                ReadInstr::MaybeTerminal(simple_instr(4)),  // not included in output
                // vec ends here to deliberately panic if an extra read attempt is made
            ],
            end_offset: Some(0x150),
        }.run().unwrap();
        assert_eq!(results.output, (0..=3).map(simple_instr).collect::<Vec<_>>());
        assert_eq!(results.warnings, String::new());
    }

    #[test]
    fn missing_end_of_script__end_offset() {
        let results = TestInput {
            instrs: vec![
                ReadInstr::Instr(simple_instr(0)),
                ReadInstr::MaybeTerminal(simple_instr(1)),
                ReadInstr::Instr(simple_instr(2)),
                // vec ends here to deliberately panic if an extra read attempt is made
            ],
            end_offset: Some(0x130),
        }.run().unwrap();
        assert_eq!(results.output, (0..=2).map(simple_instr).collect::<Vec<_>>());
        assert!(results.warnings.contains("missing end-of-script"), "{}", results.warnings);
    }

    #[test]
    fn missing_end_of_script__eof() {
        let results = TestInput {
            instrs: vec![
                ReadInstr::Instr(simple_instr(0)),
                ReadInstr::MaybeTerminal(simple_instr(1)),
                ReadInstr::Instr(simple_instr(2)),
                ReadInstr::EndOfFile,
            ],
            end_offset: None,
        }.run().unwrap();
        assert_eq!(results.output, (0..=2).map(simple_instr).collect::<Vec<_>>());
        assert!(results.warnings.contains("missing end-of-script"), "{}", results.warnings);
    }

    #[test]
    fn invalid_end_of_script() {
        let stderr = TestInput {
            instrs: vec![
                ReadInstr::Instr(simple_instr(0)),
                ReadInstr::MaybeTerminal(simple_instr(1)),
                ReadInstr::Instr(simple_instr(2)),
                ReadInstr::MaybeTerminal(simple_instr(3)),
                ReadInstr::MaybeTerminal(simple_instr(4)),
                ReadInstr::EndOfFile,
            ],
            end_offset: Some(0x134),
        }.run().unwrap_err();
        assert!(stderr.contains("read past"));
    }
}
