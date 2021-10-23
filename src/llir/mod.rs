use enum_map::EnumMap;

use crate::raw;
use crate::game::InstrLanguage;
use crate::io::{BinReader, BinWriter, ReadResult, WriteResult};
use crate::diagnostic::{Diagnostic, Emitter};
use crate::value::{ScalarValue, ScalarType};
use crate::resolve::{RegId};

pub use abi::{InstrAbi, ArgEncoding, AcceleratingByteMask, TimelineArgKind};
mod abi;

pub use lower::lower_sub_ast_to_instrs;
mod lower;

pub use raise::{Raiser, DecompileOptions};
mod raise;

pub use intrinsic::{IntrinsicInstrs, IntrinsicInstrKind, JumpIntrinsicArgOrder};
mod intrinsic;

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
    /// The time label of the instruction.
    pub time: raw::Time,
    pub opcode: raw::Opcode,
    /// A mask indicating which arguments are registers, in languages that support registers.
    ///
    /// In other languages, it is zero.
    pub param_mask: raw::ParamMask,
    /// The bytes after the instruction header, exactly as they will appear in the file.
    pub args_blob: Vec<u8>,
    /// Difficulty mask.
    pub difficulty: raw::DifficultyMask,
    /// Stack change arg.  Only used in modern ECL.  Zero in other languages.
    pub pop: raw::StackPop,
    /// Used by ECL timelines.  `None` elsewhere.
    pub extra_arg: Option<raw::ExtraArg>,
}

impl RawInstr {
    pub const DEFAULTS: RawInstr = RawInstr {
        time: 0, opcode: 0,
        args_blob: Vec::new(), extra_arg: None,
        param_mask: 0,
        difficulty: crate::passes::semantics::time_and_difficulty::DEFAULT_DIFFICULTY_MASK,
        pop: 0,
    };
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
    pub fn expect_immediate_int(&self) -> raw::LangInt {
        assert!(!self.is_reg);
        self.expect_int()
    }

    #[track_caller]
    pub fn expect_int(&self) -> raw::LangInt {
        match self.value {
            ScalarValue::Int(x) => x,
            _ => panic!("{:?}", self),
        }
    }

    #[track_caller]
    pub fn expect_float(&self) -> raw::LangFloat {
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

impl From<raw::LangInt> for SimpleArg {
    fn from(x: raw::LangInt) -> SimpleArg { SimpleArg { value: ScalarValue::Int(x), is_reg: false } }
}

impl From<raw::LangFloat> for SimpleArg {
    fn from(x: raw::LangFloat) -> SimpleArg { SimpleArg { value: ScalarValue::Float(x), is_reg: false } }
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
    starting_offset: raw::BytePos,
    end_offset: Option<raw::BytePos>,
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
                cur_offset += format.instr_size(&instr) as raw::BytePos;

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

/// The trait that handles most differences between languages in their instruction formats.
///
/// It is responsible for:
///
/// * Parsing instruction headers from bytestreams (or similarly, writing them).
/// * Extracting the blob of bytes for the args of an instruction.
/// * Mapping language features to instruction opcodes and vice versa.
/// * Declaratively describing the availability of language features like the stack, jumps, and stack registers.
///   (this information gets used by the `lower` and `raise` modules to determine how to compile/decompile things)
///
/// It is expressly NOT responsible for:
///
/// * Parsing the headers of the files themselves, or any other data that isn't instruction-related.
///   That is all done in e.g. `format/anm`.
/// * The actual implementation of the check for where a script ends.
/// * Parsing the actual instruction args from the byte blobs.
pub trait InstrFormat {
    /// Language key, so that signatures can be looked up for the right type of instruction (e.g. ECL vs timeline).
    fn language(&self) -> InstrLanguage;

    fn has_registers(&self) -> bool;

    fn intrinsic_instrs(&self) -> IntrinsicInstrs {
        IntrinsicInstrs::from_pairs(self.intrinsic_opcode_pairs())
    }

    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, raw::Opcode)>;

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
    fn instr_disables_scratch_regs(&self, _opcode: raw::Opcode) -> bool { false }

    /// Used by TH06 to indicate that an instruction must be the last instruction in the script.
    fn is_th06_anm_terminating_instr(&self, _opcode: raw::Opcode) -> bool { false }

    // Most formats encode labels as offsets from the beginning of the script, but:
    // * early STD writes the instruction *index*.
    // * early (?) ECL writes offsets relative to the current instruction.
    // both args here are relative to the beginning of the sub.
    fn encode_label(&self, _cur_offset: raw::BytePos, dest_offset: raw::BytePos) -> raw::RawDwordBits { dest_offset as _ }
    fn decode_label(&self, _cur_offset: raw::BytePos, bits: raw::RawDwordBits) -> raw::BytePos { bits as _ }

    /// Helper method that returns the total instruction size, including the arguments.
    /// There should be no need to override this.
    fn instr_size(&self, instr: &RawInstr) -> usize { self.instr_header_size() + instr.args_blob.len() }

    /// Initial difficulty mask.  In languages without difficulty, this returns `None.
    fn default_difficulty_mask(&self) -> Option<raw::DifficultyMask> { None }

    /// In EoSD ECL, the value of an argument can, in some cases, decide if it is
    /// a literal or a register.
    fn register_style(&self) -> RegisterEncodingStyle { RegisterEncodingStyle::ByParamMask }
}

#[derive(Copy, Clone)]
pub enum RegisterEncodingStyle {
    /// The language encodes "registerness" of arguments in the parameter mask.
    ByParamMask,
    /// The language is EoSD ECL and all registers are just special values.
    EosdEcl { does_value_look_like_a_register: fn(&ScalarValue) -> bool },
}

/// An implementation of InstrFormat for testing the raising and lowering phases of compilation.
#[derive(Debug, Clone)]
pub struct TestFormat {
    pub language: InstrLanguage,
    pub intrinsic_opcode_pairs: Vec<(IntrinsicInstrKind, raw::Opcode)>,
    pub general_use_int_regs: Vec<RegId>,
    pub general_use_float_regs: Vec<RegId>,
    /// For simulating the existence of an instruction like ANM `ins_509`
    pub anti_scratch_opcode: Option<raw::Opcode>,
}

impl Default for TestFormat {
    fn default() -> Self {
        TestFormat {
            language: InstrLanguage::Dummy,
            intrinsic_opcode_pairs: Default::default(),
            general_use_int_regs: Default::default(),
            general_use_float_regs: Default::default(),
            anti_scratch_opcode: None,
        }
    }
}

impl InstrFormat for TestFormat {
    fn language(&self) -> InstrLanguage { self.language }

    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, raw::Opcode)> {
        self.intrinsic_opcode_pairs.clone()
    }

    fn instr_header_size(&self) -> usize { 4 }
    fn read_instr(&self, _: &mut BinReader, _: &dyn Emitter) -> ReadResult<ReadInstr> { panic!("TestInstrFormat does not implement reading or writing") }
    fn write_instr(&self, _: &mut BinWriter, _: &dyn Emitter, _: &RawInstr) -> WriteResult { panic!("TestInstrFormat does not implement reading or writing") }
    fn write_terminal_instr(&self, _: &mut BinWriter, _: &dyn Emitter) -> WriteResult { panic!("TestInstrFormat does not implement reading or writing")  }

    fn instr_disables_scratch_regs(&self, opcode: raw::Opcode) -> bool {
        self.anti_scratch_opcode == Some(opcode)
    }

    fn has_registers(&self) -> bool { true }

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
        fn language(&self) -> InstrLanguage { InstrLanguage::Dummy }
        fn has_registers(&self) -> bool { true }
        fn instr_header_size(&self) -> usize { 0x10 }
        fn read_instr(&self, _: &mut BinReader, _: &dyn Emitter) -> ReadResult<ReadInstr> {
            Ok(self.iter.borrow_mut().next().expect("instr reader tried to read too many instrs!"))
        }
        fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, raw::Opcode)> { vec![] }
        fn write_instr(&self, _: &mut BinWriter, _: &dyn Emitter, _: &RawInstr) -> WriteResult { panic!("SimpleInstrReader does not implement reading or writing") }
        fn write_terminal_instr(&self, _: &mut BinWriter, _: &dyn Emitter) -> WriteResult { panic!("SimpleInstrReader does not implement reading or writing")  }
    }

    fn simple_instr(opcode: raw::Opcode) -> RawInstr {
        RawInstr { opcode, ..RawInstr::DEFAULTS }
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
