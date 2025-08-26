use enum_map::EnumMap;

use crate::raw;
use crate::game::LanguageKey;
use crate::io::{BinReader, BinWriter, ReadResult, WriteResult};
use crate::diagnostic::{Diagnostic, Emitter};
use crate::value::{ScalarValue, ScalarType, ReadType};
use crate::resolve::{RegId};

pub use abi::{InstrAbi, ArgEncoding, AcceleratingByteMask, StringArgSize};
mod abi;

pub use lower::Lowerer;
mod lower;

pub use raise::{Raiser, DecompileOptions, CallRegSignatures};
mod raise;

pub use intrinsic::{IntrinsicInstrs, IntrinsicInstrKind, alternatives, AlternativesInfo};
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
    /// Used by stack ECL.  Read by the `printf` instructions.  Zero in other formats.
    pub arg_count: raw::ArgCount,
}

impl RawInstr {
    pub const DEFAULTS: RawInstr = RawInstr {
        time: 0, opcode: 0, param_mask: 0, pop: 0,
        args_blob: Vec::new(),
        extra_arg: None, arg_count: 0,
        difficulty: crate::passes::semantics::time_and_difficulty::DEFAULT_DIFFICULTY_MASK_BYTE,
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
    pub fn expect_immediate(&self) -> &ScalarValue {
        assert!(!self.is_reg);
        &self.value
    }

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

    pub fn is_immediate_zero(&self) -> bool {
        matches!(self, SimpleArg { is_reg: false, value: ScalarValue::Int(0), .. })
    }
}

impl SimpleArg {
    /// Construct a register SimpleArg whose ID is encoded as a given datatype.
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

impl From<ScalarValue> for SimpleArg {
    fn from(value: ScalarValue) -> SimpleArg { SimpleArg { value, is_reg: false } }
}

impl From<raw::LangInt> for SimpleArg {
    fn from(x: raw::LangInt) -> SimpleArg { ScalarValue::Int(x).into() }
}

impl From<raw::LangFloat> for SimpleArg {
    fn from(x: raw::LangFloat) -> SimpleArg { ScalarValue::Float(x).into() }
}

impl From<String> for SimpleArg {
    fn from(x: String) -> SimpleArg { ScalarValue::String(x).into() }
}

fn unsupported(span: crate::pos::Span, what: &str) -> Diagnostic {
    error!(
        message("feature not supported by format"),
        primary(span, "{what} not supported by format"),
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

    let has_terminal_instr = format.has_terminal_instr();

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
                    if has_terminal_instr && possible_terminal.is_none() {
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
                if has_terminal_instr && possible_terminal.is_none() {
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
    if format.has_terminal_instr() {
        emitter.chain_with(|f| write!(f, "writing script end marker"), |emitter| {
            format.write_terminal_instr(f, emitter)
        })?;
    }
    Ok(())
}

// =============================================================================
// Hooks for use during raising/lowering

/// The trait that provides hooks for dealing with most differences between script languages.
///
/// In this context, "language" is referring to a property of a single item/script within a file.
/// E.g. ECL and ECL Timeline are two different languages that can appear in the same file.
///
/// It is responsible for mapping language features to instruction opcodes (FIXME: move to core mapfiles?),
/// and declaratively describing the availability of language features like the stack, jumps, and stack registers.
/// (this information gets used by the `lower` and `raise` modules to determine how to compile/decompile things)
pub trait LanguageHooks {
    /// Language key, so that signatures can be looked up for the right type of instruction (e.g. ECL vs timeline).
    fn language(&self) -> LanguageKey;

    fn has_registers(&self) -> bool;

    // ---------------------------------------------------
    // Special purpose functions only overridden by a few formats

    /// List of registers available for scratch use in formats without a stack.
    fn general_use_regs(&self) -> EnumMap<ScalarType, Vec<RegId>> {
        enum_map::enum_map!(_ => vec![])
    }

    /// Should return `true` if this instruction makes it dangerous to use scratch registers.
    ///
    /// Normally, most things that are implicitly read by an instruction must also be set by the
    /// caller, and anything set by an instruction can be typically assumed to be meaningless unless
    /// it is read by the caller.  Thus, the standard "register usage" analysis suffices for 99% of
    /// instructions.
    ///
    /// But there are some particularly *evil* instructions that can cause action at a distance,
    /// typically in a setup involving at least 3 functions.
    ///
    /// For instance, ANM `ins_509` copies all variables from the parent.  If you have three
    /// scripts set up like `grandparent->parent->child` and this is used by both `parent` and `child`,
    /// then there could be registers that are dangerous to modify in `parent` despite not being
    /// mentioned at all in its script!
    fn instr_disables_scratch_regs(&self, _opcode: raw::Opcode) -> Option<HowBadIsIt> { None }

    /// Used by TH06 to indicate that an instruction must be the last instruction in the script.
    fn is_th06_anm_terminating_instr(&self, _opcode: raw::Opcode) -> bool { false }

    // Most formats encode labels as offsets from the beginning of the script, but:
    // * early STD writes the instruction *index*.
    // * early (?) ECL writes offsets relative to the current instruction.
    // both args here are relative to the beginning of the sub.
    fn encode_label(&self, _cur_offset: raw::BytePos, dest_offset: raw::BytePos) -> raw::RawDwordBits { dest_offset as _ }
    fn decode_label(&self, _cur_offset: raw::BytePos, bits: raw::RawDwordBits) -> raw::BytePos { bits as _ }

    /// Initial difficulty mask.  In languages without difficulty, this returns `None.
    fn default_difficulty_mask(&self) -> Option<raw::DifficultyMask> { None }

    /// The register that contains the current difficulty.  Only for use in diagnostic messages.
    fn difficulty_register(&self) -> Option<RegId> { None }

    /// In EoSD ECL, the value of an argument can, in some cases, decide if it is
    /// a literal or a register.
    fn register_style(&self) -> RegisterEncodingStyle { RegisterEncodingStyle::ByParamMask }

    /// The argument registers of each type for [`IntrinsicInstrKind::CallReg`].
    fn arg_registers(&self) -> Option<EnumMap<ReadType, &[RegId]>> { None }

    /// Get the [`InstrFormat`].  One might've expected that the raising/lowering phases *shouldn't*
    /// need this, but they do need it in order to deal with jump offsets.
    fn instr_format(&self) -> &dyn InstrFormat;

    /// Should return `true` if the language automatically casts variables when read as another type.
    ///
    /// Only EoSD ECL doesn't do this.
    fn has_auto_casts(&self) -> bool { true }
}

/// How bad is the scratch-disabling-ness of this instruction?
#[derive(Copy, Clone)]
pub enum HowBadIsIt {
    OhItsJustThisOneFunction,
    ItsWaterElf,
}

#[derive(Copy, Clone)]
pub enum RegisterEncodingStyle {
    /// The language encodes "registerness" of arguments in the parameter mask.
    ByParamMask,
    /// The language is EoSD ECL and all registers are just special values.
    EosdEcl { does_value_look_like_a_register: fn(&ScalarValue) -> bool },
}

// =============================================================================
// For dealing with instructions <-> bytestreams

/// Trait for reading and writing single instructions in raw form.
///
/// It is responsible for:
///
/// * Parsing instruction headers from bytestreams (or similarly, writing them).
/// * Extracting the blob of bytes for the args of an instruction.
///
/// It is expressly NOT responsible for:
///
/// * Parsing the headers of the files themselves, or any other data that isn't instruction-related.
///   That is all done in e.g. `format/anm`.
/// * The actual implementation of the check for where a script ends.
/// * Converting the byte blobs to/from argument lists.
pub trait InstrFormat {
    /// Get the number of bytes in the binary encoding of an instruction's header (before the arguments).
    fn instr_header_size(&self) -> usize;

    /// Returns `true` if there is a dummy instruction at the end of every script.
    ///
    /// Only stack ECL lacks terminal instructions.  Where present, these instruction will be stripped
    /// from decompiled output and inserted on compilation.
    ///
    /// (if this returns `false`, [`ReadInstr`] should always return `Instr`, and [`crate::llir::read_instrs`]
    /// must be provided with an end offset)
    fn has_terminal_instr(&self) -> bool { true }

    /// Read a single script instruction from an input stream, which may be a terminal instruction.
    fn read_instr(&self, f: &mut BinReader, emitter: &dyn Emitter) -> ReadResult<ReadInstr>;

    /// Write a single script instruction into an output stream.
    fn write_instr(&self, f: &mut BinWriter, emitter: &dyn Emitter, instr: &RawInstr) -> WriteResult;

    /// Write a marker that goes after the final instruction in a function or script.
    ///
    /// If [`InstrFormat::has_terminal_instr`] returns `false`, this should simply panic.
    fn write_terminal_instr(&self, f: &mut BinWriter, emitter: &dyn Emitter) -> WriteResult;

    /// Helper method that returns the total instruction size, including the arguments.
    /// There should be no need to override this.
    fn instr_size(&self, instr: &RawInstr) -> usize { self.instr_header_size() + instr.args_blob.len() }
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

// =============================================================================

/// An implementation of [`LanguageHooks`] and [`InstrFormat`] for testing the raising
/// and lowering phases of compilation.
#[derive(Debug, Clone)]
pub struct TestLanguage {
    pub language: LanguageKey,
    pub general_use_int_regs: Vec<RegId>,
    pub general_use_float_regs: Vec<RegId>,
    /// For simulating the existence of an instruction like ANM `ins_509`
    pub anti_scratch_opcode: Option<raw::Opcode>,
}

impl Default for TestLanguage {
    fn default() -> Self {
        TestLanguage {
            language: LanguageKey::Dummy,
            general_use_int_regs: Default::default(),
            general_use_float_regs: Default::default(),
            anti_scratch_opcode: None,
        }
    }
}

impl LanguageHooks for TestLanguage {
    fn language(&self) -> LanguageKey { self.language }

    fn instr_disables_scratch_regs(&self, opcode: raw::Opcode) -> Option<HowBadIsIt> {
        (self.anti_scratch_opcode == Some(opcode)).then(|| HowBadIsIt::OhItsJustThisOneFunction)
    }

    fn has_registers(&self) -> bool { true }

    fn general_use_regs(&self) -> EnumMap<ScalarType, Vec<RegId>> {
        enum_map::enum_map!{
            ScalarType::Int => self.general_use_int_regs.clone(),
            ScalarType::Float => self.general_use_float_regs.clone(),
            ScalarType::String => vec![],
        }
    }

    fn instr_format(&self) -> &dyn InstrFormat { self }
}

impl InstrFormat for TestLanguage {
    fn instr_header_size(&self) -> usize { 4 }
    fn read_instr(&self, _: &mut BinReader, _: &dyn Emitter) -> ReadResult<ReadInstr> { panic!("TestInstrFormat does not implement reading or writing") }
    fn write_instr(&self, _: &mut BinWriter, _: &dyn Emitter, _: &RawInstr) -> WriteResult { panic!("TestInstrFormat does not implement reading or writing") }
    fn write_terminal_instr(&self, _: &mut BinWriter, _: &dyn Emitter) -> WriteResult { panic!("TestInstrFormat does not implement reading or writing")  }
}

#[cfg(test)]
mod test_reader {
    #![allow(non_snake_case)]
    use super::*;
    use crate::error::ErrorReported;

    struct SimpleInstrReader {
        has_terminal: bool,
        iter: std::cell::RefCell<std::vec::IntoIter<ReadInstr>>
    }

    impl SimpleInstrReader {
        fn new(has_terminal: bool, vec: Vec<ReadInstr>) -> Self {
            SimpleInstrReader { has_terminal, iter: std::cell::RefCell::new(vec.into_iter()) }
        }
    }

    impl InstrFormat for SimpleInstrReader {
        fn instr_header_size(&self) -> usize { 0x10 }
        fn has_terminal_instr(&self) -> bool { self.has_terminal }
        fn read_instr(&self, _: &mut BinReader, _: &dyn Emitter) -> ReadResult<ReadInstr> {
            Ok(self.iter.borrow_mut().next().expect("instr reader tried to read too many instrs!"))
        }
        fn write_instr(&self, _: &mut BinWriter, _: &dyn Emitter, _: &RawInstr) -> WriteResult { panic!("SimpleInstrReader does not implement reading or writing") }
        fn write_terminal_instr(&self, _: &mut BinWriter, _: &dyn Emitter) -> WriteResult { panic!("SimpleInstrReader does not implement reading or writing")  }
    }

    fn simple_instr(opcode: raw::Opcode) -> RawInstr {
        RawInstr { opcode, ..RawInstr::DEFAULTS }
    }

    struct TestInput {
        format_has_terminals: bool,
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
                &SimpleInstrReader::new(self.format_has_terminals, self.instrs),
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
            format_has_terminals: true,
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
            format_has_terminals: true,
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
            format_has_terminals: true,
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
            format_has_terminals: true,
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
            format_has_terminals: true,
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
            format_has_terminals: true,
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

    #[test]
    fn no_terminal__end_offset() {
        let results = TestInput {
            format_has_terminals: false,
            instrs: vec![
                ReadInstr::Instr(simple_instr(0)),
                ReadInstr::Instr(simple_instr(1)),
            ],
            end_offset: Some(0x120),
        }.run().unwrap();
        assert_eq!(results.output, (0..=1).map(simple_instr).collect::<Vec<_>>());
        assert!(results.warnings.is_empty());
    }

    #[test]
    fn no_terminal__eof() {
        let results = TestInput {
            format_has_terminals: false,
            instrs: vec![
                ReadInstr::Instr(simple_instr(0)),
                ReadInstr::Instr(simple_instr(1)),
                ReadInstr::EndOfFile,
            ],
            end_offset: None,
        }.run().unwrap();
        assert_eq!(results.output, (0..=1).map(simple_instr).collect::<Vec<_>>());
        assert!(results.warnings.is_empty());
    }
}
