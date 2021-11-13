use std::collections::{BTreeMap, BTreeSet};

use crate::raw;
use crate::ast::{self, pseudo};
use crate::ast::diff_str::DiffFlagNames;
use crate::ident::{Ident, ResIdent};
use crate::pos::{Sp, Span};
use crate::diagnostic::{Emitter};
use crate::error::{ErrorReported};
use crate::llir::{RawInstr, LanguageHooks, IntrinsicInstrKind, IntrinsicInstrs, SimpleArg};
use crate::llir::intrinsic::{IntrinsicInstrAbiParts, abi_parts};
use crate::resolve::{RegId};
use crate::context::{self, Defs, CompilerContext};
use crate::game::LanguageKey;
use crate::llir::{ArgEncoding, TimelineArgKind, InstrAbi, RegisterEncodingStyle};
use crate::value::{ScalarValue};
use crate::passes::semantics::time_and_difficulty::{DEFAULT_DIFFICULTY_MASK, DEFAULT_DIFFICULTY_MASK_BYTE};
use crate::diff_switch_utils::{self as ds_util, DiffSwitchSlice, DiffSwitchVec};
use crate::io::{DEFAULT_ENCODING, Encoded};

use IntrinsicInstrKind as IKind;
use crate::bitset::BitSet32;

#[derive(Debug, Clone)]
pub struct DecompileOptions {
    pub arguments: bool,
    pub intrinsics: bool,  // invariant: intrinsics implies arguments
    pub blocks: bool,
}

impl DecompileOptions {
    /// Construct with all features enabled.
    pub fn new() -> Self { Default::default() }
}

impl Default for DecompileOptions {
    fn default() -> Self {
        DecompileOptions { arguments: true, intrinsics: true, blocks: true }
    }
}

/// Intermediate form of an instruction only used during decompilation.
#[derive(Debug)]
struct RaiseInstr<Arg = SimpleArg, Offset = raw::BytePos> {
    /// NOTE: In CompressedInstr this is a vec with the offset of each original instr.
    offset: Offset,
    time: raw::Time,
    difficulty_mask: raw::DifficultyMask,
    opcode: raw::Opcode,
    args: RaiseArgs<Arg>,
}
type CompressedInstr = RaiseInstr<CompressedArg, DiffSwitchVec<raw::BytePos>>;

#[derive(Debug)]
enum RaiseArgs<Arg> {
    /// The ABI of the instruction was known, so we parsed the argument bytes into arguments.
    Decoded(Vec<Arg>),
    /// The ABI was not known, so we will be emitting pseudo-args like `@blob=`.
    Unknown(UnknownArgsData),
}

impl<Arg> RaiseArgs<Arg> {
    fn decoded(&self) -> Option<&[Arg]> { match self {
        RaiseArgs::Decoded(args) => Some(args),
        RaiseArgs::Unknown { .. } => None,
    }}
}

enum CompressedArg {
    DiffSwitch(DiffSwitchVec<SimpleArg>),
    Single(SimpleArg),
}

impl CompressedArg {
    fn iter_raw_args(&self) -> impl Iterator<Item=&SimpleArg> + '_ {
        match self {
            CompressedArg::Single(x) => Box::new(core::iter::once(x)) as Box<dyn Iterator<Item=&SimpleArg>>,
            CompressedArg::DiffSwitch(args) => Box::new(args.iter().filter_map(|opt| opt.as_ref())),
        }
    }
}

#[derive(Debug, Clone)]
struct UnknownArgsData {
    param_mask: raw::ParamMask,
    extra_arg: Option<raw::ExtraArg>,
    blob: Vec<u8>,
}

/// Type that provides methods to raise instructions to AST nodes.
///
/// It tracks some state related to diagnostics, so that some consolidated warnings
/// can be given at the end of decompilation.
pub struct Raiser<'a> {
    hooks: &'a dyn LanguageHooks,
    opcodes_without_abis: BTreeSet<u16>,
    // Root emitter because we don't want any additional context beyond the filename.
    emitter_for_abi_warnings: &'a context::RootEmitter,
    options: &'a DecompileOptions,
    intrinsic_instrs: IntrinsicInstrs,
}

impl Drop for Raiser<'_> {
    fn drop(&mut self) {
        self.generate_warnings();
    }
}

impl<'a> Raiser<'a> {
    pub fn new(
        hooks: &'a dyn LanguageHooks,
        emitter: &'a context::RootEmitter,
        defs: &context::Defs,
        options: &'a DecompileOptions,
    ) -> Result<Self, ErrorReported> {
        Ok(Raiser {
            hooks,
            opcodes_without_abis: Default::default(),
            emitter_for_abi_warnings: emitter,
            // If intrinsic decompilation is disabled, simply pretend that there aren't any intrinsics.
            intrinsic_instrs: match options.intrinsics {
                true => IntrinsicInstrs::from_format_and_mapfiles(hooks, defs, emitter)?,
                false => Default::default(),
            },
            options,
        })
    }

    pub fn raise_instrs_to_sub_ast(
        &mut self,
        emitter: &dyn Emitter,
        raw_script: &[RawInstr],
        ctx: &CompilerContext<'_>,
    ) -> Result<Vec<Sp<ast::Stmt>>, ErrorReported> {
        let mut stmts = _raise_instrs_to_sub_ast(self, &emitter, raw_script, ctx)?;
        crate::passes::resolution::fill_missing_node_ids(&mut stmts[..], &ctx.unused_node_ids)?;
        Ok(stmts)
    }

    pub fn generate_warnings(&mut self) {
        if !self.opcodes_without_abis.is_empty() {
            self.emitter_for_abi_warnings.emit(warning!(
                message("{} instructions with unknown signatures were decompiled to byte blobs.", self.hooks.language().descr()),
                note(
                    "The following opcodes were affected: {}",
                    self.opcodes_without_abis.iter()
                        .map(|opcode| opcode.to_string()).collect::<Vec<_>>().join(", ")
                ),
            )).ignore();
        }

        self.opcodes_without_abis.clear();
    }
}

fn _raise_instrs_to_sub_ast(
    raiser: &mut Raiser,
    emitter: &impl Emitter,
    raw_script: &[RawInstr],
    ctx: &CompilerContext,
) -> Result<Vec<Sp<ast::Stmt>>, ErrorReported> {
    let hooks = raiser.hooks;
    let ref instr_offsets = gather_instr_offsets(raw_script, hooks);

    // Preprocess by using mapfile signatures to parse arguments
    let script: Vec<RaiseInstr> = {
        raw_script.iter().zip(instr_offsets)
            .map(|(raw_instr, &instr_offset)| raiser.decode_args(emitter, raw_instr, instr_offset, &ctx.defs))
            .collect::<Result<_, _>>()?
    };

    let ref jump_data = gather_jump_time_args(&script, &ctx.defs, hooks)?;
    let ref offset_labels = generate_offset_labels(emitter, &script, instr_offsets, jump_data)?;

    let &end_offset = instr_offsets.last().expect("n + 1 offsets so there's always at least one");
    let intrinsic_instrs = &raiser.intrinsic_instrs;
    SingleSubRaiser {
        emitter, hooks, end_offset, offset_labels, intrinsic_instrs,
        defs: &ctx.defs,
        diff_flag_names: &ctx.diff_flag_names,
    }.raise_instrs(&script)
}

/// Type containing all sorts of info about the current sub so that functions involved in
/// raising instrs to statements don't need to take 50 arguments.
struct SingleSubRaiser<'a> {
    // context
    end_offset: raw::BytePos,
    offset_labels: &'a BTreeMap<raw::BytePos, Label>,
    intrinsic_instrs: &'a IntrinsicInstrs,
    hooks: &'a dyn LanguageHooks,
    emitter: &'a dyn Emitter,
    defs: &'a context::Defs,
    diff_flag_names: &'a DiffFlagNames,
}

/// Methods where all of the fallback logic concerning diff switches and intrinsics is implemented.
impl SingleSubRaiser<'_> {
    fn raise_instrs(&self, script: &[RaiseInstr]) -> Result<Vec<Sp<ast::Stmt>>, ErrorReported> {
        let mut out = vec![];
        let mut label_gen = LabelEmitter::new(self.offset_labels, self.diff_flag_names);
        let mut remaining_instrs = script;

        // assert!(!script.iter().any(|instr| instr.offset == 1766), "{:#?}", script);
        'instr: while remaining_instrs.len() > 0 {
            // Eagerly try compressing multiple instructions using diff switches.
            if let Some(compressed_instr) = try_compress_instr(remaining_instrs, |offset| self.offset_labels.contains_key(&offset)) {
                let args = compressed_instr.args.decoded().expect("a blob wouldn't have compressed");

                match self.try_raise_single_instr_intrinsic(&compressed_instr, args) {
                    Ok(raised_intrinsic) => {
                        // if this returned Ok, then whether its an intrinsic or not, we're going to emit it
                        label_gen.emit_labels_for_instr(&mut out, &compressed_instr);
                        out.push(self.make_stmt(compressed_instr.difficulty_mask, match raised_intrinsic {
                            Some(kind) => kind,
                            // if it wasn't an intrinsic, fall back to `ins_` syntax
                            None => self.raise_raw_ins(&compressed_instr, args)?,
                        }));
                        remaining_instrs = &remaining_instrs[compressed_instr.num_instrs_compressed()..];
                        continue 'instr;
                    },
                    Err(RaiseIntrinsicError::MustDecompress) => {
                        // Do NOT emit this as an `ins_`.
                        // Fall through out of this 'if' block to the no-diff-switch logic.
                    },
                    Err(RaiseIntrinsicError::Error(e)) => return Err(e),
                }
            }
            // Compressing didn't work out then (no diff switches).
            let instr_1 = CompressedInstr::from_single(&remaining_instrs[0]);
            label_gen.emit_labels_for_instr(&mut out, &instr_1);

            // Was it a blob?
            let args_1 = match &instr_1.args {
                RaiseArgs::Unknown(blob_data) => {
                    let kind = raise_unknown_instr(self.hooks.language(), &instr_1, blob_data)?;
                    out.push(self.make_stmt(instr_1.difficulty_mask, kind));
                    remaining_instrs = &remaining_instrs[1..];
                    continue;
                },
                RaiseArgs::Decoded(args) => args,
            };

            // Is it a two-instruction intrinsic?
            // Both instructions must have known signatures...
            if remaining_instrs.len() > 1 {
                let instr_2 = CompressedInstr::from_single(&remaining_instrs[1]);
                if let RaiseArgs::Decoded(args_2) = &instr_2.args {
                    if !label_gen.would_emit_labels(&instr_2) && instr_1.difficulty_mask == instr_2.difficulty_mask {
                        if let Some(kind) = self.try_raise_double_instr_intrinsic(&instr_1, &instr_2, args_1, args_2)? {
                            // Success! It's a two-instruction intrinsic.
                            out.push(self.make_stmt(instr_1.difficulty_mask, kind));
                            remaining_instrs = &remaining_instrs[2..];
                            continue;
                        }
                    }
                }
            }

            match self.try_raise_single_instr_intrinsic(&instr_1, args_1) {
                Ok(raised_intrinsic) => {
                    out.push(self.make_stmt(instr_1.difficulty_mask, match raised_intrinsic {
                        Some(kind) => kind,
                        None => self.raise_raw_ins(&instr_1, args_1)?,
                    }));
                    remaining_instrs = &remaining_instrs[1..];
                    continue 'instr;
                },
                Err(RaiseIntrinsicError::MustDecompress) => unreachable!(),
                Err(RaiseIntrinsicError::Error(e)) => return Err(e),
            }
        }

        // possible label after last instruction
        let end_time = label_gen.prev_time;
        label_gen.emit_labels(&mut out, self.end_offset, end_time);

        Ok(out)
    }

    fn make_stmt(&self, difficulty_mask: raw::DifficultyMask, kind: ast::StmtKind) -> Sp<ast::Stmt> {
        sp!(ast::Stmt {
            node_id: None,
            diff_label: self.make_diff_label(difficulty_mask),
            kind,
        })
    }

    fn make_diff_label(&self, mask_byte: raw::DifficultyMask) -> Option<Sp<ast::DiffLabel>> {
        match mask_byte {
            // save some work by suppressing redundant labels now.
            // (this pass generates a flat list so the "outer"/natural difficulty is always 0xFF)
            DEFAULT_DIFFICULTY_MASK_BYTE => None,
            mask_byte => {
                let mask = BitSet32::from_mask(mask_byte as _);
                Some(sp!(ast::DiffLabel {
                    mask: Some(mask),
                    string: sp!(self.diff_flag_names.mask_to_diff_label(mask)),
                }))
            },
        }
    }
}

// =============================================================================
// Label-generating pass

#[derive(Debug, Clone, PartialEq)]
struct Label {
    time_label: raw::Time,
    label: Ident
}

struct JumpData {
    /// For each offset that has at least one jump to it, all of the time arguments for those jumps.
    all_offset_args: BTreeMap<raw::BytePos, BTreeSet<Option<raw::Time>>>,
}

fn gather_instr_offsets(
    script: &[RawInstr],
    hooks: &dyn LanguageHooks,
) -> Vec<u64> {
    let mut out = vec![0];
    let mut offset = 0;

    let instr_format = hooks.instr_format();
    for instr in script {
        offset += instr_format.instr_size(instr) as u64;
        out.push(offset);
    }
    out
}

fn gather_jump_time_args(
    script: &[RaiseInstr],
    defs: &context::Defs,
    hooks: &dyn LanguageHooks,
) -> Result<JumpData, ErrorReported> {
    let mut all_offset_args = BTreeMap::<u64, BTreeSet<Option<i32>>>::new();

    for instr in script {
        if let Some((jump_offset, jump_time)) = extract_jump_args_by_signature(hooks, instr, defs) {
            all_offset_args.entry(jump_offset).or_default().insert(jump_time);
        }
    }

    Ok(JumpData { all_offset_args })
}

/// Maps offsets to their labels.
type OffsetLabels = BTreeMap<raw::BytePos, Label>;

fn generate_offset_labels(
    emitter: &impl Emitter,
    script: &[RaiseInstr],
    instr_offsets: &[raw::BytePos],
    jump_data: &JumpData,
) -> Result<OffsetLabels, ErrorReported> {
    let mut offset_labels = BTreeMap::new();
    for (&offset, time_args) in &jump_data.all_offset_args {
        let dest_index = {
            instr_offsets.binary_search(&offset)
                .map_err(|_| emitter.emit(error!("an instruction has a bad jump offset!")))?
        };
        // Find out the time range between this instruction and the previous one
        // (the or_else triggers when dest_index == script.len() (label after last instruction))
        let dest_time = script.get(dest_index).unwrap_or_else(|| script.last().unwrap()).time;
        let next = (instr_offsets[dest_index], dest_time);
        let prev = match dest_index {
            0 => (0, 0), // scripts implicitly start at time 0.  (test 'time_loop_at_beginning_of_script')
            i => (instr_offsets[i - 1], script[i - 1].time),
        };
        offset_labels.insert(offset, generate_label_at_offset(prev, next, time_args));
    }
    Ok(offset_labels)
}

/// Given all of the different time args used when jumping to `next_offset`,
/// determine what to call the label at this offset (and what time label to give it).
fn generate_label_at_offset(
    (prev_offset, prev_time): (raw::BytePos, raw::Time),
    (next_offset, next_time): (raw::BytePos, raw::Time),
    time_args: &BTreeSet<Option<raw::Time>>,
) -> Label {
    let time_args = time_args.iter().map(|&x| x.unwrap_or(next_time)).collect::<BTreeSet<_>>();

    // If the only time used with this label is the time of the previous instruction
    // (which is less than this instruction), put the label before the relative time increase.
    if prev_time < next_time && time_args.len() == 1 && time_args.iter().next().unwrap() == &prev_time {
        return Label { label: format!("label_{}r", prev_offset).parse().unwrap(), time_label: prev_time };
    }
    Label { label: format!("label_{}", next_offset).parse().unwrap(), time_label: next_time }
}

#[test]
fn test_generate_label_at_offset() {
    let check = generate_label_at_offset;
    let set = |times: &[Option<i32>]| times.iter().copied().collect();
    let label = |str: &str, time_label: i32| Label { label: str.parse().unwrap(), time_label };

    assert_eq!(check((0, 0), (0, 10), &set(&[Some(10)])), (label("label_0", 10)));
    assert_eq!(check((100, 10), (116, 20), &set(&[Some(20)])), (label("label_116", 20)));
    assert_eq!(check((100, 10), (116, 20), &set(&[None])), (label("label_116", 20)));
    // make sure label doesn't get 'r' label if two instructions have equal times
    assert_eq!(check((100, 10), (116, 10), &set(&[Some(10)])), (label("label_116", 10)));
    // time label decrease means no 'r' label
    assert_eq!(check((100, 20), (116, 10), &set(&[Some(20)])), (label("label_116", 10)));
    // multiple different time args means no 'r' label
    assert_eq!(check((100, 10), (116, 20), &set(&[Some(10), Some(20)])), (label("label_116", 20)));
    assert_eq!(check((100, 10), (116, 20), &set(&[Some(10), Some(16)])), (label("label_116", 20)));

    // the case where an r label is created
    assert_eq!(check((100, 10), (116, 20), &set(&[Some(10)])), (label("label_100r", 10)));
}

fn extract_jump_args_by_signature(
    hooks: &dyn LanguageHooks,
    instr: &RaiseInstr,
    defs: &context::Defs,
) -> Option<(raw::BytePos, Option<raw::Time>)> {
    let mut jump_offset = None;
    let mut jump_time = None;

    let args = match &instr.args {
        RaiseArgs::Decoded(args) => args,
        RaiseArgs::Unknown(_) => return None,
    };

    let (abi, _) = defs.ins_abi(hooks.language(), instr.opcode).expect("decoded, so abi is known");
    for (arg, encoding) in zip!(args, abi.arg_encodings()) {
        match encoding {
            ArgEncoding::JumpOffset
                => jump_offset = Some(hooks.decode_label(instr.offset, arg.expect_immediate_int() as u32)),
            ArgEncoding::JumpTime
                => jump_time = Some(arg.expect_immediate_int()),
            _ => {},
        }
    }

    jump_offset.map(|offset| (offset, jump_time))
}

// =============================================================================

/// Diff-switch detection pass
///
/// This is where we turn a series of instructions with different difficulty flags into
/// something like `ins_10(4:4:5:6);`
///
/// Doing this on the AST is a nigh-intractable problem, so it is done at the instruction level
/// during raising. Series of instructions that look like diff switches are eagerly compressed.
/// If this compression later causes an issue, the compressed instruction can be ignored
/// and multiple instructions can be decoded as a fallback.

// try compressing instrs beginning at the beginning of a slice into a diff switch
fn try_compress_instr(
    instrs: &[RaiseInstr<SimpleArg>],
    // for looking up whether an offset is jumped to from anywhere
    mut has_label: impl FnMut(raw::BytePos) -> bool,
) -> Option<CompressedInstr> {
    // early checks to avoid allocations in cases where there's clearly no diff switch
    if instrs.len() < 2 || instrs[0].opcode != instrs[1].opcode || instrs[0].time != instrs[1].time
        || instrs[0].difficulty_mask == DEFAULT_DIFFICULTY_MASK_BYTE
    {
        return None;
    }

    let first_args = match &instrs[0].args {
        RaiseArgs::Decoded(args) => args,
        RaiseArgs::Unknown(_) => return None,
    };

    // collect instructions at the beginning of the slice that resemble the first instruction,
    // and have disjoint difficulty masks spanning a range of contiguous bits starting at 0
    let mut next_difficulty = 0;
    let mut args_by_index = vec![vec![]; first_args.len()];  // [arg_index] -> [instr_index] -> arg
    let mut offsets = vec![];
    let mut explicit_difficulties = BitSet32::new();
    for instr in instrs {

        // do a full destructure to remind us to update this when adding a new field
        let &RaiseInstr {
            opcode: this_opcode, time: this_time,
            args: ref this_args, difficulty_mask: this_mask,
            offset: this_offset,
        } = instr;
        let this_mask = BitSet32::from_mask(this_mask as _);

        // check for any "combo breakers"
        if this_opcode != instrs[0].opcode || this_time != instrs[0].time {
            break;
        }
        let this_args = match this_args {
            RaiseArgs::Decoded(args) if args.len() == first_args.len() => args,
            _ => break,
        };
        if this_mask == DEFAULT_DIFFICULTY_MASK {
            break;
        }
        // don't allow any "holes" in the difficulties
        if !(this_mask.first() == Some(next_difficulty) && bitmask_bits_are_contiguous(this_mask)) {
            break;
        }

        explicit_difficulties.insert(next_difficulty);
        next_difficulty += this_mask.len() as u32;
        offsets.push(this_offset);
        for (arg_index, arg) in this_args.iter().enumerate() {
            args_by_index[arg_index].push(arg);
        }
    }
    let diff_meta = ds_util::DiffSwitchMeta {
        explicit_difficulties,
        num_difficulties: next_difficulty as _,
    };

    let num_instrs_compressed = offsets.len();
    if num_instrs_compressed < 2 {
        return None;  // one case does not a diff switch make!
    }
    // FIXME: maybe this is overzealous
    if diff_meta.num_difficulties < 4 {  // check we have values up to at least Lunatic
        return None;
    }

    // We can't compress if there exists a jump somewhere into the middle of it!
    if offsets[1..].iter().any(|&offset| has_label(offset)) {
        return None;
    }

    // now make each individual arg into a diff switch if necessary
    let compressed_args = args_by_index.into_iter().map(|explicit_cases| {
        if explicit_cases.iter().all(|case| case == &explicit_cases[0]) {
            CompressedArg::Single(explicit_cases[0].clone())
        } else {
            let cases = diff_meta.switch_from_explicit_cases(explicit_cases.into_iter().cloned());
            CompressedArg::DiffSwitch(cases)
        }
    }).collect::<Vec<_>>();

    // this catches garbage like:
    //
    //   difficulty[1]:  ins_10(30);
    //   difficulty[2]:  ins_10(30);
    //   difficulty[4]:  ins_10(30);
    //   difficulty[8]:  ins_10(30);
    //
    // where the file contains variants for each difficulty but they're all identical
    if !compressed_args.iter().any(|arg| matches!(arg, CompressedArg::DiffSwitch(_))) {
        return None;
    }

    Some(RaiseInstr {
        opcode: instrs[0].opcode, time: instrs[0].time,
        args: RaiseArgs::Decoded(compressed_args),
        difficulty_mask: DEFAULT_DIFFICULTY_MASK_BYTE,
        offset: diff_meta.switch_from_explicit_cases(offsets),
    })
}

fn bitmask_bits_are_contiguous(mask: BitSet32) -> bool {
    assert!(!mask.is_empty());
    mask.last().unwrap() + 1 - mask.first().unwrap() == mask.len() as u32
}

impl CompressedInstr {
    fn num_instrs_compressed(&self) -> usize { self.offset.iter().filter(|x| x.is_some()).count() }

    fn from_single(instr: &RaiseInstr) -> Self {
        let &RaiseInstr { offset, time, difficulty_mask, opcode, ref args } = instr;
        RaiseInstr {
            time, difficulty_mask, opcode,
            offset: vec![Some(offset)],
            args: match args {
                RaiseArgs::Decoded(args) => RaiseArgs::Decoded({
                    args.iter().map(|arg| CompressedArg::Single(arg.clone())).collect()
                }),
                RaiseArgs::Unknown(blob) => RaiseArgs::Unknown(blob.clone()),
            }
        }
    }
}

// =============================================================================

macro_rules! ensure {
    ($emitter:ident, $cond:expr, $($arg:tt)+) => {
        if !$cond { return Err($emitter.emit(error!($($arg)+))); }
    };
}
macro_rules! warn_unless {
    ($emitter:ident, $cond:expr, $($arg:tt)+) => {
        if !$cond { $emitter.emit(warning!($($arg)+)).ignore(); }
    };
}

fn raise_unknown_instr(
    language: LanguageKey,
    instr: &CompressedInstr,
    args: &UnknownArgsData,
) -> Result<ast::StmtKind, ErrorReported> {
    let mut pseudos = vec![];
    if args.param_mask != 0 {
        pseudos.push(sp!(ast::PseudoArg {
            at_sign: sp!(()), eq_sign: sp!(()),
            kind: sp!(token![mask]),
            value: sp!(ast::Expr::LitInt { value: args.param_mask as i32, radix: ast::IntRadix::Bin }),
        }));
    }

    if let Some(extra_arg) = args.extra_arg {
        pseudos.push(sp!(ast::PseudoArg {
            at_sign: sp!(()), eq_sign: sp!(()),
            kind: sp!(token![arg0]),
            value: sp!((extra_arg as i32).into()),
        }));
    }

    pseudos.push(sp!(ast::PseudoArg {
        at_sign: sp!(()), eq_sign: sp!(()),
        kind: sp!(token![blob]),
        value: sp!(pseudo::format_blob(&args.blob).into()),
    }));

    Ok(ast::StmtKind::Expr(sp!(ast::Expr::Call(ast::ExprCall {
        name: sp!(ast::CallableName::Ins { opcode: instr.opcode, language: Some(language) }),
        pseudos,
        args: vec![],
    }))))
}

enum RaiseIntrinsicError {
    Error(ErrorReported),
    /// A unique kind of error that can be returned when raising an intrinsic with a difficulty switch.
    ///
    /// If the difficulty switch appears in an unsupported location (e.g. an output register for assignment),
    /// then for the sake of static analysis it is preferable to fall back to individual statements for each
    /// difficulty case rather than outputting a raw `ins_` syntax with the switch.
    MustDecompress,
}

impl From<ErrorReported> for RaiseIntrinsicError {
    fn from(e: ErrorReported) -> Self { RaiseIntrinsicError::Error(e) }
}

impl SingleSubRaiser<'_> {
    fn try_raise_single_instr_intrinsic(
        &self,
        instr: &CompressedInstr,
        args: &[CompressedArg],
    ) -> Result<Option<ast::StmtKind>, RaiseIntrinsicError> {
        let abi = self.expect_abi(instr);

        let (kind, abi_info) = match self.intrinsic_instrs.get_intrinsic_and_props(instr.opcode) {
            Some(tuple) => tuple,
            None => return Ok(None), // not an intrinsic!
        };

        let mut parts = self.emitter.as_sized().chain_with(|f| write!(f, "while decompiling a {}", kind.heavy_descr()), |emitter| {
            RaisedIntrinsicParts::from_instr(instr, args, abi, abi_info, emitter, self.hooks, self.offset_labels)
        })?;

        match kind {
            IKind::Jmp => {
                let goto = parts.jump.take().unwrap();
                Ok(Some(stmt_goto!(rec_sp!(Span::NULL => as kind, goto #(goto.destination) #(goto.time)))))
            },


            IKind::AssignOp(op, _ty) => {
                let var = parts.outputs.next().unwrap();
                let value = parts.plain_args.next().unwrap();
                Ok(Some(stmt_assign!(rec_sp!(Span::NULL => as kind, #var #op #value))))
            },


            IKind::BinOp(op, _ty) => {
                let var = parts.outputs.next().unwrap();
                let a = parts.plain_args.next().unwrap();
                let b = parts.plain_args.next().unwrap();
                Ok(Some(stmt_assign!(rec_sp!(Span::NULL => as kind, #var = expr_binop!(#a #op #b)))))
            },


            IKind::UnOp(op, _ty) => {
                let var = parts.outputs.next().unwrap();
                let b = parts.plain_args.next().unwrap();
                Ok(Some(stmt_assign!(rec_sp!(Span::NULL => as kind, #var = expr_unop!(#op #b)))))
            },


            IKind::InterruptLabel => {
                let interrupt = parts.plain_args.next().unwrap();
                let interrupt = sp!(Span::NULL => interrupt.as_const_int().ok_or_else(|| {
                    assert!(matches!(interrupt, ast::Expr::Var { .. }));
                    self.emitter.as_sized().emit(error!("unexpected register in interrupt label"))
                })?);
                Ok(Some(stmt_interrupt!(rec_sp!(Span::NULL => as kind, #interrupt))))
            },


            IKind::CountJmp => {
                let goto = parts.jump.take().unwrap();
                let var = parts.outputs.next().unwrap();
                Ok(Some(stmt_cond_goto!(rec_sp!(Span::NULL =>
                    as kind, if (decvar: #var) goto #(goto.destination) #(goto.time)
                ))))
            },


            IKind::CondJmp(op, _ty) => {
                let goto = parts.jump.take().unwrap();
                let a = parts.plain_args.next().unwrap();
                let b = parts.plain_args.next().unwrap();
                Ok(Some(stmt_cond_goto!(rec_sp!(Span::NULL =>
                    as kind, if expr_binop!(#a #op #b) goto #(goto.destination) #(goto.time)
                ))))
            },


            IKind::CallEosd => {
                let name = parts.sub_id.take().unwrap();
                let int = parts.plain_args.next().unwrap();
                let float = parts.plain_args.next().unwrap();

                Ok(Some(ast::StmtKind::Expr(sp!(ast::Expr::Call(ast::ExprCall {
                    name: sp!(name),
                    pseudos: vec![],
                    // FIXME: If we decompile functions to have different signatures on a per-function
                    //        basis we'll need to adjust the argument order appropriately here
                    args: vec![sp!(int), sp!(float)],
                })))))
            },


            // Individual pieces of multipart intrinsics, which can show up in this method when
            // they appear alone or with e.g. time labels in-between.
            | IKind::CondJmp2A { .. }
            | IKind::CondJmp2B { .. }
            => Ok(None),
        }
    }

    /// Try to raise an intrinsic that is two instructions long.
    fn try_raise_double_instr_intrinsic(
        &self,
        instr_1: &CompressedInstr,
        instr_2: &CompressedInstr,
        args_1: &[CompressedArg],
        args_2: &[CompressedArg],
    ) -> Result<Option<ast::StmtKind>, ErrorReported> {
        assert_eq!(instr_1.time, instr_2.time, "already checked by caller");
        assert_eq!(instr_1.difficulty_mask, instr_2.difficulty_mask, "already checked by caller");

        let abi_1 = self.expect_abi(instr_1);
        let abi_2 = self.expect_abi(instr_2);

        match self.intrinsic_instrs.get_intrinsic_and_props(instr_1.opcode) {
            Some((IKind::CondJmp2A(_), abi_info_1)) => match self.intrinsic_instrs.get_intrinsic_and_props(instr_2.opcode) {
                Some((IKind::CondJmp2B(op), abi_info_2)) => {
                    self.emitter.as_sized().chain("while decompiling a two-step conditional jump", |emitter| {
                        let raise_parts = |instr, args, abi, abi_info| {
                            RaisedIntrinsicParts::from_instr(instr, args, abi, abi_info, emitter, self.hooks, self.offset_labels)
                        };
                        // FIXME needstest (diff switch)
                        let mut cmp_parts = match raise_parts(instr_1, args_1, abi_1, abi_info_1) {
                            Ok(parts) => parts,
                            Err(RaiseIntrinsicError::MustDecompress) => return Ok(None),
                            Err(RaiseIntrinsicError::Error(e)) => return Err(e),
                        };
                        // FIXME needstest (diff switch)
                        let mut jmp_parts = match raise_parts(instr_2, args_2, abi_2, abi_info_2) {
                            Ok(parts) => parts,
                            Err(RaiseIntrinsicError::MustDecompress) => return Ok(None),
                            Err(RaiseIntrinsicError::Error(e)) => return Err(e),
                        };

                        let a = cmp_parts.plain_args.next().unwrap();
                        let b = cmp_parts.plain_args.next().unwrap();
                        let goto = jmp_parts.jump.take().unwrap();
                        Ok(Some(stmt_cond_goto!(rec_sp!(Span::NULL =>
                            as kind, if expr_binop!(#a #op #b) goto #(goto.destination) #(goto.time)
                        ))))
                    })
                },
                _ => Ok(None),
            },
            _ => Ok(None),
        }
    }

    /// Raise an instr to raw `ins_` syntax, with decoded args.
    fn raise_raw_ins(
        &self,
        instr: &CompressedInstr,
        args: &[CompressedArg],  // args decoded from the blob
    ) -> Result<ast::StmtKind, ErrorReported> {
        let language = self.hooks.language();
        let abi = self.expect_abi(instr);
        let encodings = abi.arg_encodings().collect::<Vec<_>>();

        if args.len() != encodings.len() {
            return Err(self.emitter.as_sized().emit(error!(
                "provided arg count ({}) does not match mapfile ({})", args.len(), encodings.len(),
            )));
        }

        // in case this is a jump that didn't decompile to an intrinsic, scan ahead for an offset arg
        // so we can use this info when decompiling the time arg.
        let dest_label = {
            encodings.iter().zip(args)
                .find(|(&enc, _)| enc == ArgEncoding::JumpOffset)
                .map(|(_, offset_compressed_arg)| {
                    // To make matters even worse, the offset might be a diff switch!
                    // We need to decode each case according to its own original instruction's offset.

                    // (we want to make a DiffSwitchVec so iterate over instr.offset which has the desired shape,
                    //  and we'll read off the corresponding case args in parallel)
                    let mut remaining_case_args = offset_compressed_arg.iter_raw_args();
                    let dest_labels = instr.offset.iter().map(|opt| opt.map(|case_instr_offset| {
                        // get the destination label for one explicit difficulty
                        let case_offset_arg = remaining_case_args.next().expect("fewer offset args than instr's own offsets");
                        let case_offset = self.hooks.decode_label(case_instr_offset, case_offset_arg.expect_int() as u32);
                        self.offset_labels.get(&case_offset)
                            .ok_or(IllegalOffset)  // if it was a valid offset, it would have a label
                    })).collect::<DiffSwitchVec<_>>();

                    assert!(remaining_case_args.next().is_none(), "more offset args than instr's own offsets");
                    dest_labels
                })
        };

        let mut raised_args = encodings.iter().zip(args).enumerate().map(|(i, (&enc, arg))| {
            self.emitter.as_sized().chain_with(|f| write!(f, "in argument {}", i + 1), |emitter| {
                Ok(sp!(raise_compressed(language, emitter, &arg, enc, dest_label.as_deref())?))
            })
        }).collect::<Result<Vec<_>, ErrorReported>>()?;

        // Move unused timeline arguments out of the argument list and into a pseudo-arg.
        let mut pseudos = vec![];
        if matches!(encodings.get(0), Some(ArgEncoding::TimelineArg(TimelineArgKind::Unused))) {
            let arg0_expr = raised_args.remove(0);
            if arg0_expr.as_const_int().unwrap() != 0 {
                pseudos.push(sp!(ast::PseudoArg {
                    at_sign: sp!(()), eq_sign: sp!(()),
                    kind: sp!(ast::PseudoArgKind::ExtraArg),
                    value: arg0_expr,
                }))
            }
        }

        // drop early STD padding args from the end as long as they're zero.
        //
        // IMPORTANT: this is looking at the original arg list because the new lengths may differ due to arg0.
        for (enc, arg) in abi.arg_encodings().zip(args).rev() {
            match enc {
                ArgEncoding::Padding if arg.iter_raw_args().all(|raw| matches!(raw, SimpleArg { value: ScalarValue::Int(0), .. })) => {
                    raised_args.pop()
                },
                _ => break,
            };
        }
        Ok(ast::StmtKind::Expr(sp!(ast::Expr::Call(ast::ExprCall {
            name: sp!(ast::CallableName::Ins { opcode: instr.opcode, language: Some(language) }),
            pseudos,
            args: raised_args,
        }))))
    }

    fn expect_abi<T, U>(&self, instr: &RaiseInstr<T, U>) -> &InstrAbi {
        // if we have RaiseInstr then we already used the signature earlier to decode the arg bytes
        self.defs.ins_abi(self.hooks.language(), instr.opcode).unwrap_or_else(|| {
            unreachable!("(BUG!) signature not known for opcode {}, but this should have been caught earlier!", instr.opcode)
        }).0
    }
}

/// Indicates that a jump offset did not point to an instruction.
#[derive(Debug, Clone, Copy)]
struct IllegalOffset;

/// Adapts a [`SimpleArg`]-raising function to raise a [`CompressedArg`] instead.
fn raise_compressed_with<E>(
    arg: &CompressedArg,
    mut raise_raw: impl FnMut(usize, &SimpleArg) -> Result<ast::Expr, E>,
) -> Result<ast::Expr, E> {
    match arg {
        CompressedArg::Single(raw) => raise_raw(0, raw),

        CompressedArg::DiffSwitch(cases) => Ok(ast::Expr::DiffSwitch({
            cases.iter().enumerate().map(|(case_index, case_opt)| {
                case_opt.as_ref().map(|raw| Ok(sp!(raise_raw(case_index, raw)?))).transpose()
            }).collect::<Result<_, E>>()?
        })),
    }
}

fn raise_compressed(
    language: LanguageKey,
    emitter: &impl Emitter,
    arg: &CompressedArg,
    enc: ArgEncoding,
    dest_label: Option<&DiffSwitchSlice<Result<&Label, IllegalOffset>>>,
) -> Result<ast::Expr, ErrorReported> {
    raise_compressed_with(arg, |case_index, raw| {
        let case_dest_label = dest_label.map(|slice| slice[case_index].unwrap());
        raise_arg(language, emitter, raw, enc, case_dest_label)
    })
}

/// General argument-raising routine that supports registers and uses the encoding in the ABI
/// to possibly guide how to express the output. This is what is used for e.g. args in `ins_` syntax.
fn raise_arg(
    language: LanguageKey,
    emitter: &impl Emitter,
    raw: &SimpleArg,
    enc: ArgEncoding,
    dest_label: Option<Result<&Label, IllegalOffset>>,
) -> Result<ast::Expr, ErrorReported> {
    if raw.is_reg {
        Ok(ast::Expr::Var(sp!(raise_arg_to_reg(language, emitter, raw, enc, abi_parts::OutputArgMode::Natural)?)))
    } else {
        raise_arg_to_literal(emitter, raw, enc, dest_label)
    }
}

#[allow(unused)] // FIXME: should be used once jump time can be exprs
fn raise_compressed_to_literal(
    emitter: &impl Emitter,
    arg: &CompressedArg,
    enc: ArgEncoding,
    dest_label: Option<&DiffSwitchSlice<Result<&Label, IllegalOffset>>>,
) -> Result<ast::Expr, ErrorReported> {
    raise_compressed_with(arg, |case_index, raw| {
        let case_dest_label = dest_label.map(|slice| slice[case_index].unwrap());
        raise_arg_to_literal(emitter, raw, enc, case_dest_label)
    })
}

/// Raise an immediate arg, using the encoding to guide the formatting of the output.
fn raise_arg_to_literal(
    emitter: &impl Emitter,
    raw: &SimpleArg,
    enc: ArgEncoding,
    dest_label: Option<Result<&Label, IllegalOffset>>,
) -> Result<ast::Expr, ErrorReported> {
    ensure!(emitter, !raw.is_reg, "expected an immediate, got a register");

    match enc {
        | ArgEncoding::Padding
        | ArgEncoding::Word
        | ArgEncoding::Dword
        | ArgEncoding::TimelineArg(TimelineArgKind::MsgSub)
        | ArgEncoding::TimelineArg(TimelineArgKind::Unused)
        => Ok(ast::Expr::from(raw.expect_int())),

        | ArgEncoding::Sprite
        => match raw.expect_int() {
            -1 => Ok(ast::Expr::from(-1)),
            id => {
                let const_ident = ResIdent::new_null(crate::formats::anm::auto_sprite_name(id as _));
                let name = ast::VarName::new_non_reg(const_ident);
                Ok(ast::Expr::Var(sp!(ast::Var { name, ty_sigil: None })))
            },
        },

        | ArgEncoding::Script
        => {
            let const_ident = ResIdent::new_null(crate::formats::anm::auto_script_name(raw.expect_int() as _));
            let name = ast::VarName::new_non_reg(const_ident);
            Ok(ast::Expr::Var(sp!(ast::Var { name, ty_sigil: None })))
        },

        | ArgEncoding::Sub
        | ArgEncoding::TimelineArg(TimelineArgKind::EclSub)
        => {
            let const_ident = ResIdent::new_null(crate::formats::ecl::auto_sub_name(raw.expect_int() as _));
            let name = ast::VarName::new_non_reg(const_ident);
            Ok(ast::Expr::Var(sp!(ast::Var { name, ty_sigil: None })))
        }

        | ArgEncoding::Color
        => Ok(ast::Expr::LitInt { value: raw.expect_int(), radix: ast::IntRadix::Hex }),

        | ArgEncoding::Float
        => Ok(ast::Expr::from(raw.expect_float())),

        | ArgEncoding::String { .. }
        => Ok(ast::Expr::from(raw.expect_string().clone())),

        | ArgEncoding::JumpTime
        => match dest_label {
            | Some(Ok(Label { time_label, label })) if *time_label == raw.expect_int()
            => Ok(ast::Expr::LabelProperty { label: sp!(label.clone()), keyword: sp!(token![timeof]) }),

            _ => Ok(ast::Expr::from(raw.expect_int())),
        },

        | ArgEncoding::JumpOffset
        => match dest_label.unwrap() {
            | Ok(Label { label, .. })
            => Ok(ast::Expr::LabelProperty { label: sp!(label.clone()), keyword: sp!(token![offsetof]) }),

            | Err(IllegalOffset) => {
                emitter.emit(warning!("invalid offset in a jump instruction")).ignore();
                Ok(ast::Expr::LitInt { value: raw.expect_int(), radix: ast::IntRadix::SignedHex })
            },
        },
    }
}

fn raise_arg_to_reg(
    language: LanguageKey,
    emitter: &impl Emitter,
    raw: &SimpleArg,
    encoding: ArgEncoding,
    // ty: ScalarType,
    // FIXME: feels out of place.  But basically, the only place where the type of the raised
    //        variable can have a different type from its storage is in some intrinsics, yet the logic
    //        for dealing with these is otherwise the same as regs in non-intrinsics.
    storage_mode: abi_parts::OutputArgMode,
) -> Result<ast::Var, ErrorReported> {
    ensure!(emitter, raw.is_reg, "expected a variable, got an immediate");

    let storage_ty_sigil = encoding.expr_type().sigil().expect("(bug!) raise_arg_to_reg used on invalid type");
    let ast_ty_sigil = match storage_mode {
        abi_parts::OutputArgMode::FloatAsInt => ast::VarSigil::Float,
        abi_parts::OutputArgMode::Natural => storage_ty_sigil,
    };
    let reg = match storage_ty_sigil {
        ast::VarSigil::Int => RegId(raw.expect_int()),
        ast::VarSigil::Float => {
            let float_reg = raw.expect_float();
            if float_reg != f32::round(float_reg) {
                return Err(emitter.emit(error!("non-integer float variable %REG[{}] in binary file!", float_reg)));
            }
            RegId(float_reg as i32)
        },
    };
    let name = ast::VarName::Reg { reg, language: Some(language) };
    Ok(ast::Var { ty_sigil: Some(ast_ty_sigil), name })
}

/// Result of raising an intrinsic's arguments.
///
/// The fields correspond to those on [`IntrinsicInstrAbiParts`].
#[derive(Debug)]
struct RaisedIntrinsicParts {
    jump: Option<ast::StmtGoto>,
    sub_id: Option<ast::CallableName>,
    outputs: std::vec::IntoIter<ast::Var>,
    plain_args: std::vec::IntoIter<ast::Expr>,
}

impl RaisedIntrinsicParts {
    fn from_instr(
        instr: &CompressedInstr,
        args: &[CompressedArg],
        abi: &InstrAbi,
        abi_parts: &IntrinsicInstrAbiParts,
        emitter: &impl Emitter,
        hooks: &dyn LanguageHooks,
        offset_labels: &BTreeMap<u64, Label>,
    ) -> Result<Self, RaiseIntrinsicError> {
        let encodings = abi.arg_encodings().collect::<Vec<_>>();
        let IntrinsicInstrAbiParts {
            num_instr_args: _, padding: ref padding_info, outputs: ref outputs_info,
            jump: ref jump_info, plain_args: ref plain_args_info, sub_id: ref sub_id_info,
        } = abi_parts;

        let padding_range = padding_info.index..padding_info.index + padding_info.count;
        warn_unless!(
            emitter,
            args[padding_range].iter().all(|a| a.iter_raw_args().all(|r| !r.is_reg && r.expect_immediate_int() == 0)),
            "unsupported data in padding of intrinsic",
        );

        macro_rules! require_no_diff_switch {
            ($expr:expr) => {
                match $expr {
                    CompressedArg::DiffSwitch(_) => return Err(RaiseIntrinsicError::MustDecompress),
                    CompressedArg::Single(arg) => arg,
                }
            };
        }

        let mut jump = None;
        if let &Some((index, order)) = jump_info {
            let (offset_arg, time_arg) = match order {
                abi_parts::JumpArgOrder::TimeLoc => (&args[index + 1], Some(&args[index])),
                abi_parts::JumpArgOrder::LocTime => (&args[index], Some(&args[index + 1])),
                abi_parts::JumpArgOrder::Loc => (&args[index], None),
            };

            if instr.num_instrs_compressed() > 1 {
                return Err(RaiseIntrinsicError::MustDecompress);
            };
            // we don't allow diff switches for the label so we only need the first offset
            let instr_offset = instr.offset[0].unwrap();

            let label_offset = hooks.decode_label(instr_offset, require_no_diff_switch!(offset_arg).expect_immediate_int() as u32);
            let label = &offset_labels[&label_offset];
            jump = Some(ast::StmtGoto {
                destination: sp!(label.label.clone()),
                time: match time_arg {
                    Some(arg) => {
                        let arg = require_no_diff_switch!(arg);
                        Some(sp!(arg.expect_immediate_int())).filter(|&t| t != label.time_label)
                    },
                    None => None,
                },
            });
        }

        let mut sub_id = None;
        if let &Some(index) = sub_id_info {
            // FIXME: What if the index is invalid?  It'd be nice to fall back to raw instruction syntax...
            let sub_index = require_no_diff_switch!(&args[index]).expect_immediate_int() as _;
            let ident = ResIdent::new_null(crate::ecl::auto_sub_name(sub_index));
            let name = ast::CallableName::Normal { ident, language_if_ins: Some(hooks.language()) };
            sub_id = Some(name);
        }

        let mut outputs = vec![];
        for &(index, mode) in outputs_info {
            let arg = require_no_diff_switch!(&args[index]);
            let var = raise_arg_to_reg(hooks.language(), emitter, arg, encodings[index], mode)?;
            outputs.push(var);
        }

        let mut plain_args = vec![];
        for &index in plain_args_info {
            let dest_label = None;  // offset and time are not plain args so this is irrelevant
            let expr = raise_compressed(hooks.language(), emitter, &args[index], encodings[index], dest_label)?;
            plain_args.push(expr);
        }
        Ok(RaisedIntrinsicParts { jump, sub_id, outputs: outputs.into_iter(), plain_args: plain_args.into_iter() })
    }
}

// =============================================================================

impl Raiser<'_> {
    fn decode_args(&mut self, emitter: &impl Emitter, instr: &RawInstr, instr_offset: raw::BytePos, defs: &Defs) -> Result<RaiseInstr, ErrorReported> {
        if self.options.arguments {
            if let Some((abi, _)) = defs.ins_abi(self.hooks.language(), instr.opcode) {
                return decode_args_with_abi(emitter, self.hooks, instr, instr_offset, abi);
            } else {
                self.opcodes_without_abis.insert(instr.opcode);
            }
        }

        // Fall back to decompiling as a blob.
        Ok(RaiseInstr {
            offset: instr_offset,
            time: instr.time,
            opcode: instr.opcode,
            difficulty_mask: instr.difficulty,
            args: RaiseArgs::Unknown(UnknownArgsData {
                param_mask: instr.param_mask,
                extra_arg: instr.extra_arg,
                blob: instr.args_blob.to_vec(),
            }),
        })
    }
}

fn decode_args_with_abi(
    emitter: &impl Emitter,
    hooks: &dyn LanguageHooks,
    instr: &RawInstr,
    instr_offset: raw::BytePos,
    siggy: &InstrAbi,
) -> Result<RaiseInstr, ErrorReported> {
    use crate::io::BinRead;

    let mut param_mask = instr.param_mask;
    let mut args_blob = std::io::Cursor::new(&instr.args_blob);
    let mut args = vec![];
    let mut remaining_len = instr.args_blob.len();

    fn decrease_len(emitter: &impl Emitter, remaining_len: &mut usize, amount: usize) -> Result<(), ErrorReported> {
        if *remaining_len < amount {
            return Err(emitter.emit(error!("not enough bytes in instruction")));
        }
        *remaining_len -= amount;
        Ok(())
    }

    let reg_style = hooks.register_style();
    for (arg_index, enc) in siggy.arg_encodings().enumerate() {
        let param_mask_bit = param_mask % 2 == 1;
        param_mask /= 2;

        emitter.chain_with(|f| write!(f, "in argument {} of ins_{}", arg_index + 1, instr.opcode), |emitter| {
            let value = match enc {
                | ArgEncoding::Dword
                | ArgEncoding::Color
                | ArgEncoding::JumpOffset
                | ArgEncoding::JumpTime
                | ArgEncoding::Padding
                | ArgEncoding::Sprite
                | ArgEncoding::Script
                | ArgEncoding::Sub
                => {
                    decrease_len(emitter, &mut remaining_len, 4)?;
                    ScalarValue::Int(args_blob.read_u32().expect("already checked len") as i32)
                },

                | ArgEncoding::Float
                => {
                    decrease_len(emitter, &mut remaining_len, 4)?;
                    ScalarValue::Float(f32::from_bits(args_blob.read_u32().expect("already checked len")))
                },

                | ArgEncoding::Word
                => {
                    decrease_len(emitter, &mut remaining_len, 2)?;
                    ScalarValue::Int(args_blob.read_i16().expect("already checked len") as i32)
                },

                | ArgEncoding::String { block_size: _, mask, furibug: _ }
                => {
                    // read to end
                    let read_len = remaining_len;
                    decrease_len(emitter, &mut remaining_len, read_len)?;

                    let mut encoded = Encoded(args_blob.read_byte_vec(read_len).expect("already checked len"));
                    encoded.apply_xor_mask(mask);
                    encoded.trim_first_nul(emitter);

                    let string = encoded.decode(DEFAULT_ENCODING).map_err(|e| emitter.emit(e))?;
                    ScalarValue::String(string)
                },

                | ArgEncoding::TimelineArg { .. }
                => {
                    // a check that non-timeline languages don't have timeline args in their signature
                    // is done earlier so we can unwrap this
                    let extra_arg = instr.extra_arg.expect("timeline arg in sig for non-timeline language");
                    ScalarValue::Int(extra_arg as _)
                },
            };

            let is_reg = match reg_style {
                RegisterEncodingStyle::ByParamMask => param_mask_bit,
                RegisterEncodingStyle::EosdEcl { does_value_look_like_a_register } => {
                    does_value_look_like_a_register(&value)
                },
            };

            args.push(SimpleArg { value, is_reg });
            Ok(())
        })?;
    }

    if args_blob.position() != args_blob.get_ref().len() as u64 {
        emitter.emit(warning!(
            // this could mean the signature is incomplete
            "unexpected leftover bytes in ins_{}! (read {} bytes out of {}!)",
            instr.opcode, args_blob.position(), args_blob.get_ref().len(),
        )).ignore();
    }

    // check that we did enough right-shifts to use every bit
    if param_mask != 0 && matches!(reg_style, RegisterEncodingStyle::ByParamMask) {
        emitter.emit(warning!(
            "unused mask bits in ins_{}! (arg {} is a register, but there are only {} args!)",
            instr.opcode, param_mask.trailing_zeros() + args.len() as u32 + 1, args.len(),
        )).ignore();
    }
    Ok(RaiseInstr {
        offset: instr_offset,
        time: instr.time,
        opcode: instr.opcode,
        difficulty_mask: instr.difficulty,
        args: RaiseArgs::Decoded(args),
    })
}

// =============================================================================

/// Emits time and difficulty labels from an instruction stream.
#[derive(Debug, Clone)]
struct LabelEmitter<'a> {
    prev_time: raw::Time,
    offset_labels: &'a BTreeMap<raw::BytePos, Label>,
    diff_flag_names: &'a DiffFlagNames,
}

impl<'a> LabelEmitter<'a> {
    fn new(offset_labels: &'a BTreeMap<raw::BytePos, Label>, diff_flag_names: &'a DiffFlagNames) -> Self {
        LabelEmitter {
            prev_time: 0,
            offset_labels,
            diff_flag_names,
        }
    }

    fn emit_labels(&mut self, out: &mut Vec<Sp<ast::Stmt>>, offset: raw::BytePos, time: raw::Time) {
        self.emit_labels_with(offset, time, &mut |stmt| out.push(stmt))
    }

    fn emit_labels_for_instr(&mut self, out: &mut Vec<Sp<ast::Stmt>>, instr: &CompressedInstr) {
        self.emit_labels_for_instr_with(instr, &mut |stmt| out.push(stmt))
    }

    /// Determine if the label emitter would emit a label here.
    fn would_emit_labels(&self, instr: &CompressedInstr) -> bool {
        let mut emitted = false;
        let mut temp_emitter = self.clone();
        temp_emitter.emit_labels_for_instr_with(instr, &mut |_| emitted = true);
        emitted
    }

    // -----------------
    // underlying implementation which uses a callback

    fn emit_labels_for_instr_with(&mut self, instr: &CompressedInstr, emit: &mut impl FnMut(Sp<ast::Stmt>)) {
        let offset = instr.offset[0].expect("no easy offset?");
        assert!(
            instr.offset[1..].iter().copied().flatten().all(|offset| !self.offset_labels.contains_key(&offset)),
            "a label got compressed into the middle of a diff switch!!",
        );

        self.emit_labels_with(offset, instr.time, emit);
    }

    fn emit_labels_with(&mut self, offset: raw::BytePos, time: raw::Time, emit: &mut impl FnMut(Sp<ast::Stmt>)) {
        self.emit_offset_and_time_labels_with(offset, time, emit);

        // not statements anymore
        // self.emit_difficulty_labels_with(difficulty, emit);
    }

    // emit both labels like "label_354:" and "+24:"
    fn emit_offset_and_time_labels_with(&mut self, offset: raw::BytePos, time: raw::Time, emit: &mut impl FnMut(Sp<ast::Stmt>)) {
        // labels don't need to worry about difficulty
        let make_stmt = |kind| sp!(ast::Stmt { node_id: None, diff_label: None, kind });

        // in the current implementation there is at most one regular label at this offset, which
        // may be before or after a relative time jump.
        let mut offset_label = self.offset_labels.get(&offset);
        macro_rules! put_offset_label_here_if_it_has_time {
            ($time:expr) => {
                if let Some(label) = &offset_label {
                    if label.time_label == $time {
                        emit(make_stmt(ast::StmtKind::Label(sp!(label.label.clone()))));
                        offset_label = None;
                    }
                }
            };
        }

        put_offset_label_here_if_it_has_time!(self.prev_time);

        // add time labels
        let prev_time = self.prev_time;
        if time != prev_time {
            if prev_time < 0 && 0 <= time {
                // Include an intermediate 0: between negative and positive.
                // This is because ANM scripts can start with instrs at -1: that have special properties.
                emit(make_stmt(ast::StmtKind::AbsTimeLabel(sp!(0))));
                if time > 0 {
                    emit(make_stmt(ast::StmtKind::RelTimeLabel {
                        delta: sp!(time),
                        _absolute_time_comment: Some(time),
                    }));
                }
            } else if time < prev_time {
                emit(make_stmt(ast::StmtKind::AbsTimeLabel(sp!(time))));
            } else if prev_time < time {
                emit(make_stmt(ast::StmtKind::RelTimeLabel {
                    delta: sp!(time - prev_time),
                    _absolute_time_comment: Some(time),
                }));
            }
        }

        put_offset_label_here_if_it_has_time!(time);

        // do we have a label we never placed?
        if let Some(label) = &offset_label {
            panic!("impossible time for label: (times: {} -> {}) {:?}", self.prev_time, time, label);
        }

        self.prev_time = time;
    }
}

// =============================================================================
