use std::collections::{BTreeMap, BTreeSet};

use crate::raw;
use crate::ast::{self, pseudo};
use crate::ident::{Ident, ResIdent};
use crate::pos::{Sp, Span};
use crate::diagnostic::{Emitter};
use crate::error::{ErrorReported};
use crate::llir::{RawInstr, InstrFormat, IntrinsicInstrKind, IntrinsicInstrs, SimpleArg};
use crate::llir::intrinsic::{IntrinsicInstrAbiParts, abi_parts};
use crate::resolve::{RegId, NodeId, UnusedIds};
use crate::context::{self, Defs};
use crate::game::InstrLanguage;
use crate::llir::{ArgEncoding, TimelineArgKind, InstrAbi, RegisterEncodingStyle};
use crate::value::{ScalarValue};
use crate::io::{DEFAULT_ENCODING, Encoded};

use IntrinsicInstrKind as IKind;

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
struct RaiseInstr {
    offset: raw::BytePos,
    time: raw::Time,
    difficulty_mask: raw::DifficultyMask,
    opcode: raw::Opcode,
    args: RaiseArgs,
}

enum RaiseArgs {
    /// The ABI of the instruction was known, so we parsed the argument bytes into arguments.
    Decoded(Vec<SimpleArg>),
    /// The ABI was not known, so we will be emitting pseudo-args like `@blob=`.
    Unknown(UnknownArgsData),
}

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
    instr_format: &'a dyn InstrFormat,
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
        instr_format: &'a dyn InstrFormat,
        emitter: &'a context::RootEmitter,
        defs: &context::Defs,
        options: &'a DecompileOptions,
    ) -> Result<Self, ErrorReported> {
        Ok(Raiser {
            instr_format,
            opcodes_without_abis: Default::default(),
            emitter_for_abi_warnings: emitter,
            // If intrinsic decompilation is disabled, simply pretend that there aren't any intrinsics.
            intrinsic_instrs: match options.intrinsics {
                true => IntrinsicInstrs::from_format_and_mapfiles(instr_format, defs, emitter)?,
                false => Default::default(),
            },
            options,
        })
    }

    pub fn raise_instrs_to_sub_ast(
        &mut self,
        emitter: &dyn Emitter,
        raw_script: &[RawInstr],
        defs: &Defs,
        unused_node_ids: &UnusedIds<NodeId>,
    ) -> Result<Vec<Sp<ast::Stmt>>, ErrorReported> {
        let mut stmts = _raise_instrs_to_sub_ast(self, &emitter, raw_script, defs)?;
        crate::passes::resolution::fill_missing_node_ids(&mut stmts[..], &unused_node_ids)?;
        Ok(stmts)
    }

    pub fn generate_warnings(&mut self) {
        if !self.opcodes_without_abis.is_empty() {
            self.emitter_for_abi_warnings.emit(warning!(
                message("{} instructions with unknown signatures were decompiled to byte blobs.", self.instr_format.language().descr()),
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
    defs: &Defs,
) -> Result<Vec<Sp<ast::Stmt>>, ErrorReported> {
    let instr_format = raiser.instr_format;
    let instr_offsets = gather_instr_offsets(raw_script, instr_format);

    // Preprocess by using mapfile signatures to parse arguments
    let script: Vec<RaiseInstr> = {
        raw_script.iter().zip(&instr_offsets)
            .map(|(raw_instr, &instr_offset)| raiser.decode_args(emitter, raw_instr, instr_offset, defs))
            .collect::<Result<_, _>>()?
    };

    let jump_data = gather_jump_time_args(&script, defs, instr_format)?;
    let offset_labels = generate_offset_labels(emitter, &script, &instr_offsets, &jump_data)?;

    _raise_instrs_main_loop(
        emitter, defs, instr_format, &instr_offsets,
        &script, &offset_labels, &raiser.intrinsic_instrs,
    )
}

fn _raise_instrs_main_loop(
    emitter: &impl Emitter,
    defs: &Defs,
    instr_format: &dyn InstrFormat,
    instr_offsets: &Vec<raw::BytePos>,
    script: &[RaiseInstr],
    offset_labels: &BTreeMap<raw::BytePos, Label>,
    intrinsic_instrs: &IntrinsicInstrs,
) -> Result<Vec<Sp<ast::Stmt>>, ErrorReported> {
    let mut out = vec![];
    let mut label_gen = LabelEmitter::new(offset_labels);
    let mut remaining_instrs = zip!(instr_offsets.iter().copied(), script).peekable();

    while let Some((offset, instr)) = remaining_instrs.next() {
        label_gen.emit_labels(&mut out, offset, instr.time, instr.difficulty_mask);

        let args = match &instr.args {
            RaiseArgs::Unknown(args) => {
                // Unknown signature, fall back to pseudos.
                let kind = raise_unknown_instr(instr_format.language(), instr, args)?;
                out.push(sp!(ast::Stmt { node_id: None, kind }));
                continue;
            },
            RaiseArgs::Decoded(args) => args,
        };

        // Is it a two-instruction intrinsic?
        // Both instructions must have known signatures...
        if let Some(&(next_offset, ref next_instr)) = remaining_instrs.peek() {
            if let RaiseArgs::Decoded(next_args) = &next_instr.args {
                // FIXME don't do this check on every instr, or maybe benchmark?
                if !label_gen.would_emit_labels(next_offset, next_instr.time, next_instr.difficulty_mask) {
                    if let Some(kind) = possibly_raise_long_intrinsic(
                        emitter, instr_format, instr, next_instr,
                        args, next_args, defs, intrinsic_instrs, offset_labels,
                    )? {
                        // Success! It's a two-instruction intrinsic.
                        out.push(sp!(ast::Stmt { node_id: None, kind }));
                        remaining_instrs.next();  // consume second part
                        continue;
                    }
                }
            }
        }

        // We have a single instruction with known signature.
        let kind = raise_single_decoded_instr(
            emitter, instr_format, instr, args, defs,
            &intrinsic_instrs, &offset_labels,
        )?;
        out.push(sp!(ast::Stmt { node_id: None, kind }));
    }

    // possible label after last instruction
    let end_time = label_gen.prev_time;
    let end_difficulty = label_gen.prev_difficulty;
    let &end_offset = instr_offsets.last().expect("n + 1 offsets so there's always at least one");
    label_gen.emit_labels(&mut out, end_offset, end_time, end_difficulty);

    Ok(out)
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
    instr_format: &dyn InstrFormat,
) -> Vec<u64> {
    let mut out = vec![0];
    let mut offset = 0;

    for instr in script {
        offset += instr_format.instr_size(instr) as u64;
        out.push(offset);
    }
    out
}

fn gather_jump_time_args(
    script: &[RaiseInstr],
    defs: &Defs,
    instr_format: &dyn InstrFormat,
) -> Result<JumpData, ErrorReported> {
    let mut all_offset_args = BTreeMap::<u64, BTreeSet<Option<i32>>>::new();

    for instr in script {
        if let Some((jump_offset, jump_time)) = extract_jump_args_by_signature(instr_format, instr, defs) {
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
    instr_format: &dyn InstrFormat,
    instr: &RaiseInstr,
    defs: &Defs,
) -> Option<(raw::BytePos, Option<raw::Time>)> {
    let mut jump_offset = None;
    let mut jump_time = None;

    let args = match &instr.args {
        RaiseArgs::Decoded(args) => args,
        RaiseArgs::Unknown(_) => return None,
    };

    let abi = defs.ins_abi(instr_format.language(), instr.opcode).expect("decoded, so abi is known");
    for (arg, encoding) in zip!(args, abi.arg_encodings()) {
        match encoding {
            ArgEncoding::JumpOffset
                => jump_offset = Some(instr_format.decode_label(instr.offset, arg.expect_immediate_int() as u32)),
            ArgEncoding::JumpTime
                => jump_time = Some(arg.expect_immediate_int()),
            _ => {},
        }
    }

    jump_offset.map(|offset| (offset, jump_time))
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
    language: InstrLanguage,
    instr: &RaiseInstr,
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

    Ok(ast::StmtKind::Expr(sp!(ast::Expr::Call {
        name: sp!(ast::CallableName::Ins { opcode: instr.opcode, language: Some(language) }),
        pseudos,
        args: vec![],
    })))
}

fn raise_single_decoded_instr(
    emitter: &impl Emitter,
    instr_format: &dyn InstrFormat,
    instr: &RaiseInstr,
    args: &[SimpleArg],
    defs: &Defs,
    intrinsic_instrs: &IntrinsicInstrs,
    offset_labels: &OffsetLabels,
) -> Result<ast::StmtKind, ErrorReported> {
    let language = instr_format.language();
    let opcode = instr.opcode;
    let abi = expect_abi(language, instr, defs);

    if let Some((kind, abi_info)) = intrinsic_instrs.get_intrinsic_and_props(opcode) {
        let mut parts = emitter.chain_with(|f| write!(f, "while decompiling a {}", kind.heavy_descr()), |emitter| {
            RaisedIntrinsicParts::from_instr(instr, args, abi, abi_info, emitter, instr_format, offset_labels)
        })?;

        match kind {
            IKind::Jmp => {
                let goto = parts.jump.unwrap();
                return Ok(stmt_goto!(rec_sp!(Span::NULL => as kind, goto #(goto.destination) #(goto.time))));
            },


            IKind::AssignOp(op, _ty) => {
                let value = parts.plain_args.pop().unwrap();
                let var = parts.outputs.pop().unwrap();
                return Ok(stmt_assign!(rec_sp!(Span::NULL => as kind, #var #op #value)));
            },


            IKind::BinOp(op, _ty) => {
                let b = parts.plain_args.pop().unwrap();
                let a = parts.plain_args.pop().unwrap();
                let var = parts.outputs.pop().unwrap();
                return Ok(stmt_assign!(rec_sp!(Span::NULL => as kind, #var = expr_binop!(#a #op #b))));
            },


            IKind::UnOp(op, _ty) => {
                let b = parts.plain_args.pop().unwrap();
                let var = parts.outputs.pop().unwrap();
                return Ok(stmt_assign!(rec_sp!(Span::NULL => as kind, #var = expr_unop!(#op #b))));
            },


            IKind::InterruptLabel => {
                let interrupt = parts.plain_args.pop().unwrap();
                let interrupt = sp!(Span::NULL => interrupt.as_const_int().ok_or_else(|| {
                    assert!(matches!(interrupt, ast::Expr::Var { .. }));
                    emitter.emit(error!("unexpected register in interrupt label"))
                })?);
                return Ok(stmt_interrupt!(rec_sp!(Span::NULL => as kind, #interrupt)));
            },


            IKind::CountJmp => {
                let goto = parts.jump.unwrap();
                let var = parts.outputs.pop().unwrap();
                return Ok(stmt_cond_goto!(rec_sp!(Span::NULL =>
                    as kind, if (decvar: #var) goto #(goto.destination) #(goto.time)
                )));
            },


            IKind::CondJmp(op, _ty) => {
                let goto = parts.jump.unwrap();
                let b = parts.plain_args.pop().unwrap();
                let a = parts.plain_args.pop().unwrap();
                return Ok(stmt_cond_goto!(rec_sp!(Span::NULL =>
                    as kind, if expr_binop!(#a #op #b) goto #(goto.destination) #(goto.time)
                )));
            },


            // Individual pieces of multipart intrinsics, which can show up in this method when
            // they appear alone or with e.g. time labels in-between.
            | IKind::CondJmp2A { .. }
            | IKind::CondJmp2B { .. }
            => {},  // fall out to the default `ins_` emitting behavior
        }
    }

    // Cannot raise as intrinsic.  Raise directly to `ins_*(...)` syntax.
    emitter.chain_with(|f| write!(f, "while decompiling ins_{}", opcode), |emitter| {
        raise_plain_ins(instr_format, emitter, instr, args, defs, offset_labels)
    })
}

/// Raise an intrinsic that is two instructions long.
fn possibly_raise_long_intrinsic(
    emitter: &impl Emitter,
    instr_format: &dyn InstrFormat,
    instr_1: &RaiseInstr,
    instr_2: &RaiseInstr,
    args_1: &[SimpleArg],
    args_2: &[SimpleArg],
    defs: &Defs,
    intrinsic_instrs: &IntrinsicInstrs,
    offset_labels: &OffsetLabels,
) -> Result<Option<ast::StmtKind>, ErrorReported> {
    assert_eq!(instr_1.time, instr_2.time, "already checked by caller");
    assert_eq!(instr_1.difficulty_mask, instr_2.difficulty_mask, "already checked by caller");

    let language = instr_format.language();
    let abi_1 = expect_abi(language, instr_1, defs);
    let abi_2 = expect_abi(language, instr_2, defs);

    match intrinsic_instrs.get_intrinsic_and_props(instr_1.opcode) {
        Some((IKind::CondJmp2A(_), abi_info_1)) => match intrinsic_instrs.get_intrinsic_and_props(instr_2.opcode) {
            Some((IKind::CondJmp2B(op), abi_info_2)) => {
                emitter.chain("while decompiling a two-step conditional jump", |emitter| {
                    let mut cmp_parts = RaisedIntrinsicParts::from_instr(instr_1, args_1, abi_1, abi_info_1, emitter, instr_format, offset_labels)?;
                    let mut jmp_parts = RaisedIntrinsicParts::from_instr(instr_2, args_2, abi_2, abi_info_2, emitter, instr_format, offset_labels)?;

                    let goto = jmp_parts.jump.take().unwrap();
                    let b = cmp_parts.plain_args.pop().unwrap();
                    let a = cmp_parts.plain_args.pop().unwrap();
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

/// Indicates that a jump offset did not point to an instruction.
#[derive(Debug, Clone, Copy)]
struct IllegalOffset;

/// Raise a list of args for `ins_` syntax. (i.e. not intrinsics)
fn raise_plain_ins(
    instr_format: &dyn InstrFormat,
    emitter: &impl Emitter,
    instr: &RaiseInstr,
    args: &[SimpleArg],  // args decoded from the blob
    defs: &context::Defs,
    offset_labels: &OffsetLabels,
) -> Result<ast::StmtKind, ErrorReported> {
    let language = instr_format.language();
    let abi = expect_abi(language, instr, defs);
    let encodings = abi.arg_encodings().collect::<Vec<_>>();

    if args.len() != encodings.len() {
        return Err(emitter.emit(error!("provided arg count ({}) does not match mapfile ({})", args.len(), encodings.len())));
    }

    // in case this is a jump that didn't decompile to an intrinsic, scan ahead for an offset arg
    // so we can use this info when decompiling the time arg.
    let dest_label = {
        encodings.iter().zip(args)
            .find(|(&enc, _)| enc == ArgEncoding::JumpOffset)
            .map(|(_, arg)| {
                let offset = instr_format.decode_label(instr.offset, arg.expect_int() as u32);
                offset_labels.get(&offset)
                    .ok_or(IllegalOffset)  // if it was a valid offset, it would have a label
            })
    };

    let mut raised_args = encodings.iter().zip(args).enumerate().map(|(i, (&enc, arg))| {
        emitter.chain_with(|f| write!(f, "in argument {}", i + 1), |emitter| {
            Ok(sp!(raise_arg(language, emitter, &arg, enc, dest_label)?))
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
        match (enc, arg) {
            (ArgEncoding::Padding, SimpleArg { value: ScalarValue::Int(0), .. }) => raised_args.pop(),
            _ => break,
        };
    }
    Ok(ast::StmtKind::Expr(sp!(ast::Expr::Call {
        name: sp!(ast::CallableName::Ins { opcode: instr.opcode, language: Some(language) }),
        pseudos,
        args: raised_args,
    })))
}

/// General argument-raising routine that supports registers and uses the encoding in the ABI
/// to possibly guide how to express the output. This is what is used for e.g. args in `ins_` syntax.
fn raise_arg(
    language: InstrLanguage,
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
    language: InstrLanguage,
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
struct RaisedIntrinsicParts {
    jump: Option<ast::StmtGoto>,
    outputs: Vec<ast::Var>,
    plain_args: Vec<ast::Expr>,
}

impl RaisedIntrinsicParts {
    fn from_instr(
        instr: &RaiseInstr,
        args: &[SimpleArg],
        abi: &InstrAbi,
        abi_parts: &IntrinsicInstrAbiParts,
        emitter: &impl Emitter,
        instr_format: &dyn InstrFormat,
        offset_labels: &BTreeMap<u64, Label>,
    ) -> Result<Self, ErrorReported> {
        let encodings = abi.arg_encodings().collect::<Vec<_>>();
        let IntrinsicInstrAbiParts {
            num_instr_args: _, padding: ref padding_info, outputs: ref outputs_info,
            jump: ref jump_info, plain_args: ref plain_args_info,
        } = abi_parts;

        let mut out = RaisedIntrinsicParts { jump: None, outputs: vec![], plain_args: vec![] };

        let padding_range = padding_info.index..padding_info.index + padding_info.count;
        warn_unless!(
            emitter,
            args[padding_range].iter().all(|a| !a.is_reg && a.expect_immediate_int() == 0),
            "unsupported data in padding of intrinsic",
        );

        if let &Some((index, order)) = jump_info {
            let (offset_arg, time_arg) = match order {
                abi_parts::JumpArgOrder::TimeLoc => (&args[index + 1], Some(&args[index])),
                abi_parts::JumpArgOrder::LocTime => (&args[index], Some(&args[index + 1])),
                abi_parts::JumpArgOrder::Loc => (&args[index], None),
            };

            let offset = instr_format.decode_label(instr.offset, offset_arg.expect_immediate_int() as u32);
            let label = &offset_labels[&offset];
            out.jump = Some(ast::StmtGoto {
                destination: sp!(label.label.clone()),
                time: time_arg.map(|arg| sp!(arg.expect_immediate_int())).filter(|&t| t != label.time_label),
            });
        }

        for &(index, mode) in outputs_info {
            let var = raise_arg_to_reg(instr_format.language(), emitter, &args[index], encodings[index], mode)?;
            out.outputs.push(var);
        }

        for &index in plain_args_info {
            let dest_label = None;  // offset and time are not plain args so this is irrelevant
            let expr = raise_arg(instr_format.language(), emitter, &args[index], encodings[index], dest_label)?;
            out.plain_args.push(expr);
        }
        Ok(out)
    }
}

// =============================================================================

impl Raiser<'_> {
    fn decode_args(&mut self, emitter: &impl Emitter, instr: &RawInstr, instr_offset: raw::BytePos, defs: &Defs) -> Result<RaiseInstr, ErrorReported> {
        if self.options.arguments {
            if let Some(abi) = defs.ins_abi(self.instr_format.language(), instr.opcode) {
                return decode_args_with_abi(emitter, self.instr_format, instr, instr_offset, abi);
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
    instr_format: &dyn InstrFormat,
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

    let reg_style = instr_format.register_style();
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

fn expect_abi<'a>(language: InstrLanguage, instr: &RaiseInstr, defs: &'a Defs) -> &'a InstrAbi {
    // if we have Instr then we already must have used the signature earlier to decode the arg bytes,
    // so we can just panic
    defs.ins_abi(language, instr.opcode).unwrap_or_else(|| {
        unreachable!("(BUG!) signature not known for opcode {}, but this should have been caught earlier!", instr.opcode)
    })
}

// =============================================================================

/// Emits time and difficulty labels from an instruction stream.
#[derive(Debug, Clone)]
struct LabelEmitter<'a> {
    prev_time: raw::Time,
    prev_difficulty: raw::DifficultyMask,
    offset_labels: &'a BTreeMap<raw::BytePos, Label>,
}

impl<'a> LabelEmitter<'a> {
    fn new(offset_labels: &'a BTreeMap<raw::BytePos, Label>) -> Self {
        LabelEmitter {
            prev_time: 0,
            prev_difficulty: crate::passes::semantics::time_and_difficulty::DEFAULT_DIFFICULTY_MASK,
            offset_labels,
        }
    }

    fn emit_labels(&mut self, out: &mut Vec<Sp<ast::Stmt>>, offset: raw::BytePos, time: raw::Time, difficulty: raw::DifficultyMask) {
        self.emit_difficulty_labels(out, difficulty);
        self.emit_offset_and_time_labels(out, offset, time);
    }

    /// Determine if the label emitter would emit a label here.
    fn would_emit_labels(&self, offset: raw::BytePos, time: raw::Time, difficulty: raw::DifficultyMask) -> bool {
        let mut out = vec![];
        let mut temp_emitter = self.clone();
        temp_emitter.emit_labels(&mut out, offset, time, difficulty);
        !out.is_empty()
    }

    // emit both labels like "label_354:" and "+24:"
    fn emit_offset_and_time_labels(&mut self, out: &mut Vec<Sp<ast::Stmt>>, offset: raw::BytePos, time: raw::Time) {
        // in the current implementation there is at most one regular label at this offset, which
        // may be before or after a relative time jump.
        let mut offset_label = self.offset_labels.get(&offset);
        macro_rules! put_label_here_if_it_has_time {
            ($time:expr) => {
                if let Some(label) = &offset_label {
                    if label.time_label == $time {
                        out.push(rec_sp!(Span::NULL => stmt_label!(#(label.label.clone()))));
                        offset_label = None;
                    }
                }
            };
        }

        put_label_here_if_it_has_time!(self.prev_time);

        // add time labels
        let prev_time = self.prev_time;
        if time != prev_time {
            if prev_time < 0 && 0 <= time {
                // Include an intermediate 0: between negative and positive.
                // This is because ANM scripts can start with instrs at -1: that have special properties.
                out.push(sp!(ast::Stmt { node_id: None, kind: ast::StmtKind::AbsTimeLabel(sp!(0)) }));
                if time > 0 {
                    out.push(sp!(ast::Stmt { node_id: None, kind: ast::StmtKind::RelTimeLabel {
                        delta: sp!(time),
                        _absolute_time_comment: Some(time),
                    }}));
                }
            } else if time < prev_time {
                out.push(sp!(ast::Stmt { node_id: None, kind: ast::StmtKind::AbsTimeLabel(sp!(time)) }));
            } else if prev_time < time {
                out.push(sp!(ast::Stmt { node_id: None, kind: ast::StmtKind::RelTimeLabel {
                    delta: sp!(time - prev_time),
                    _absolute_time_comment: Some(time),
                }}));
            }
        }

        put_label_here_if_it_has_time!(time);

        // do we have a label we never placed?
        if let Some(label) = &offset_label {
            panic!("impossible time for label: (times: {} -> {}) {:?}", self.prev_time, time, label);
        }

        self.prev_time = time;
    }

    fn emit_difficulty_labels(&mut self, out: &mut Vec<Sp<ast::Stmt>>, difficulty: raw::DifficultyMask) {
        if difficulty != self.prev_difficulty {
            out.push(sp!(ast::Stmt { node_id: None, kind: ast::StmtKind::RawDifficultyLabel(sp!(difficulty as _)) }));
        }
        self.prev_difficulty = difficulty;
    }
}
