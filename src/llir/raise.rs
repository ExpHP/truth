use std::collections::{BTreeMap, BTreeSet};

use crate::ast::{self, Expr};
use crate::ident::{Ident, ResIdent};
use crate::pos::{Sp, Span};
use crate::diagnostic::{Emitter};
use crate::error::{ErrorReported};
use crate::llir::{RawInstr, InstrFormat, IntrinsicInstrKind, IntrinsicInstrs, SimpleArg};
use crate::resolve::{RegId};
use crate::context::{self, Defs};
use crate::game::InstrLanguage;
use crate::llir::{ArgEncoding, InstrAbi};
use crate::value::{ScalarValue, ScalarType};
use crate::io::{DEFAULT_ENCODING, Encoded};

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
    time: i32,
    opcode: u16,
    args: RaiseArgs,
}

enum RaiseArgs {
    /// The ABI of the instruction was known, so we parsed the argument bytes into arguments.
    Decoded(Vec<SimpleArg>),
    /// The ABI was not known, so we will be emitting pseudo-args like `@blob=`.
    Unknown(UnknownArgsData),
}

struct UnknownArgsData {
    param_mask: u16,
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
}

impl Drop for Raiser<'_> {
    fn drop(&mut self) {
        self.generate_warnings();
    }
}

impl<'a> Raiser<'a> {
    pub fn new(instr_format: &'a dyn InstrFormat, emitter: &'a context::RootEmitter, options: &'a DecompileOptions) -> Self {
        Raiser {
            instr_format,
            opcodes_without_abis: Default::default(),
            emitter_for_abi_warnings: emitter,
            options,
        }
    }

    pub fn raise_instrs_to_sub_ast(
        &mut self,
        emitter: &dyn Emitter,
        raw_script: &[RawInstr],
        defs: &Defs,
    ) -> Result<Vec<Sp<ast::Stmt>>, ErrorReported> {
        raise_instrs_to_sub_ast(self, &emitter, raw_script, defs)
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

fn raise_instrs_to_sub_ast(
    raiser: &mut Raiser,
    emitter: &impl Emitter,
    raw_script: &[RawInstr],
    defs: &Defs,
) -> Result<Vec<Sp<ast::Stmt>>, ErrorReported> {
    let instr_format = raiser.instr_format;
    let instr_offsets = gather_instr_offsets(raw_script, instr_format);

    let script: Vec<RaiseInstr> = raw_script.iter().map(|raw_instr| raiser.decode_args(emitter, raw_instr, defs)).collect::<Result<_, _>>()?;

    let jump_data = gather_jump_time_args(&script, defs, instr_format)?;
    let offset_labels = generate_offset_labels(emitter, &script, &instr_offsets, &jump_data)?;
    let mut out = vec![sp!(ast::Stmt {
        time: script.get(0).map(|x| x.time).unwrap_or(0),
        body: ast::StmtBody::NoInstruction,
    })];

    // If intrinsic decompilation is disabled, simply pretend that there aren't any intrinsics.
    let intrinsic_instrs = match raiser.options.intrinsics {
        true => instr_format.intrinsic_instrs(),
        false => Default::default(),
    };

    for (&offset, instr) in zip!(&instr_offsets, &script) {
        if let Some(label) = offset_labels.get(&offset) {
            out.push(rec_sp!(Span::NULL => stmt_label!(at #(label.time_label), #(label.label.clone()))));
        }

        let body = raise_instr(emitter, instr_format, instr, defs, &intrinsic_instrs, &offset_labels)?;
        out.push(rec_sp!(Span::NULL => stmt!(at #(instr.time), #body)));
    }

    // possible label after last instruction
    let end_time = out.last().expect("there must be at least the other bookend!").time;
    if let Some(label) = offset_labels.get(instr_offsets.last().expect("n + 1 offsets so there's always at least one")) {
        out.push(rec_sp!(Span::NULL => stmt_label!(at #(label.time_label), #(label.label.clone()))));
    }
    out.push(sp!(ast::Stmt {
        time: end_time,
        body: ast::StmtBody::NoInstruction,
    }));
    Ok(out)
}

// =============================================================================

#[derive(Debug, Clone, PartialEq)]
struct Label {
    time_label: i32,
    label: Ident
}

// Data-gathering pass
struct JumpData {
    /// For each offset that has at least one jump to it, all of the time arguments for those jumps.
    all_offset_args: BTreeMap<u64, BTreeSet<Option<i32>>>,
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

fn generate_offset_labels(
    emitter: &impl Emitter,
    script: &[RaiseInstr],
    instr_offsets: &[u64],
    jump_data: &JumpData,
) -> Result<BTreeMap<u64, Label>, ErrorReported> {
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
            0 => None,
            i => Some((instr_offsets[i - 1], script[i - 1].time)),
        };
        offset_labels.insert(offset, generate_label_at_offset(prev, next, time_args));
    }
    Ok(offset_labels)
}

/// Given all of the different time args used when jumping to `next_offset`,
/// determine what to call the label at this offset (and what time label to give it).
fn generate_label_at_offset(
    prev: Option<(u64, i32)>,  // info about previous instruction, None for first instruction
    (next_offset, next_time): (u64, i32),
    time_args: &BTreeSet<Option<i32>>,
) -> Label {
    let time_args = time_args.iter().map(|&x| x.unwrap_or(next_time)).collect::<BTreeSet<_>>();

    if let Some((prev_offset, prev_time)) = prev {
        // If the only time used with this label is the time of the previous instruction
        // (which is less than this instruction), put the label before the relative time increase.
        if prev_time < next_time && time_args.len() == 1 && time_args.iter().next().unwrap() == &prev_time {
            return Label { label: format!("label_{}r", prev_offset).parse().unwrap(), time_label: prev_time };
        }
    }
    Label { label: format!("label_{}", next_offset).parse().unwrap(), time_label: next_time }
}

#[test]
fn test_generate_label_at_offset() {
    let check = generate_label_at_offset;
    let set = |times: &[Option<i32>]| times.iter().copied().collect();
    let label = |str: &str, time_label: i32| Label { label: str.parse().unwrap(), time_label };

    assert_eq!(check(None, (0, 10), &set(&[Some(10)])), (label("label_0", 10)));
    assert_eq!(check(Some((100, 10)), (116, 20), &set(&[Some(20)])), (label("label_116", 20)));
    assert_eq!(check(Some((100, 10)), (116, 20), &set(&[None])), (label("label_116", 20)));
    // make sure label doesn't get 'r' label if two instructions have equal times
    assert_eq!(check(Some((100, 10)), (116, 10), &set(&[Some(10)])), (label("label_116", 10)));
    // time label decrease means no 'r' label
    assert_eq!(check(Some((100, 20)), (116, 10), &set(&[Some(20)])), (label("label_116", 10)));
    // multiple different time args means no 'r' label
    assert_eq!(check(Some((100, 10)), (116, 20), &set(&[Some(10), Some(20)])), (label("label_116", 20)));
    assert_eq!(check(Some((100, 10)), (116, 20), &set(&[Some(10), Some(16)])), (label("label_116", 20)));

    // the case where an r label is created
    assert_eq!(check(Some((100, 10)), (116, 20), &set(&[Some(10)])), (label("label_100r", 10)));
}

fn extract_jump_args_by_signature(
    instr_format: &dyn InstrFormat,
    instr: &RaiseInstr,
    defs: &Defs,
) -> Option<(u64, Option<i32>)> {
    let mut jump_offset = None;
    let mut jump_time = None;

    let args = match &instr.args {
        RaiseArgs::Decoded(args) => args,
        RaiseArgs::Unknown(_) => return None,
    };

    let abi = defs.ins_abi(instr_format.language(), instr.opcode).expect("decoded, so abi is known");
    for (arg, encoding) in zip!(args, abi.arg_encodings()) {
        match encoding {
            ArgEncoding::JumpOffset => jump_offset = Some(instr_format.decode_label(arg.expect_immediate_int() as u32)),
            ArgEncoding::JumpTime => jump_time = Some(arg.expect_immediate_int()),
            _ => {},
        }
    }

    jump_offset.map(|offset| (offset, jump_time))
}


fn raise_instr(
    emitter: &impl Emitter,
    instr_format: &dyn InstrFormat,
    instr: &RaiseInstr,
    defs: &Defs,
    intrinsic_instrs: &IntrinsicInstrs,
    offset_labels: &BTreeMap<u64, Label>,
) -> Result<ast::StmtBody, ErrorReported> {
    match &instr.args {
        RaiseArgs::Decoded(args) => raise_decoded_instr(emitter, instr_format, instr, args, defs, intrinsic_instrs, offset_labels),
        RaiseArgs::Unknown(args) => raise_unknown_instr(instr_format.language(), instr, args),
    }
}

fn raise_unknown_instr(
    language: InstrLanguage,
    instr: &RaiseInstr,
    args: &UnknownArgsData,
) -> Result<ast::StmtBody, ErrorReported> {
    let mut pseudos = vec![];
    if args.param_mask != 0 {
        pseudos.push(sp!(ast::PseudoArg {
            at_sign: sp!(()), eq_sign: sp!(()),
            kind: sp!(token![mask]),
            value: sp!(ast::Expr::LitInt { value: args.param_mask as i32, radix: ast::IntRadix::Bin }),
        }));
    }

    pseudos.push(sp!(ast::PseudoArg {
        at_sign: sp!(()), eq_sign: sp!(()),
        kind: sp!(token![blob]),
        value: sp!(crate::pseudo::format_blob(&args.blob).into()),
    }));

    Ok(ast::StmtBody::Expr(sp!(Expr::Call {
        name: sp!(ast::CallableName::Ins { opcode: instr.opcode, language: Some(language) }),
        pseudos,
        args: vec![],
    })))
}

fn raise_decoded_instr(
    emitter: &impl Emitter,
    instr_format: &dyn InstrFormat,
    instr: &RaiseInstr,
    args: &[SimpleArg],
    defs: &Defs,
    intrinsic_instrs: &IntrinsicInstrs,
    offset_labels: &BTreeMap<u64, Label>,
) -> Result<ast::StmtBody, ErrorReported> {
    let language = instr_format.language();
    let opcode = instr.opcode;
    let abi = defs.ins_abi(language, instr.opcode).expect("decoded, so abi is known");
    let encodings = abi.arg_encodings().collect::<Vec<_>>();

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

    match intrinsic_instrs.get_intrinsic(opcode) {
        Some(IntrinsicInstrKind::Jmp) => emitter.chain("while decompiling a 'goto' operation", |emitter| {
            let nargs = if instr_format.jump_has_time_arg() { 2 } else { 1 };

            // This one is >= because it exists in early STD where there can be padding args.
            ensure!(emitter, args.len() >= nargs, "expected {} args, got {}", nargs, args.len());
            warn_unless!(emitter, args[nargs..].iter().all(|a| a.expect_int() == 0), "unsupported data in padding of intrinsic");

            let goto = raise_jump_args(&args[0], args.get(1), instr_format, offset_labels);
            Ok(stmt_goto!(rec_sp!(Span::NULL => goto #(goto.destination) #(goto.time))))
        }),


        Some(IntrinsicInstrKind::AssignOp(op, ty)) => emitter.chain_with(|f| write!(f, "while decompiling a '{}' operation", op), |emitter| {
            ensure!(emitter, args.len() == 2, "expected {} args, got {}", 2, args.len());
            let var = raise_arg_to_reg(language, emitter, &args[0], ty)?;
            let value = raise_arg(language, emitter, &args[1], encodings[1])?;

            Ok(stmt_assign!(rec_sp!(Span::NULL => #var #op #value)))
        }),


        Some(IntrinsicInstrKind::Binop(op, ty)) => emitter.chain_with(|f| write!(f, "while decompiling a '{}' operation", op), |emitter| {
            ensure!(emitter, args.len() == 3, "expected {} args, got {}", 3, args.len());
            let var = raise_arg_to_reg(language, emitter, &args[0], ty)?;
            let a = raise_arg(language, emitter, &args[1], encodings[1])?;
            let b = raise_arg(language, emitter, &args[2], encodings[2])?;

            Ok(stmt_assign!(rec_sp!(Span::NULL => #var = expr_binop!(#a #op #b))))
        }),


        Some(IntrinsicInstrKind::Unop(op, ty)) => emitter.chain_with(|f| write!(f, "while decompiling a unary '{}' operation", op), |emitter| {
            ensure!(emitter, args.len() == 2, "expected {} args, got {}", 2, args.len());
            let var = raise_arg_to_reg(language, emitter, &args[0], ty)?;
            let b = raise_arg(language, emitter, &args[1], encodings[1])?;

            Ok(stmt_assign!(rec_sp!(Span::NULL => #var = expr_unop!(#op #b))))
        }),


        Some(IntrinsicInstrKind::InterruptLabel) => emitter.chain("while decompiling an interrupt label", |emitter| {
            // This one is >= because it exists in STD where there can be padding args.
            ensure!(emitter, args.len() >= 1, "expected {} args, got {}", 1, args.len());
            warn_unless!(emitter, args[1..].iter().all(|a| a.expect_int() == 0), "unsupported data in padding of intrinsic");

            Ok(stmt_interrupt!(rec_sp!(Span::NULL => #(args[0].expect_immediate_int()) )))
        }),


        Some(IntrinsicInstrKind::CountJmp) => emitter.chain("while decompiling a decrement jump", |emitter| {
            warn_unless!(emitter, args.len() == 3, "expected {} args, got {}", 3, args.len());
            let var = raise_arg_to_reg(language, emitter, &args[0], ScalarType::Int)?;
            let goto = raise_jump_args(&args[1], Some(&args[2]), instr_format, offset_labels);

            Ok(stmt_cond_goto!(rec_sp!(Span::NULL =>
                if (decvar: #var) goto #(goto.destination) #(goto.time)
            )))
        }),


        Some(IntrinsicInstrKind::CondJmp(op, _)) => emitter.chain("while decompiling a conditional jump", |emitter| {
            warn_unless!(emitter, args.len() == 4, "expected {} args, got {}", 4, args.len());
            let a = raise_arg(language, emitter, &args[0], encodings[0])?;
            let b = raise_arg(language, emitter, &args[1], encodings[1])?;
            let goto = raise_jump_args(&args[2], Some(&args[3]), instr_format, offset_labels);

            Ok(stmt_cond_goto!(rec_sp!(Span::NULL =>
                if expr_binop!(#a #op #b) goto #(goto.destination) #(goto.time)
            )))
        }),


        // Default behavior for general instructions
        None => emitter.chain_with(|f| write!(f, "while decompiling ins_{}", opcode), |emitter| {
            let abi = expect_abi(language, instr, defs);

            Ok(ast::StmtBody::Expr(sp!(Expr::Call {
                name: sp!(ast::CallableName::Ins { opcode, language: Some(language) }),
                pseudos: vec![],
                args: raise_args(language, emitter, args, abi)?,
            })))
        }),
    }
}


fn raise_args(language: InstrLanguage, emitter: &impl Emitter, args: &[SimpleArg], abi: &InstrAbi) -> Result<Vec<Sp<Expr>>, ErrorReported> {
    let encodings = abi.arg_encodings().collect::<Vec<_>>();

    if args.len() != encodings.len() {
        return Err(emitter.emit(error!("provided arg count ({}) does not match mapfile ({})", args.len(), encodings.len())));
    }

    let mut out = encodings.iter().zip(args).enumerate().map(|(i, (&enc, arg))| {
        emitter.chain_with(|f| write!(f, "in argument {}", i + 1), |emitter| {
            Ok(sp!(raise_arg(language, emitter, &arg, enc)?))
        })
    }).collect::<Result<Vec<_>, ErrorReported>>()?;

    // drop early STD padding args from the end as long as they're zero
    for (enc, arg) in abi.arg_encodings().zip(args).rev() {
        match (enc, arg) {
            (ArgEncoding::Padding, SimpleArg { value: ScalarValue::Int(0), .. }) => out.pop(),
            _ => break,
        };
    }
    Ok(out)
}

fn raise_arg(language: InstrLanguage, emitter: &impl Emitter, raw: &SimpleArg, enc: ArgEncoding) -> Result<Expr, ErrorReported> {
    if raw.is_reg {
        let ty = match enc {
            | ArgEncoding::Padding
            | ArgEncoding::Color
            | ArgEncoding::Sprite
            | ArgEncoding::Script
            | ArgEncoding::Dword
            => ScalarType::Int,

            | ArgEncoding::Float
            => ScalarType::Float,

            | ArgEncoding::JumpTime => return Err(emitter.emit(error!("unexpected register used as jump time"))),
            | ArgEncoding::JumpOffset => return Err(emitter.emit(error!("unexpected register used as jump offset"))),
            | ArgEncoding::Word => return Err(emitter.emit(error!("unexpected register used as word-sized argument"))),
            | ArgEncoding::String { .. } => return Err(emitter.emit(error!("unexpected register used as string argument"))),
        };
        Ok(Expr::Var(sp!(raise_arg_to_reg(language, emitter, raw, ty)?)))
    } else {
        raise_arg_to_literal(emitter, raw, enc)
    }
}

fn raise_arg_to_literal(emitter: &impl Emitter, raw: &SimpleArg, enc: ArgEncoding) -> Result<Expr, ErrorReported> {
    if raw.is_reg {
        return Err(emitter.emit(error!("expected an immediate, got a register")));
    }

    match enc {
        | ArgEncoding::Padding
        | ArgEncoding::Word
        | ArgEncoding::Dword
        | ArgEncoding::JumpTime  // NOTE: might eventually want timeof(label)
        => Ok(Expr::from(raw.expect_int())),

        | ArgEncoding::Sprite
        => match raw.expect_int() {
            -1 => Ok(Expr::from(-1)),
            id => Ok(Expr::Var(sp!(ast::Var {
                name: ast::VarName::Normal { ident: ResIdent::new_null(crate::formats::anm::auto_sprite_name(id as _)) },
                ty_sigil: None,
            }))),
        },

        | ArgEncoding::Script
        => Ok(Expr::Var(sp!(ast::Var {
            name: ast::VarName::Normal { ident: ResIdent::new_null(crate::formats::anm::auto_script_name(raw.expect_int() as _)) },
            ty_sigil: None,
        }))),

        | ArgEncoding::Color
        | ArgEncoding::JumpOffset  // NOTE: might eventually want offsetof(label)
        => Ok(Expr::LitInt { value: raw.expect_int(), radix: ast::IntRadix::Hex }),

        | ArgEncoding::Float
        => Ok(Expr::from(raw.expect_float())),

        | ArgEncoding::String { .. }
        => Ok(Expr::from(raw.expect_string().clone())),
    }
}

fn raise_arg_to_reg(language: InstrLanguage, emitter: &impl Emitter, raw: &SimpleArg, ty: ScalarType) -> Result<ast::Var, ErrorReported> {
    if !raw.is_reg {
        return Err(emitter.emit(error!("expected a variable, got an immediate")));
    }
    let ty_sigil = ty.sigil().expect("(bug!) raise_arg_to_reg used on invalid type");
    let reg = match ty_sigil {
        ast::VarSigil::Int => RegId(raw.expect_int()),
        ast::VarSigil::Float => {
            let float_reg = raw.expect_float();
            if float_reg != f32::round(float_reg) {
                return Err(emitter.emit(error!("non-integer float variable [{}] in binary file!", float_reg)));
            }
            RegId(float_reg as i32)
        },
    };
    let name = ast::VarName::Reg { reg, language: Some(language) };
    Ok(ast::Var { ty_sigil: Some(ty_sigil), name })
}

fn raise_jump_args(
    offset_arg: &SimpleArg,
    time_arg: Option<&SimpleArg>,  // None when the instruction signature has no time arg
    instr_format: &dyn InstrFormat,
    offset_labels: &BTreeMap<u64, Label>,
) -> ast::StmtGoto {
    let offset = instr_format.decode_label(offset_arg.expect_immediate_int() as u32);
    let label = &offset_labels[&offset];
    ast::StmtGoto {
        destination: sp!(label.label.clone()),
        time: time_arg.map(|arg| sp!(arg.expect_immediate_int())).filter(|&t| t != label.time_label),
    }
}

// =============================================================================

impl Raiser<'_> {
    fn decode_args(&mut self, emitter: &impl Emitter, instr: &RawInstr, defs: &Defs) -> Result<RaiseInstr, ErrorReported> {
        if self.options.arguments {
            if let Some(abi) = defs.ins_abi(self.instr_format.language(), instr.opcode) {
                return decode_args_with_abi(emitter, instr, abi);
            } else {
                self.opcodes_without_abis.insert(instr.opcode);
            }
        }

        // Fall back to decompiling as a blob.
        Ok(RaiseInstr {
            time: instr.time,
            opcode: instr.opcode,
            args: RaiseArgs::Unknown(UnknownArgsData {
                param_mask: instr.param_mask,
                blob: instr.args_blob.to_vec(),
            }),
        })
    }
}

fn decode_args_with_abi(
    emitter: &impl Emitter,
    instr: &RawInstr,
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

    for (arg_index, enc) in siggy.arg_encodings().enumerate() {
        let is_reg = param_mask % 2 == 1;
        param_mask /= 2;

        let value = emitter.chain_with(|f| write!(f, "in argument {} of ins_{}", arg_index + 1, instr.opcode), |emitter| match enc {
            | ArgEncoding::Dword
            | ArgEncoding::Color
            | ArgEncoding::JumpOffset
            | ArgEncoding::JumpTime
            | ArgEncoding::Padding
            | ArgEncoding::Sprite
            | ArgEncoding::Script
            => {
                decrease_len(emitter, &mut remaining_len, 4)?;
                Ok(ScalarValue::Int(args_blob.read_u32().expect("already checked len") as i32))
            },

            | ArgEncoding::Float
            => {
                decrease_len(emitter, &mut remaining_len, 4)?;
                Ok(ScalarValue::Float(f32::from_bits(args_blob.read_u32().expect("already checked len"))))
            },

            | ArgEncoding::Word
            => {
                decrease_len(emitter, &mut remaining_len, 2)?;
                Ok(ScalarValue::Int(args_blob.read_i16().expect("already checked len") as i32))
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
                Ok(ScalarValue::String(string))
            },
        })?;

        args.push(SimpleArg { value, is_reg })
    }

    if args_blob.position() != args_blob.get_ref().len() as u64 {
        emitter.emit(warning!(
            // this could mean the signature is incomplete
            "unexpected leftover bytes in ins_{}! (read {} bytes out of {}!)",
            instr.opcode, args_blob.position(), args_blob.get_ref().len(),
        )).ignore();
    }

    if param_mask != 0 {
        emitter.emit(warning!(
            "unused mask bits in ins_{}! (arg {} is a register, but there are only {} args!)",
            instr.opcode, param_mask.trailing_zeros() + args.len() as u32 + 1, args.len(),
        )).ignore();
    }
    Ok(RaiseInstr {
        time: instr.time,
        opcode: instr.opcode,
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
