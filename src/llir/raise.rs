use std::collections::{BTreeMap, BTreeSet};

use anyhow::{Context, ensure, bail};

use crate::ast::{self, Expr};
use crate::ident::Ident;
use crate::pos::{Sp, Span};
use crate::error::{group_anyhow, SimpleError};
use crate::llir::{RawInstr, InstrFormat, IntrinsicInstrKind, IntrinsicInstrs, SimpleArg};
use crate::resolve::{RegId};
use crate::type_system::{ArgEncoding, TypeSystem, ScalarType, InstrAbi};
use crate::value::ScalarValue;

/// Intermediate form of an instruction only used during decompilation.
struct RaiseInstr {
    time: i32,
    opcode: u16,
    args: RaiseArgs,
}

enum RaiseArgs {
    /// The ABI of the instruction was known, so we parsed the argument bytes into arguments.
    Decoded(Vec<SimpleArg>),
    /// The ABI was not known, so we will be emitting pseudo-args like `@args=`.
    Unknown(UnknownArgsData),
}

struct UnknownArgsData {
    param_mask: u16,
    blob: Vec<u8>,
}

pub fn raise_instrs_to_sub_ast(
    instr_format: &dyn InstrFormat,
    raw_script: &[RawInstr],
    ty_ctx: &TypeSystem,
) -> Result<Vec<Sp<ast::Stmt>>, SimpleError> {
    let instr_offsets = gather_instr_offsets(raw_script, instr_format);

    let script: Vec<RaiseInstr> = raw_script.iter().map(|raw_instr| decode_args(raw_instr, ty_ctx)).collect::<Result<_, _>>()?;

    let jump_data = gather_jump_time_args(&script, ty_ctx, instr_format)?;
    let offset_labels = generate_offset_labels(&script, &instr_offsets, &jump_data)?;
    let mut out = vec![sp!(ast::Stmt {
        time: script.get(0).map(|x| x.time).unwrap_or(0),
        body: ast::StmtBody::NoInstruction,
    })];

    let intrinsic_instrs = instr_format.intrinsic_instrs();
    for (&offset, instr) in zip!(&instr_offsets, &script) {
        if let Some(label) = offset_labels.get(&offset) {
            out.push(rec_sp!(Span::NULL => stmt_label!(at #(label.time_label), #(label.label.clone()))));
        }

        let body = raise_instr(instr_format, instr, ty_ctx, &intrinsic_instrs, &offset_labels)?;
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
    ty_ctx: &TypeSystem,
    instr_format: &dyn InstrFormat,
) -> Result<JumpData, SimpleError> {
    let mut all_offset_args = BTreeMap::<u64, BTreeSet<Option<i32>>>::new();

    for instr in script {
        if let Some((jump_offset, jump_time)) = extract_jump_args_by_signature(instr_format, instr, ty_ctx) {
            all_offset_args.entry(jump_offset).or_default().insert(jump_time);
        }
    }

    Ok(JumpData { all_offset_args })
}

fn generate_offset_labels(
    script: &[RaiseInstr],
    instr_offsets: &[u64],
    jump_data: &JumpData,
) -> Result<BTreeMap<u64, Label>, SimpleError> {
    let mut offset_labels = BTreeMap::new();
    for (&offset, time_args) in &jump_data.all_offset_args {
        let dest_index = {
            instr_offsets.binary_search(&offset)
                .map_err(|_| anyhow::anyhow!("an instruction has a bad jump offset!"))?
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
    ty_ctx: &TypeSystem,
) -> Option<(u64, Option<i32>)> {
    let mut jump_offset = None;
    let mut jump_time = None;

    let args = match &instr.args {
        RaiseArgs::Decoded(args) => args,
        RaiseArgs::Unknown(_) => return None,
    };

    let abi = ty_ctx.ins_abi(instr.opcode).expect("decoded, so abi is known");
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
    instr_format: &dyn InstrFormat,
    instr: &RaiseInstr,
    ty_ctx: &TypeSystem,
    intrinsic_instrs: &IntrinsicInstrs,
    offset_labels: &BTreeMap<u64, Label>,
) -> Result<ast::StmtBody, SimpleError> {
    match &instr.args {
        RaiseArgs::Decoded(args) => raise_decoded_instr(instr_format, instr, args, ty_ctx, intrinsic_instrs, offset_labels),
        RaiseArgs::Unknown(args) => raise_unknown_instr(instr, args),
    }
}

fn raise_unknown_instr(
    instr: &RaiseInstr,
    args: &UnknownArgsData,
) -> Result<ast::StmtBody, SimpleError> {
    let mut pseudos = vec![];
    if args.param_mask != 0 {
        pseudos.push(sp!(ast::PseudoArg {
            at_sign: sp!(()), eq_sign: sp!(()),
            kind: sp!(ast::PseudoArgKind::Mask),
            value: sp!(ast::Expr::LitInt { value: args.param_mask as i32, radix: ast::IntRadix::Bin }),
        }));
    }

    pseudos.push(sp!(ast::PseudoArg {
        at_sign: sp!(()), eq_sign: sp!(()),
        kind: sp!(ast::PseudoArgKind::Args),
        value: sp!(crate::pseudo::format_blob(&args.blob).into()),
    }));

    Ok(ast::StmtBody::Expr(sp!(Expr::Call {
        name: sp!(ast::CallableName::Ins { opcode: instr.opcode }),
        pseudos,
        args: vec![],
    })))
}

fn raise_decoded_instr(
    instr_format: &dyn InstrFormat,
    instr: &RaiseInstr,
    args: &[SimpleArg],
    ty_ctx: &TypeSystem,
    intrinsic_instrs: &IntrinsicInstrs,
    offset_labels: &BTreeMap<u64, Label>,
) -> Result<ast::StmtBody, SimpleError> {
    let opcode = instr.opcode;
    let abi = ty_ctx.ins_abi(instr.opcode).expect("decoded, so abi is known");
    let encodings = abi.arg_encodings().collect::<Vec<_>>();

    match intrinsic_instrs.get_intrinsic(opcode) {
        Some(IntrinsicInstrKind::Jmp) => group_anyhow(|| {
            let nargs = if instr_format.jump_has_time_arg() { 2 } else { 1 };

            // This one is >= because it exists in early STD where there can be padding args.
            ensure!(args.len() >= nargs, "expected {} args, got {}", nargs, args.len());
            ensure!(args[nargs..].iter().all(|a| a.expect_int() == 0), "unsupported data in padding of intrinsic");

            let goto = raise_jump_args(&args[0], args.get(1), instr_format, offset_labels);
            Ok(stmt_goto!(rec_sp!(Span::NULL => goto #(goto.destination) #(goto.time))))
        }).with_context(|| format!("while decompiling a 'goto' operation")),


        Some(IntrinsicInstrKind::AssignOp(op, ty)) => group_anyhow(|| {
            ensure!(args.len() == 2, "expected {} args, got {}", 2, args.len());
            let var = raise_arg_to_reg(&args[0], ty)?;
            let value = raise_arg(&args[1], encodings[1])?;

            Ok(stmt_assign!(rec_sp!(Span::NULL => #var #op #value)))
        }).with_context(|| format!("while decompiling a '{}' operation", op)),


        Some(IntrinsicInstrKind::Binop(op, ty)) => group_anyhow(|| {
            ensure!(args.len() == 3, "expected {} args, got {}", 3, args.len());
            let var = raise_arg_to_reg(&args[0], ty)?;
            let a = raise_arg(&args[1], encodings[1])?;
            let b = raise_arg(&args[2], encodings[2])?;

            Ok(stmt_assign!(rec_sp!(Span::NULL => #var = expr_binop!(#a #op #b))))
        }).with_context(|| format!("while decompiling a '{}' operation", op)),


        Some(IntrinsicInstrKind::Unop(op, ty)) => group_anyhow(|| {
            ensure!(args.len() == 2, "expected {} args, got {}", 2, args.len());
            let var = raise_arg_to_reg(&args[0], ty)?;
            let b = raise_arg(&args[1], encodings[1])?;

            Ok(stmt_assign!(rec_sp!(Span::NULL => #var = expr_unop!(#op #b))))
        }).with_context(|| format!("while decompiling a unary '{}' operation", op)),


        Some(IntrinsicInstrKind::InterruptLabel) => group_anyhow(|| {
            // This one is >= because it exists in STD where there can be padding args.
            ensure!(args.len() >= 1, "expected {} args, got {}", 1, args.len());
            ensure!(args[1..].iter().all(|a| a.expect_int() == 0), "unsupported data in padding of intrinsic");

            Ok(stmt_interrupt!(rec_sp!(Span::NULL => #(args[0].expect_immediate_int()) )))
        }).with_context(|| format!("while decompiling an interrupt label")),


        Some(IntrinsicInstrKind::CountJmp) => group_anyhow(|| {
            ensure!(args.len() == 3, "expected {} args, got {}", 3, args.len());
            let var = raise_arg_to_reg(&args[0], ScalarType::Int)?;
            let goto = raise_jump_args(&args[1], Some(&args[2]), instr_format, offset_labels);

            Ok(stmt_cond_goto!(rec_sp!(Span::NULL =>
                if (decvar: #var) goto #(goto.destination) #(goto.time)
            )))
        }).with_context(|| format!("while decompiling a decrement jump")),


        Some(IntrinsicInstrKind::CondJmp(op, _)) => group_anyhow(|| {
            ensure!(args.len() == 4, "expected {} args, got {}", 4, args.len());
            let a = raise_arg(&args[0], encodings[0])?;
            let b = raise_arg(&args[1], encodings[1])?;
            let goto = raise_jump_args(&args[2], Some(&args[3]), instr_format, offset_labels);

            Ok(stmt_cond_goto!(rec_sp!(Span::NULL =>
                if expr_binop!(#a #op #b) goto #(goto.destination) #(goto.time)
            )))
        }).with_context(|| format!("while decompiling a conditional jump")),


        // Default behavior for general instructions
        None => group_anyhow(|| {
            let abi = expect_abi(instr, ty_ctx);

            Ok(ast::StmtBody::Expr(sp!(Expr::Call {
                name: sp!(ast::CallableName::Ins { opcode }),
                pseudos: vec![],
                args: raise_args(args, abi)?,
            })))
        }).with_context(|| format!("while decompiling ins_{}", opcode)),
    }
}


fn raise_args(args: &[SimpleArg], abi: &InstrAbi) -> Result<Vec<Sp<Expr>>, SimpleError> {
    let encodings = abi.arg_encodings().collect::<Vec<_>>();

    if args.len() != encodings.len() {
        bail!("provided arg count ({}) does not match mapfile ({})", args.len(), encodings.len());
    }

    let mut out = encodings.iter().zip(args).enumerate().map(|(i, (&enc, arg))| {
        let arg_ast = raise_arg(&arg, enc).with_context(|| format!("in argument {}", i + 1))?;
        Ok(sp!(arg_ast))
    }).collect::<Result<Vec<_>, SimpleError>>()?;

    // drop early STD padding args from the end as long as they're zero
    for (enc, arg) in abi.arg_encodings().zip(args).rev() {
        match (enc, arg) {
            (ArgEncoding::Padding, SimpleArg { value: ScalarValue::Int(0), .. }) => out.pop(),
            _ => break,
        };
    }
    Ok(out)
}

fn raise_arg(raw: &SimpleArg, enc: ArgEncoding) -> Result<Expr, SimpleError> {
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

            | ArgEncoding::JumpTime => bail!("unexpected register used as jump time"),
            | ArgEncoding::JumpOffset => bail!("unexpected register used as jump offset"),
            | ArgEncoding::Word => bail!("unexpected register used as word-sized argument"),
            | ArgEncoding::String { .. } => bail!("unexpected register used as string argument"),
        };
        Ok(Expr::Var(sp!(raise_arg_to_reg(raw, ty)?)))
    } else {
        raise_arg_to_literal(raw, enc)
    }
}

fn raise_arg_to_literal(raw: &SimpleArg, enc: ArgEncoding) -> Result<Expr, SimpleError> {
    if raw.is_reg {
        bail!("expected an immediate, got a variable");
    }

    match enc {
        | ArgEncoding::Padding
        | ArgEncoding::Word
        | ArgEncoding::Dword
        => Ok(Expr::from(raw.expect_int())),

        | ArgEncoding::Sprite
        => match raw.expect_int() {
            -1 => Ok(Expr::from(-1)),
            id => Ok(Expr::Var(sp!(ast::Var::Named {
                ident: crate::formats::anm::auto_sprite_name(id as _).into(),
                ty_sigil: None,
            }))),
        },

        | ArgEncoding::Script
        => Ok(Expr::Var(sp!(ast::Var::Named {
            ident: crate::formats::anm::auto_script_name(raw.expect_int() as _).into(),
            ty_sigil: None,
        }))),

        | ArgEncoding::Color
        => Ok(Expr::LitInt { value: raw.expect_int(), radix: ast::IntRadix::Hex }),

        | ArgEncoding::Float
        => Ok(Expr::from(raw.expect_float())),

        | ArgEncoding::String { .. }
        => Ok(Expr::from(raw.expect_string().clone())),

        // These only show up in intrinsics where they are handled by other code.
        //
        // We *could* eventually support them in user-added custom instructions, but then we'd probably
        // also need to add labels as expressions and `timeof(label)`.
        | ArgEncoding::JumpOffset
        | ArgEncoding::JumpTime
        => bail!("unexpected jump-related arg in non-jump instruction"),
    }
}

fn raise_arg_to_reg(raw: &SimpleArg, ty: ScalarType) -> Result<ast::Var, SimpleError> {
    if !raw.is_reg {
        bail!("expected a variable, got an immediate");
    }
    let ty_sigil = ty.sigil().expect("(bug!) raise_arg_to_reg used on invalid type");
    let reg = match ty_sigil {
        ast::VarReadType::Int => RegId(raw.expect_int()),
        ast::VarReadType::Float => {
            let float_reg = raw.expect_float();
            if float_reg != f32::round(float_reg) {
                bail!("non-integer float variable [{}] in binary file!", float_reg);
            }
            RegId(float_reg as i32)
        },
    };
    Ok(ast::Var::Reg { reg, ty_sigil })
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

fn decode_args(instr: &RawInstr, ty_ctx: &TypeSystem) -> Result<RaiseInstr, SimpleError> {
    use crate::binary_io::BinRead;

    let siggy = match ty_ctx.ins_abi(instr.opcode) {
        Some(siggy) => siggy,
        None => {
            // TODO: would be nice to collect all affected opcodes and generate a single warning
            //       listing all of them at the very end of decompilation, rather than spamming
            //       the console.  Unfortunately this requires retaining some sort of state between
            //       calls to raise_instr
            fast_warning!("unknown signature for ins_{}; decompiling to raw args blob", instr.opcode);

            return Ok(RaiseInstr {
                time: instr.time,
                opcode: instr.opcode,
                args: RaiseArgs::Unknown(UnknownArgsData {
                    param_mask: instr.param_mask,
                    blob: instr.args_blob.to_vec(),
                }),
            });
        },
    };

    let mut param_mask = instr.param_mask;
    let mut args_blob = std::io::Cursor::new(&instr.args_blob);
    let mut args = vec![];
    for (arg_index, enc) in siggy.arg_encodings().enumerate() {
        let is_reg = param_mask % 2 == 1;
        param_mask /= 2;

        let value = crate::error::group_anyhow(|| match enc {
            | ArgEncoding::Dword
            | ArgEncoding::Color
            | ArgEncoding::JumpOffset
            | ArgEncoding::JumpTime
            | ArgEncoding::Padding
            | ArgEncoding::Sprite
            | ArgEncoding::Script
            => Ok(ScalarValue::Int(args_blob.read_u32()? as i32)),

            | ArgEncoding::Float
            => Ok(ScalarValue::Float(f32::from_bits(args_blob.read_u32()?))),

            | ArgEncoding::Word
            => Ok(ScalarValue::Int(args_blob.read_i16()? as i32)),

            | ArgEncoding::String { block_size: _, mask }
            => {
                // read to end
                let read_len = args_blob.get_ref().len() - args_blob.pos()? as usize;
                Ok(ScalarValue::String(args_blob.read_cstring_masked_exact(read_len, mask)?.decode()?))
            },
        }).with_context(|| format!("in argument {} of ins_{}", arg_index + 1, instr.opcode))?;

        args.push(SimpleArg { value, is_reg })
    }

    if args_blob.position() != args_blob.get_ref().len() as u64 {
        fast_warning!(
            // this could mean the signature is incomplete
            "unexpected leftover bytes in ins_{}! (read {} bytes out of {} in file!)",
            instr.opcode, args_blob.position(), args_blob.get_ref().len(),
        );
    }

    if param_mask != 0 {
        fast_warning!(
            "unused bits in ins_{}! (arg {} is a variable, but there are only {} args!)",
            instr.opcode, param_mask.trailing_zeros() + args.len() as u32 + 1, args.len(),
        );
    }
    Ok(RaiseInstr {
        time: instr.time,
        opcode: instr.opcode,
        args: RaiseArgs::Decoded(args),
    })
}

fn expect_abi<'a>(instr: &RaiseInstr, ty_ctx: &'a TypeSystem) -> &'a InstrAbi {
    // if we have Instr then we already must have used the signature earlier to decode the arg bytes,
    // so we can just panic
    ty_ctx.ins_abi(instr.opcode).unwrap_or_else(|| {
        unreachable!("(BUG!) signature not known for opcode {}, but this should have been caught earlier!", instr.opcode)
    })
}
