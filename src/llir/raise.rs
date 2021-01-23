use std::collections::{BTreeMap, BTreeSet};

use anyhow::{Context, ensure, bail};

use crate::ast::{self, Expr};
use crate::ident::Ident;
use crate::pos::{Sp, Span};
use crate::error::{group_anyhow, SimpleError};
use crate::llir::{Instr, InstrArg, InstrFormat, IntrinsicInstrKind, IntrinsicInstrs, RawArg};
use crate::var::{VarId, RegId};
use crate::type_system::{ArgEncoding, RegsAndInstrs, ScalarType, Signature};

pub fn raise_instrs_to_sub_ast(
    instr_format: &dyn InstrFormat,
    script: &[Instr],
    ty_ctx: &RegsAndInstrs,
) -> Result<Vec<Sp<ast::Stmt>>, SimpleError> {
    let intrinsic_instrs = instr_format.intrinsic_instrs();

    let jump_data = gather_label_data(instr_format, script, ty_ctx)?;
    let offset_labels = generate_offset_labels(script, &jump_data)?;
    let mut out = vec![sp!(ast::Stmt {
        time: script.get(0).map(|x| x.time).unwrap_or(0),
        body: ast::StmtBody::NoInstruction,
    })];

    for (&offset, instr) in zip!(&jump_data.instr_offsets, script) {
        if let Some(label) = offset_labels.get(&offset) {
            out.push(rec_sp!(Span::NULL => stmt_label!(at #(label.time_label), #(label.label.clone()))));
        }

        let body = raise_instr(instr_format, instr, ty_ctx, &intrinsic_instrs, &offset_labels)?;
        out.push(rec_sp!(Span::NULL => stmt!(at #(instr.time), #body)));
    }

    // possible label after last instruction
    let end_time = out.last().expect("there must be at least the other bookend!").time;
    if let Some(label) = offset_labels.get(jump_data.instr_offsets.last().expect("n + 1 offsets so there's always at least one")) {
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
    /// The offsets for each instruction.
    instr_offsets: Vec<u64>,
}

fn gather_label_data(
    instr_format: &dyn InstrFormat,
    script: &[Instr],
    ty_ctx: &RegsAndInstrs,
) -> Result<JumpData, SimpleError> {
    let mut all_offset_args = BTreeMap::<u64, BTreeSet<Option<i32>>>::new();
    let mut instr_offsets = vec![0];
    let mut offset = 0;

    for instr in script {
        offset += instr_format.instr_size(instr) as u64;
        instr_offsets.push(offset);

        if let Some((jump_offset, jump_time)) = extract_jump_args_by_signature(instr_format, instr, ty_ctx) {
            all_offset_args.entry(jump_offset).or_default().insert(jump_time);
        }
    }

    Ok(JumpData { all_offset_args, instr_offsets })
}

fn generate_offset_labels(
    script: &[Instr],
    jump_data: &JumpData,
) -> Result<BTreeMap<u64, Label>, SimpleError> {
    let mut offset_labels = BTreeMap::new();
    for (&offset, time_args) in &jump_data.all_offset_args {
        let dest_index = {
            jump_data.instr_offsets.binary_search(&offset)
                .map_err(|_| anyhow::anyhow!("an instruction has a bad jump offset!"))?
        };
        // Find out the time range between this instruction and the previous one
        // (the or_else triggers when dest_index == script.len() (label after last instruction))
        let dest_time = script.get(dest_index).unwrap_or_else(|| script.last().unwrap()).time;
        let next = (jump_data.instr_offsets[dest_index], dest_time);
        let prev = match dest_index {
            0 => None,
            i => Some((jump_data.instr_offsets[i - 1], script[i - 1].time)),
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
    instr: &Instr,
    ty_ctx: &RegsAndInstrs,
) -> Option<(u64, Option<i32>)> {
    let mut jump_offset = None;
    let mut jump_time = None;

    if let Some(siggy) = ty_ctx.ins_signature(instr.opcode) {
        let encodings = siggy.arg_encodings();

        for (arg, encoding) in zip!(&instr.args, encodings) {
            match encoding {
                ArgEncoding::JumpOffset => jump_offset = Some(instr_format.decode_label(arg.expect_raw().bits)),
                ArgEncoding::JumpTime => jump_time = Some(arg.expect_immediate_int()),
                _ => {},
            }
        }
    }

    jump_offset.map(|offset| (offset, jump_time))
}


fn raise_instr(
    instr_format: &dyn InstrFormat,
    instr: &Instr,
    ty_ctx: &RegsAndInstrs,
    intrinsic_instrs: &IntrinsicInstrs,
    offset_labels: &BTreeMap<u64, Label>,
) -> Result<ast::StmtBody, SimpleError> {
    let Instr { opcode, ref args, .. } = *instr;
    match intrinsic_instrs.get_intrinsic(opcode) {
        Some(IntrinsicInstrKind::Jmp) => group_anyhow(|| {
            let nargs = if instr_format.jump_has_time_arg() { 2 } else { 1 };

            // This one is >= because it exists in early STD where there can be padding args.
            ensure!(args.len() >= nargs, "expected {} args, got {}", nargs, args.len());
            ensure!(args[nargs..].iter().all(|a| a.expect_raw().bits == 0), "unsupported data in padding of intrinsic");

            let goto = raise_jump_args(&args[0], args.get(1), instr_format, offset_labels);
            Ok(stmt_goto!(rec_sp!(Span::NULL => goto #(goto.destination) #(goto.time))))
        }).with_context(|| format!("while decompiling a 'goto' operation")),


        Some(IntrinsicInstrKind::AssignOp(op, ty)) => group_anyhow(|| {
            ensure!(args.len() == 2, "expected {} args, got {}", 2, args.len());
            let var = raise_arg_to_var(&args[0].expect_raw(), ty)?;
            let value = raise_arg(&args[1].expect_raw(), ty.default_encoding())?;

            Ok(stmt_assign!(rec_sp!(Span::NULL => #var #op #value)))
        }).with_context(|| format!("while decompiling a '{}' operation", op)),


        Some(IntrinsicInstrKind::Binop(op, ty)) => group_anyhow(|| {
            ensure!(args.len() == 3, "expected {} args, got {}", 3, args.len());
            let var = raise_arg_to_var(&args[0].expect_raw(), ty)?;
            let a = raise_arg(&args[1].expect_raw(), ty.default_encoding())?;
            let b = raise_arg(&args[2].expect_raw(), ty.default_encoding())?;

            Ok(stmt_assign!(rec_sp!(Span::NULL => #var = expr_binop!(#a #op #b))))
        }).with_context(|| format!("while decompiling a '{}' operation", op)),


        Some(IntrinsicInstrKind::Unop(op, ty)) => group_anyhow(|| {
            ensure!(args.len() == 2, "expected {} args, got {}", 2, args.len());
            let var = raise_arg_to_var(&args[0].expect_raw(), ty)?;
            let b = raise_arg(&args[1].expect_raw(), ty.default_encoding())?;

            Ok(stmt_assign!(rec_sp!(Span::NULL => #var = expr_unop!(#op #b))))
        }).with_context(|| format!("while decompiling a unary '{}' operation", op)),


        Some(IntrinsicInstrKind::InterruptLabel) => group_anyhow(|| {
            // This one is >= because it exists in STD where there can be padding args.
            ensure!(args.len() >= 1, "expected {} args, got {}", 1, args.len());
            ensure!(args[1..].iter().all(|a| a.expect_raw().bits == 0), "unsupported data in padding of intrinsic");

            Ok(stmt_interrupt!(rec_sp!(Span::NULL => #(args[0].expect_immediate_int()) )))
        }).with_context(|| format!("while decompiling an interrupt label")),


        Some(IntrinsicInstrKind::CountJmp) => group_anyhow(|| {
            ensure!(args.len() == 3, "expected {} args, got {}", 3, args.len());
            let var = raise_arg_to_var(&args[0].expect_raw(), ScalarType::Int)?;
            let goto = raise_jump_args(&args[1], Some(&args[2]), instr_format, offset_labels);

            Ok(stmt_cond_goto!(rec_sp!(Span::NULL =>
                if (decvar: #var) goto #(goto.destination) #(goto.time)
            )))
        }).with_context(|| format!("while decompiling a decrement jump")),


        Some(IntrinsicInstrKind::CondJmp(op, ty)) => group_anyhow(|| {
            ensure!(args.len() == 4, "expected {} args, got {}", 4, args.len());
            let a = raise_arg(&args[0].expect_raw(), ty.default_encoding())?;
            let b = raise_arg(&args[1].expect_raw(), ty.default_encoding())?;
            let goto = raise_jump_args(&args[2], Some(&args[3]), instr_format, offset_labels);

            Ok(stmt_cond_goto!(rec_sp!(Span::NULL =>
                if expr_binop!(#a #op #b) goto #(goto.destination) #(goto.time)
            )))
        }).with_context(|| format!("while decompiling a conditional jump")),


        None => group_anyhow(|| {
            // Default behavior for general instructions
            let ins_ident = {
                ty_ctx.opcode_names.get(&opcode).cloned()
                    .unwrap_or_else(|| Ident::new_ins(opcode))
            };

            Ok(ast::StmtBody::Expr(sp!(Expr::Call {
                args: match ty_ctx.ins_signature(opcode) {
                    Some(siggy) => raise_args(args, siggy)?,
                    None => {
                        let siggy = Signature::auto(args.len());
                        fast_warning!("don't know how to decompile opcode {}! (assuming signature '{}')", opcode, siggy.as_str());
                        raise_args(args, &siggy)?
                    },
                },
                func: sp!(ins_ident),
            })))
        }).with_context(|| format!("while decompiling ins_{}", opcode)),
    }
}


fn raise_args(args: &[InstrArg], siggy: &Signature) -> Result<Vec<Sp<Expr>>, SimpleError> {
    if args.len() != siggy.arg_encodings().len() {
        bail!("provided arg count ({}) does not match mapfile ({})", args.len(), siggy.arg_encodings().len());
    }

    let mut out = siggy.arg_encodings().zip(args).enumerate().map(|(i, (enc, arg))| {
        let arg_ast = raise_arg(&arg.expect_raw(), enc).with_context(|| format!("in argument {}", i + 1))?;
        Ok(sp!(arg_ast))
    }).collect::<Result<Vec<_>, SimpleError>>()?;

    // drop early STD padding args from the end as long as they're zero
    for (enc, arg) in siggy.arg_encodings().zip(args).rev() {
        match (enc, arg) {
            (ArgEncoding::Padding, InstrArg::Raw(RawArg { bits: 0, .. })) => out.pop(),
            _ => break,
        };
    }
    Ok(out)
}

fn raise_arg(raw: &RawArg, enc: ArgEncoding) -> Result<Expr, SimpleError> {
    if raw.is_reg {
        let ty = match enc {
            ArgEncoding::Padding |
            ArgEncoding::Color |
            ArgEncoding::Dword => ScalarType::Int,
            ArgEncoding::Float => ScalarType::Float,
            ArgEncoding::JumpTime => bail!("unexpected register used as jump time"),
            ArgEncoding::JumpOffset => bail!("unexpected register used as jump offset"),
        };
        Ok(Expr::Var(sp!(raise_arg_to_var(raw, ty)?)))
    } else {
        raise_arg_to_literal(raw, enc)
    }
}

fn raise_arg_to_literal(raw: &RawArg, enc: ArgEncoding) -> Result<Expr, SimpleError> {
    if raw.is_reg {
        bail!("expected an immediate, got a variable");
    }
    match enc {
        ArgEncoding::Padding |
        ArgEncoding::Dword => Ok(Expr::from(raw.bits as i32)),
        ArgEncoding::Color => Ok(Expr::LitInt { value: raw.bits as i32, hex: true }),
        ArgEncoding::Float => Ok(Expr::from(f32::from_bits(raw.bits))),

        // These only show up in intrinsics where they are handled by other code.
        //
        // We *could* eventually support them in user-added custom instructions, but then we'd probably
        // also need to add labels as expressions and `timeof(label)`.
        ArgEncoding::JumpOffset |
        ArgEncoding::JumpTime => bail!("unexpected jump-related arg in non-jump instruction"),
    }
}

fn raise_arg_to_var(raw: &RawArg, ty: ScalarType) -> Result<ast::Var, SimpleError> {
    if !raw.is_reg {
        bail!("expected a variable, got an immediate");
    }
    let reg = match ty {
        ScalarType::Int => RegId(raw.bits as i32),
        ScalarType::Float => {
            let float_reg = f32::from_bits(raw.bits);
            if float_reg != f32::round(float_reg) {
                bail!("non-integer float variable [{}] in binary file!", float_reg);
            }
            RegId(float_reg as i32)
        },
    };
    Ok(ast::Var::Resolved {
        var_id: VarId::Reg(reg),
        ty_sigil: Some(ty.into()),
    })
}

fn raise_jump_args(
    offset_arg: &InstrArg,
    time_arg: Option<&InstrArg>,  // None when the instruction signature has no time arg
    instr_format: &dyn InstrFormat,
    offset_labels: &BTreeMap<u64, Label>,
) -> ast::StmtGoto {
    let offset = instr_format.decode_label(offset_arg.expect_raw().bits);
    let label = &offset_labels[&offset];
    ast::StmtGoto {
        destination: sp!(label.label.clone()),
        time: time_arg.map(|arg| arg.expect_immediate_int()).filter(|&t| t != label.time_label),
    }
}
