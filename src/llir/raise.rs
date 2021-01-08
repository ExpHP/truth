use anyhow::{Context, ensure, bail};

use crate::ast::{self, Expr};
use crate::ident::Ident;
use crate::pos::Sp;
use crate::error::{group_anyhow, SimpleError};
use crate::llir::{Instr, InstrArg, InstrFormat, IntrinsicInstrKind, IntrinsicInstrs, RawArg};
use crate::type_system::{ArgEncoding, RegsAndInstrs, ScalarType, Signature};

pub fn raise_instrs_to_sub_ast(
    ty_ctx: &RegsAndInstrs,
    instr_format: &dyn InstrFormat,
    script: &[Instr],
) -> Result<Vec<Sp<ast::Stmt>>, SimpleError> {
    let intrinsic_instrs = instr_format.intrinsic_instrs();

    // For now we give every instruction a label and strip the unused ones later.
    let mut offset = 0;
    let code = script.iter().map(|instr| {
        let this_instr_label = sp!(ast::StmtLabel::Label(default_instr_label(offset)));
        offset += instr_format.instr_size(instr);

        let body = raise_instr(instr_format, instr, ty_ctx, &intrinsic_instrs)?;
        Ok(sp!(ast::Stmt {
            time: instr.time,
            labels: vec![this_instr_label],
            body: sp!(body),
        }))
    }).collect();
    code
}

fn default_instr_label(offset: usize) -> Sp<Ident> {
    sp!(format!("label_{}", offset).parse::<Ident>().unwrap())
}

fn raise_instr(
    instr_format: &dyn InstrFormat,
    instr: &Instr,
    ty_ctx: &RegsAndInstrs,
    intrinsic_instrs: &IntrinsicInstrs,
) -> Result<ast::StmtBody, SimpleError> {
    let Instr { opcode, ref args, .. } = *instr;
    match intrinsic_instrs.get_intrinsic(opcode) {
        Some(IntrinsicInstrKind::Jmp) => group_anyhow(|| {
            let nargs = if instr_format.jump_has_time_arg() { 2 } else { 1 };

            // This one is >= because it exists in early STD where there can be padding args.
            ensure!(args.len() >= nargs, "expected {} args, got {}", nargs, args.len());
            ensure!(args[nargs..].iter().all(|a| a.expect_raw().bits == 0), "unsupported data in padding of intrinsic");

            let dest_offset = instr_format.decode_label(args[0].expect_raw().bits);
            let dest_time = match instr_format.jump_has_time_arg() {
                true => Some(args[1].expect_immediate_int()),
                false => None,
            };
            Ok(ast::StmtBody::Jump(ast::StmtGoto {
                destination: default_instr_label(dest_offset),
                time: dest_time,
            }))
        }).with_context(|| format!("while decompiling a 'goto' operation")),


        Some(IntrinsicInstrKind::AssignOp(op, ty)) => group_anyhow(|| {
            ensure!(args.len() == 2, "expected {} args, got {}", 2, args.len());
            Ok(ast::StmtBody::Assignment {
                var: sp!(raise_arg_to_var(&args[0].expect_raw(), ty, ty_ctx)?),
                op: sp!(op),
                value: sp!(raise_arg(&args[1].expect_raw(), ty.default_encoding(), ty_ctx)?),
            })
        }).with_context(|| format!("while decompiling a '{}' operation", op)),


        Some(IntrinsicInstrKind::Binop(op, ty)) => group_anyhow(|| {
            ensure!(args.len() == 3, "expected {} args, got {}", 3, args.len());
            Ok(ast::StmtBody::Assignment {
                var: sp!(raise_arg_to_var(&args[0].expect_raw(), ty, ty_ctx)?),
                op: sp!(ast::AssignOpKind::Assign),
                value: sp!(Expr::Binop(
                    Box::new(sp!(raise_arg(&args[1].expect_raw(), ty.default_encoding(), ty_ctx)?)),
                    sp!(op),
                    Box::new(sp!(raise_arg(&args[2].expect_raw(), ty.default_encoding(), ty_ctx)?)),
                )),
            })
        }).with_context(|| format!("while decompiling a '{}' operation", op)),


        Some(IntrinsicInstrKind::InterruptLabel) => group_anyhow(|| {
            // This one is >= because it exists in STD where there can be padding args.
            ensure!(args.len() >= 1, "expected {} args, got {}", 1, args.len());
            ensure!(args[1..].iter().all(|a| a.expect_raw().bits == 0), "unsupported data in padding of intrinsic");

            Ok(ast::StmtBody::InterruptLabel(sp!(args[0].expect_immediate_int())))
        }).with_context(|| format!("while decompiling an interrupt label")),


        Some(IntrinsicInstrKind::CountJmp) => group_anyhow(|| {
            ensure!(args.len() == 3, "expected {} args, got {}", 3, args.len());
            let var = raise_arg_to_var(&args[0].expect_raw(), ScalarType::Int, ty_ctx)?;
            let dest_offset = instr_format.decode_label(args[1].expect_raw().bits);
            let dest_time = Some(args[2].expect_immediate_int());

            Ok(ast::StmtBody::CondJump {
                keyword: sp!(ast::CondKeyword::If),
                cond: sp!(ast::Cond::Decrement(sp!(var))),
                jump: ast::StmtGoto {
                    destination: default_instr_label(dest_offset),
                    time: dest_time,
                },
            })
        }).with_context(|| format!("while decompiling a decrement jump")),


        Some(IntrinsicInstrKind::CondJmp(op, ty)) => group_anyhow(|| {
            ensure!(args.len() == 4, "expected {} args, got {}", 4, args.len());
            let a = raise_arg(&args[0].expect_raw(), ty.default_encoding(), ty_ctx)?;
            let b = raise_arg(&args[1].expect_raw(), ty.default_encoding(), ty_ctx)?;
            let dest_offset = instr_format.decode_label(args[2].expect_raw().bits);
            let dest_time = Some(args[3].expect_immediate_int());

            Ok(ast::StmtBody::CondJump {
                keyword: sp!(ast::CondKeyword::If),
                cond: sp!(ast::Cond::Expr(sp!({
                    ast::Expr::Binop(Box::new(sp!(a)), sp!(op), Box::new(sp!(b)))
                }))),
                jump: ast::StmtGoto {
                    destination: default_instr_label(dest_offset),
                    time: dest_time,
                },
            })
        }).with_context(|| format!("while decompiling a conditional jump")),


        // raising of these not yet implemented
        Some(IntrinsicInstrKind::TransOp(_)) |
        None => group_anyhow(|| {
            // Default behavior for general instructions
            let ins_ident = {
                ty_ctx.opcode_names.get(&opcode).cloned()
                    .unwrap_or_else(|| Ident::new_ins(opcode))
            };

            Ok(ast::StmtBody::Expr(sp!(Expr::Call {
                args: match ty_ctx.ins_signature(opcode) {
                    Some(siggy) => raise_args(args, siggy, ty_ctx)?,
                    None => raise_args(args, &Signature::auto(args.len()), ty_ctx)?,
                },
                func: sp!(ins_ident),
            })))
        }).with_context(|| format!("while decompiling ins_{}", opcode)),
    }
}

fn raise_args(args: &[InstrArg], siggy: &Signature, ty_ctx: &RegsAndInstrs) -> Result<Vec<Sp<Expr>>, SimpleError> {
    let encodings = siggy.arg_encodings();

    if args.len() != encodings.len() {
        bail!("provided arg count ({}) does not match mapfile ({})", args.len(), encodings.len());
    }
    let mut out = encodings.iter().zip(args).enumerate().map(|(i, (&enc, arg))| {
        let arg_ast = raise_arg(&arg.expect_raw(), enc, ty_ctx).with_context(|| format!("in argument {}", i + 1))?;
        Ok(sp!(arg_ast))
    }).collect::<Result<Vec<_>, SimpleError>>()?;

    // drop early STD padding args from the end as long as they're zero
    for (enc, arg) in encodings.iter().zip(args).rev() {
        match (enc, arg) {
            (ArgEncoding::Padding, InstrArg::Raw(RawArg { bits: 0, .. })) => out.pop(),
            _ => break,
        };
    }
    Ok(out)
}

fn raise_arg(raw: &RawArg, enc: ArgEncoding, ty_ctx: &RegsAndInstrs) -> Result<Expr, SimpleError> {
    if raw.is_var {
        let ty = match enc {
            ArgEncoding::Padding |
            ArgEncoding::Color |
            ArgEncoding::Dword => ScalarType::Int,
            ArgEncoding::Float => ScalarType::Float,
        };
        Ok(Expr::Var(sp!(raise_arg_to_var(raw, ty, ty_ctx)?)))
    } else {
        raise_arg_to_literal(raw, enc)
    }
}

fn raise_arg_to_literal(raw: &RawArg, enc: ArgEncoding) -> Result<Expr, SimpleError> {
    if raw.is_var {
        bail!("expected an immediate, got a variable");
    }
    match enc {
        ArgEncoding::Padding |
        ArgEncoding::Dword => Ok(Expr::from(raw.bits as i32)),
        ArgEncoding::Color => Ok(Expr::LitInt { value: raw.bits as i32, hex: true }),
        ArgEncoding::Float => Ok(Expr::from(f32::from_bits(raw.bits))),
    }
}

fn raise_arg_to_var(raw: &RawArg, ty: ScalarType, ty_ctx: &RegsAndInstrs) -> Result<ast::Var, SimpleError> {
    if !raw.is_var {
        bail!("expected a variable, got an immediate");
    }
    let id = match ty {
        ScalarType::Int => raw.bits as i32,
        ScalarType::Float => {
            let float_id = f32::from_bits(raw.bits);
            if float_id != f32::round(float_id) {
                bail!("non-integer float variable [{}] in binary file!", float_id);
            }
            float_id as i32
        },
    };
    Ok(ty_ctx.reg_to_ast(id, ty))
}
