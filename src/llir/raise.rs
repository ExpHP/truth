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

    // For now we put a label at every possible offset, and strip the unused ones later.
    let mut offset = 0;
    let mut out = vec![sp!(ast::Stmt {
        time: 0, body: ast::StmtBody::NoInstruction,
    })];
    for instr in script {
        let label_ident = default_instr_label(offset);
        offset += instr_format.instr_size(instr);

        let body = raise_instr(instr_format, instr, ty_ctx, &intrinsic_instrs)?;
        out.push(rec_sp!(Span::NULL => stmt_label!(at #(instr.time), #label_ident)));
        out.push(rec_sp!(Span::NULL => stmt!(at #(instr.time), #body)));
    }

    let end_time = out.last().expect("there must be at least the other bookend!").time;
    out.push(rec_sp!(Span::NULL => stmt_label!(at #end_time, #(default_instr_label(offset)))));
    Ok(out)
}

fn default_instr_label(offset: usize) -> Ident {
    format!("label_{}", offset).parse::<Ident>().unwrap()
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
            let dest_label = default_instr_label(dest_offset);

            Ok(stmt_goto!(rec_sp!(Span::NULL => goto #dest_label #dest_time)))
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
            let dest_offset = instr_format.decode_label(args[1].expect_raw().bits);
            let dest_time = args[2].expect_immediate_int();
            let dest_label = default_instr_label(dest_offset);

            Ok(stmt_cond_goto!(rec_sp!(Span::NULL =>
                if (decvar: #var) goto #dest_label @ #dest_time
            )))
        }).with_context(|| format!("while decompiling a decrement jump")),


        Some(IntrinsicInstrKind::CondJmp(op, ty)) => group_anyhow(|| {
            ensure!(args.len() == 4, "expected {} args, got {}", 4, args.len());
            let a = raise_arg(&args[0].expect_raw(), ty.default_encoding())?;
            let b = raise_arg(&args[1].expect_raw(), ty.default_encoding())?;
            let dest_offset = instr_format.decode_label(args[2].expect_raw().bits);
            let dest_time = args[3].expect_immediate_int();
            let dest_label = default_instr_label(dest_offset);

            Ok(stmt_cond_goto!(rec_sp!(Span::NULL =>
                if expr_binop!(#a #op #b) goto #dest_label @ #dest_time
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
                    None => raise_args(args, &Signature::auto(args.len()))?,
                },
                func: sp!(ins_ident),
            })))
        }).with_context(|| format!("while decompiling ins_{}", opcode)),
    }
}

fn raise_args(args: &[InstrArg], siggy: &Signature) -> Result<Vec<Sp<Expr>>, SimpleError> {
    let encodings = siggy.arg_encodings();

    if args.len() != encodings.len() {
        bail!("provided arg count ({}) does not match mapfile ({})", args.len(), encodings.len());
    }
    let mut out = encodings.iter().zip(args).enumerate().map(|(i, (&enc, arg))| {
        let arg_ast = raise_arg(&arg.expect_raw(), enc).with_context(|| format!("in argument {}", i + 1))?;
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

fn raise_arg(raw: &RawArg, enc: ArgEncoding) -> Result<Expr, SimpleError> {
    if raw.is_reg {
        let ty = match enc {
            ArgEncoding::Padding |
            ArgEncoding::Color |
            ArgEncoding::Dword => ScalarType::Int,
            ArgEncoding::Float => ScalarType::Float,
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
