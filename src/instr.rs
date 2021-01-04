use std::collections::{HashMap};

use anyhow::{Context, bail, ensure};

use crate::error::{GatherErrorIteratorExt, CompileError, SimpleError, group_anyhow};
use crate::pos::{Sp};
use crate::ast::{self, Expr};
use crate::ident::Ident;
use crate::type_system::{TypeSystem, Signature, ArgEncoding, ScalarType};
use crate::binary_io::{BinRead, BinWrite, ReadResult, WriteResult};

#[derive(Debug, Clone, PartialEq)]
pub enum InstrOrLabel {
    Label(Sp<Ident>),
    Instr(Instr),
}
#[derive(Debug, Clone, PartialEq)]
pub struct Instr {
    pub time: i32,
    pub opcode: u16,
    pub args: Vec<InstrArg>,
}
#[derive(Debug, Clone, PartialEq)]
pub enum InstrArg {
    Raw(RawArg),
    /// A label that has not yet been converted to an integer argument.
    ///
    /// This may be present in the input to [`InstrFormat::instr_size`], but will be replaced with
    /// a dword before [`InstrFormat::write_instr`] is called.
    Label(Sp<Ident>),
    /// A `timeof(label)` that has not yet been converted to an integer argument.
    ///
    /// This may be present in the input to [`InstrFormat::instr_size`], but will be replaced with
    /// a dword before [`InstrFormat::write_instr`] is called.
    TimeOf(Sp<Ident>),
}
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct RawArg {
    pub bits: u32,
    pub is_var: bool,
}

impl InstrArg {
    /// Call this at a time when the arg is known to have a fully resolved value.
    ///
    /// Such times are:
    /// * During decompilation.
    /// * Within [`InstrFormat::write_instr`].
    #[track_caller]
    pub fn expect_raw(&self) -> RawArg {
        match *self {
            InstrArg::Raw(x) => x,
            _ => panic!("unexpected unresolved argument (bug!): {:?}", self),
        }
    }

    #[track_caller]
    pub fn expect_immediate_int(&self) -> i32 {
        match *self {
            InstrArg::Raw(x) => {
                assert!(!x.is_var);
                x.bits as i32
            },
            _ => panic!("unexpected unresolved argument (bug!): {:?}", self),
        }
    }

    #[track_caller]
    pub fn expect_immediate_float(&self) -> f32 {
        match *self {
            InstrArg::Raw(x) => {
                assert!(!x.is_var);
                f32::from_bits(x.bits)
            },
            _ => panic!("unexpected unresolved argument (bug!): {:?}", self),
        }
    }
}

impl RawArg {
    pub fn from_global_var(number: i32, ty: ScalarType) -> RawArg {
        let bits = match ty {
            ScalarType::Int => number as u32,
            ScalarType::Float => (number as f32).to_bits(),
        };
        RawArg { bits, is_var: true }
    }
}

impl From<u32> for RawArg {
    fn from(x: u32) -> RawArg { RawArg { bits: x, is_var: false } }
}

impl From<i32> for RawArg {
    fn from(x: i32) -> RawArg { RawArg { bits: x as u32, is_var: false } }
}

impl From<f32> for RawArg {
    fn from(x: f32) -> RawArg { RawArg { bits: x.to_bits(), is_var: false } }
}

fn unsupported(span: &crate::pos::Span) -> CompileError {
    error!(
        message("feature not supported by format"),
        primary(span, "not supported by format"),
    )
}

// =============================================================================

/// Reads the instructions of a complete script, attaching useful information on errors.
///
/// Though it primarily uses the `None` output of [`InstrFormat::read_instr`] to determine when to stop reading
/// instructions, it also may be given an end offset. This will cause it to stop with a warning if it lands on this
/// offset without receiving a `None` result, or to fail outright if it goes past this offset.  This enables the
/// reading of TH095's `front.anm`, which contains the only ANM script in existence to have no end marker.  *Sigh.*
pub fn read_instrs(
    f: &mut dyn BinRead,
    format: &dyn InstrFormat,
    starting_offset: usize,
    end_offset: Option<usize>,
) -> ReadResult<Vec<Instr>> {
    let mut script = vec![];
    let mut offset = starting_offset;
    for index in 0.. {
        if let Some(instr) = format.read_instr(f).with_context(|| format!("in instruction {} (offset {:#x})", index, offset))? {
            offset += format.instr_size(&instr);
            script.push(instr);

            if let Some(end_offset) = end_offset {
                match offset.cmp(&end_offset) {
                    std::cmp::Ordering::Less => {},
                    std::cmp::Ordering::Equal => {
                        fast_warning!("original file is missing an end-of-script marker; one will be added on recompilation");
                        break;
                    },
                    std::cmp::Ordering::Greater => {
                        bail!("script read past expected end at offset {:#x} (we're now at offset {:#x}!)", end_offset, offset);
                    },
                }
            }
        } else {
            break;  // no more instructions
        }
    }
    Ok(script)
}

/// Writes the instructions of a complete script, attaching useful information on errors.
pub fn write_instrs(
    f: &mut dyn BinWrite,
    format: &dyn InstrFormat,
    instrs: &[Instr],
) -> WriteResult {
    for (index, instr) in instrs.iter().enumerate() {
        format.write_instr(f, instr).with_context(|| format!("while writing instruction {}", index))?;
    }
    format.write_terminal_instr(f).with_context(|| format!("while writing the script end marker"))?;
    Ok(())
}

// =============================================================================

pub fn lower_sub_ast_to_instrs(
    format: &dyn InstrFormat,
    code: &[Sp<ast::Stmt>],
    ty_ctx: &TypeSystem,
) -> Result<Vec<Instr>, CompileError> {
    let intrinsic_opcodes: HashMap<_, _> = format.intrinsic_opcode_pairs().into_iter().collect();

    let mut th06_anm_end_span = None;
    let mut out = vec![];
    code.iter().map(|stmt| {
        if let Some(end) = th06_anm_end_span {
            if !matches!(&stmt.body.value, ast::StmtBody::NoInstruction) { return Err(error!(
                message("statement after end of script"),
                primary(&stmt.body, "forbidden statement"),
                secondary(&end, "marks the end of the script"),
                note("In EoSD ANM, every script must have a single exit point (opcode 0 or 15), as the final instruction."),
            ))}
        }

        for label in &stmt.labels {
            match &label.value {
                ast::StmtLabel::Label(ident) => out.push(InstrOrLabel::Label(ident.clone())),
                ast::StmtLabel::Difficulty { .. } => return Err(unsupported(&label.span)),
            }
        }

        let get_opcode = |intrinsic, descr| lookup_opcode(&intrinsic_opcodes, intrinsic, &stmt.body, descr);

        match &stmt.body.value {
            ast::StmtBody::Jump(goto) => {
                if goto.time.is_some() && !format.jump_has_time_arg() {
                    return Err(error!(
                        message("feature not supported by format"),
                        primary(stmt.body, "'goto @ time' not supported in this game"),
                    ));
                }

                let (label_arg, time_arg) = lower_goto_args(goto);

                out.push(InstrOrLabel::Instr(Instr {
                    time: stmt.time,
                    opcode: get_opcode(IntrinsicInstrKind::Jmp, "'goto'")?,
                    args: vec![label_arg, time_arg],
                }));
            },


            ast::StmtBody::Assignment { var, op, value } => {
                out.push(lower_assignment_stmt(stmt, var, op, value, &intrinsic_opcodes, ty_ctx)?);
            },


            ast::StmtBody::InterruptLabel(interrupt_id) => {
                out.push(InstrOrLabel::Instr(Instr {
                    time: stmt.time,
                    opcode: get_opcode(IntrinsicInstrKind::InterruptLabel, "interrupt label")?,
                    args: vec![InstrArg::Raw(interrupt_id.value.into())],
                }));
            },


            ast::StmtBody::CondJump { keyword, cond, jump } => {
                out.push(lower_cond_jump_stmt(stmt, keyword, cond, jump, &intrinsic_opcodes, ty_ctx)?);
            },


            ast::StmtBody::Expr(expr) => match &expr.value {
                ast::Expr::Call { func, args } => {
                    let opcode = match ty_ctx.resolve_func_aliases(func).as_ins() {
                        Some(opcode) => opcode,
                        None => return Err(error!(
                            message("cannot find instruction '{}'", func),
                            primary(func, "not an instruction"),
                        )),
                    };
                    let siggy = match ty_ctx.ins_signature(func) {
                        Some(siggy) => siggy,
                        None => return Err(error!(
                            message("signature of '{}' is not known", func),
                            primary(func, "don't know how to compile this instruction"),
                        )),
                    };
                    let encodings = siggy.arg_encodings();
                    if !(siggy.min_args() <= args.len() && args.len() <= siggy.max_args()) {
                        return Err(error!(
                            message("wrong number of arguments to '{}'", func),
                            primary(func, "expects {} arguments, got {}", encodings.len(), args.len()),
                        ));
                    }

                    let instr = Instr {
                        time: stmt.time,
                        opcode: opcode as _,
                        args: lower_args(func, args, &encodings, ty_ctx)?,
                    };
                    if format.is_th06_anm_terminating_instr(&instr) {
                        th06_anm_end_span = Some(func);
                    }

                    out.push(InstrOrLabel::Instr(instr));
                },
                _ => return Err(unsupported(&expr.span)),
            }, // match expr

            ast::StmtBody::NoInstruction => {}

            _ => return Err(unsupported(&stmt.body.span)),
        }
        Ok(())
    }).collect_with_recovery()?;
    // And fix the labels
    encode_labels(format, 0, &mut out)?;

    Ok(out.into_iter().filter_map(|x| match x {
        InstrOrLabel::Instr(instr) => Some(instr),
        InstrOrLabel::Label(_) => None,
    }).collect())
}

fn lower_goto_args(goto: &ast::StmtGoto) -> (InstrArg, InstrArg) {
    let label_arg = InstrArg::Label(goto.destination.clone());
    let time_arg = match goto.time {
        Some(time) => InstrArg::Raw(time.into()),
        None => InstrArg::TimeOf(goto.destination.clone()),
    };
    (label_arg, time_arg)
}

fn lookup_opcode<T>(
    intrinsic_opcodes: &HashMap<IntrinsicInstrKind, u16>,
    intrinsic: IntrinsicInstrKind,
    span: &Sp<T>,
    descr: &str,
) -> Result<u16, CompileError> {
    match intrinsic_opcodes.get(&intrinsic) {
        Some(&opcode) => Ok(opcode),
        None => Err(error!(
            message("feature not supported by format"),
            primary(span, "{} not supported in this game", descr),
        )),
    }
}

/// Looks at a statement of the form `if (<cond>) goto label @ time;` and tries to produce an instruction from it.
///
/// Only handles conditions that map to instructions, e.g. `a != b` or `b--`, but not `a && b`.
/// Things like the latter are expected to have already been converted into another form if the
/// format supports them.
fn lower_cond_jump_stmt(
    stmt: &ast::Stmt,
    keyword: &Sp<ast::CondKeyword>,
    cond: &Sp<ast::Cond>,
    goto: &ast::StmtGoto,
    intrinsic_opcodes: &HashMap<IntrinsicInstrKind, u16>,
    ty_ctx: &TypeSystem,
) -> Result<InstrOrLabel, CompileError>{
    use IntrinsicInstrKind as IKind;

    let get_opcode = |intrinsic, descr| lookup_opcode(intrinsic_opcodes, intrinsic, &stmt.body, descr);

    let (arg_label, arg_time) = lower_goto_args(goto);

    match (keyword.value, &cond.value) {
        (ast::CondKeyword::If, ast::Cond::Decrement(var)) => {
            let (arg_var, ty_var) = lower_var_to_arg(var, ty_ctx)?;
            if ty_var != ScalarType::Int {
                return Err(error!(
                    message("type error"),
                    primary(cond, "expected an int, got {}", ty_var.descr()),
                    secondary(keyword, "required by this"),
                ));
            }

            Ok(InstrOrLabel::Instr(Instr {
                time: stmt.time,
                opcode: get_opcode(IKind::CountJmp, "decrement jump")?,
                args: vec![arg_var, arg_label, arg_time],
            }))
        },

        (ast::CondKeyword::If, ast::Cond::Expr(expr)) => match &expr.value {
            &Expr::Binop(ref a, op, ref b) => {
                let (arg_a, ty_a) = lower_simple_arg(a, ty_ctx)?;
                let (arg_b, ty_b) = lower_simple_arg(b, ty_ctx)?;
                let ty = ty_a.check_same(ty_b, op.span, (a.span, b.span))?;

                Ok(InstrOrLabel::Instr(Instr {
                    time: stmt.time,
                    opcode: get_opcode(IKind::CondJmp(op.value, ty), "conditional jump")?,
                    args: vec![arg_a, arg_b, arg_label, arg_time],
                }))
            },
            _ => Err(unsupported(&expr.span)),
        },
    }
}

fn lower_assignment_stmt(
    stmt: &ast::Stmt,
    var: &Sp<ast::Var>,
    assign_op: &Sp<ast::AssignOpKind>,
    rhs: &Sp<ast::Expr>,
    intrinsic_opcodes: &HashMap<IntrinsicInstrKind, u16>,
    ty_ctx: &TypeSystem,
) -> Result<InstrOrLabel, CompileError>{
    use IntrinsicInstrKind as IKind;

    let get_opcode = |intrinsic, descr| lookup_opcode(intrinsic_opcodes, intrinsic, &stmt.body, descr);

    match (assign_op.value, &rhs.value) {
        (ast::AssignOpKind::Assign, Expr::Binop(a, binop, b)) => {
            let (arg_var, ty_var) = lower_var_to_arg(var, ty_ctx)?;
            let (arg_a, ty_a) = lower_simple_arg(a, ty_ctx)?;
            let (arg_b, ty_b) = lower_simple_arg(b, ty_ctx)?;
            let ty_rhs = ty_a.check_same(ty_b, binop.span, (a.span, b.span))?;
            let ty = ty_var.check_same(ty_rhs, assign_op.span, (var.span, rhs.span))?;

            Ok(InstrOrLabel::Instr(Instr {
                time: stmt.time,
                opcode: get_opcode(IKind::Binop(binop.value, ty), "assignment of this binary operation")?,
                args: vec![arg_var, arg_a, arg_b],
            }))
        },

        (_, _) => {
            let (arg_var, ty_var) = lower_var_to_arg(var, ty_ctx)?;
            let (arg_rhs, ty_rhs) = lower_simple_arg(rhs, ty_ctx)?;
            let ty = ty_var.check_same(ty_rhs, assign_op.span, (var.span, rhs.span))?;

            Ok(InstrOrLabel::Instr(Instr {
                time: stmt.time,
                opcode: get_opcode(IKind::AssignOp(ast::AssignOpKind::Assign, ty), "simple variable assignment")?,
                args: vec![arg_var, arg_rhs],
            }))
        },
    }
}

fn lower_args(
    func: &Sp<Ident>,
    args: &[Sp<Expr>],
    encodings: &[ArgEncoding],
    ty_ctx: &TypeSystem,
) -> Result<Vec<InstrArg>, CompileError> {
    encodings.iter().zip(args).enumerate().map(|(index, (enc, arg))| {
        let (lowered, value_type) = lower_simple_arg(arg, ty_ctx)?;
        let (expected_type, expected_str) = match enc {
            ArgEncoding::Padding |
            ArgEncoding::Color |
            ArgEncoding::Dword => (ScalarType::Int, "an int"),
            ArgEncoding::Float => (ScalarType::Float, "a float"),
        };
        if value_type != expected_type {
            return Err(error!(
                message("argument {} to '{}' has wrong type", index+1, func),
                primary(arg, "wrong type"),
                secondary(func, "expects {} in arg {}", expected_str, index+1),
            ));
        }
        Ok(lowered)
    }).collect_with_recovery()
}

fn lower_simple_arg(arg: &Sp<ast::Expr>, ty_ctx: &TypeSystem) -> Result<(InstrArg, ScalarType), CompileError> {
    match arg.value {
        ast::Expr::LitInt { value, .. } => Ok((InstrArg::Raw(value.into()), ScalarType::Int)),
        ast::Expr::LitFloat { value, .. } => Ok((InstrArg::Raw(value.into()), ScalarType::Float)),
        ast::Expr::Var(ref var) => lower_var_to_arg(var, ty_ctx),
        _ => Err(unsupported(&arg.span)),
    }
}

fn lower_var_to_arg(var: &Sp<ast::Var>, ty_ctx: &TypeSystem) -> Result<(InstrArg, ScalarType), CompileError> {
    match (ty_ctx.gvar_id(var), ty_ctx.var_type(var)) {
        (Some(opcode), Some(ty)) => {
            let lowered = InstrArg::Raw(RawArg::from_global_var(opcode, ty));
            Ok((lowered, ty))
        },
        (None, _) => return Err(error!(
            message("unrecognized global variable"),
            primary(var, "not a known global"),
        )),
        (Some(_), None) => return Err(error!(
            message("variable requires a type prefix"),
            primary(var, "needs a '$' or '%' prefix"),
        )),
    }
}

pub fn raise_instrs_to_sub_ast(
    ty_ctx: &TypeSystem,
    instr_format: &dyn InstrFormat,
    script: &[Instr],
) -> Result<Vec<Sp<ast::Stmt>>, SimpleError> {
    let opcode_intrinsics: HashMap<_, _> = {
        instr_format.intrinsic_opcode_pairs().into_iter()
            .map(|(a, b)| (b, a)).collect()
    };

    // For now we give every instruction a label and strip the unused ones later.
    let mut offset = 0;
    let code = script.iter().map(|instr| {
        let this_instr_label = sp!(ast::StmtLabel::Label(default_instr_label(offset)));
        offset += instr_format.instr_size(instr);

        let body = raise_instr(instr_format, instr, ty_ctx, &opcode_intrinsics)?;
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
    ty_ctx: &TypeSystem,
    opcode_intrinsics: &HashMap<u16, IntrinsicInstrKind>,
) -> Result<ast::StmtBody, SimpleError> {
    let Instr { opcode, ref args, .. } = *instr;
    match opcode_intrinsics.get(&opcode).copied() {
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
                ty_ctx.opcode_names.get(&(opcode as u32)).cloned()
                    .unwrap_or_else(|| Ident::new_ins(opcode as u32))
            };

            Ok(ast::StmtBody::Expr(sp!(Expr::Call {
                args: match ty_ctx.ins_signature(&ins_ident) {
                    Some(siggy) => raise_args(args, siggy, ty_ctx)?,
                    None => raise_args(args, &Signature::auto(args.len()), ty_ctx)?,
                },
                func: sp!(ins_ident),
            })))
        }).with_context(|| format!("while decompiling ins_{}", opcode)),
    }
}

fn raise_args(args: &[InstrArg], siggy: &Signature, ty_ctx: &TypeSystem) -> Result<Vec<Sp<Expr>>, SimpleError> {
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

fn raise_arg(raw: &RawArg, enc: ArgEncoding, ty_ctx: &TypeSystem) -> Result<Expr, SimpleError> {
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

fn raise_arg_to_var(raw: &RawArg, ty: ScalarType, ty_ctx: &TypeSystem) -> Result<ast::Var, SimpleError> {
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
    Ok(ty_ctx.gvar_to_ast(id, ty))
}

// =============================================================================

struct RawLabelInfo {
    time: i32,
    offset: usize,
}
fn gather_label_info(
    format: &dyn InstrFormat,
    initial_offset: usize,
    code: &[InstrOrLabel]
) -> Result<HashMap<Sp<Ident>, RawLabelInfo>, CompileError> {
    use std::collections::hash_map::Entry;

    let mut offset = initial_offset;
    let mut pending_labels = vec![];
    let mut out = HashMap::new();
    code.iter().map(|thing| {
        match thing {
            // can't insert labels until we see the time of the instructions they are labeling
            InstrOrLabel::Label(ident) => pending_labels.push(ident),
            InstrOrLabel::Instr(instr) => {
                for label in pending_labels.drain(..) {
                    match out.entry(label.clone()) {
                        Entry::Vacant(e) => {
                            e.insert(RawLabelInfo { time: instr.time, offset });
                        },
                        Entry::Occupied(e) => {
                            let old = e.key();
                            return Err(error!{
                                message("duplicate label '{}'", label),
                                primary(label, "redefined here"),
                                secondary(old, "originally defined here"),
                            });
                        },
                    }
                }
                offset += format.instr_size(instr);
            },
        }
        Ok(())
    }).collect_with_recovery()?;
    assert!(pending_labels.is_empty(), "unexpected label after last instruction! (bug?)");
    Ok(out)
}

/// Eliminates all `InstrOrLabel::Label`s by replacing them with their dword values.
fn encode_labels(
    format: &dyn InstrFormat,
    initial_offset: usize,
    code: &mut [InstrOrLabel],
) -> Result<(), CompileError> {
    let label_info = gather_label_info(format, initial_offset, code)?;

    code.iter_mut().map(|thing| {
        match thing {
            InstrOrLabel::Instr(instr) => for arg in &mut instr.args {
                match *arg {
                    | InstrArg::Label(ref label)
                    | InstrArg::TimeOf(ref label)
                    => match label_info.get(label) {
                        Some(info) => match arg {
                            InstrArg::Label(_) => *arg = InstrArg::Raw(format.encode_label(info.offset).into()),
                            InstrArg::TimeOf(_) => *arg = InstrArg::Raw(info.time.into()),
                            _ => unreachable!(),
                        },
                        None => return Err(error!{
                            message("undefined label '{}'", label),
                            primary(label, "there is no label by this name"),
                        }),
                    },
                    _ => {},
                }
            },
            InstrOrLabel::Label(_) => {},
        }
        Ok(())
    }).collect_with_recovery()
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
    /// Like `a = sin(b);`
    ///
    /// Args: `a, b`.
    TransOp(TransOpKind),
    /// Like `if (x--) goto label @ t`.
    ///
    /// Args: `x, label, t`.
    CountJmp,
    /// Like `if (a == c) goto label @ t;`
    ///
    /// Args: `a, b, label, t`
    CondJmp(ast::BinopKind, ScalarType),
}

/// Transcendental functions available in at least one game.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TransOpKind { Sin, Cos, Tan, Acos, Atan }

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

pub trait InstrFormat {
    /// Get the number of bytes in the binary encoding of an instruction.
    fn instr_size(&self, instr: &Instr) -> usize;

    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, u16)>;

    /// Read a single script instruction from an input stream.
    ///
    /// Should return `None` when it reaches the marker that indicates the end of the script.
    /// When this occurs, it may leave the `Cursor` in an indeterminate state.
    fn read_instr(&self, f: &mut dyn BinRead) -> ReadResult<Option<Instr>>;

    /// Write a single script instruction into an output stream.
    fn write_instr(&self, f: &mut dyn BinWrite, instr: &Instr) -> WriteResult;

    /// Write a marker that goes after the final instruction in a function or script.
    fn write_terminal_instr(&self, f: &mut dyn BinWrite) -> WriteResult;

    // ---------------------------------------------------
    // Special purpose functions only overridden by a few formats

    /// Indicates that [`IntrinsicInstrKind::Jmp`] takes two arguments, where the second is time.
    ///
    /// TH06 ANM has no time arg. (it always sets the script clock to the destination's time)
    fn jump_has_time_arg(&self) -> bool { true }

    /// Used by TH06 to indicate that an instruction must be the last instruction in the script.
    fn is_th06_anm_terminating_instr(&self, _instr: &Instr) -> bool { false }

    // Most formats encode labels as offsets from the beginning of the script (in which case
    // these functions are trivial), but early STD is a special snowflake that writes the
    // instruction *index* instead.
    fn encode_label(&self, offset: usize) -> u32 { offset as _ }
    fn decode_label(&self, bits: u32) -> usize { bits as _ }
}

/// Helper to help implement `InstrFormat::read_instr`.
///
/// Reads `size` bytes into `size/4` dword arguments and sets their `is_var` flags according to
/// the parameter mask.  (it takes `size` instead of a count to help factor out divisibility checks,
/// as a size is often what you have to work with given the format)
pub fn read_dword_args_upto_size(
    f: &mut dyn BinRead,
    size: usize,
    mut param_mask: u16,
) -> ReadResult<Vec<InstrArg>> {
    if size % 4 != 0 {
        bail!("size not divisible by 4: {}", size);
    }
    let nargs = size/4;

    let out = (0..nargs).map(|_| {
        let bits = f.read_u32()?;
        let is_var = param_mask % 2 == 1;
        param_mask /= 2;
        Ok(InstrArg::Raw(RawArg { bits, is_var }))
    }).collect::<ReadResult<_>>()?;

    if param_mask != 0 {
        fast_warning!(
            "unused bits in param_mask! (arg {} is a variable, but there are only {} args!)",
            param_mask.trailing_zeros() + nargs as u32 + 1, nargs,
        );
    }
    Ok(out)
}

impl Instr {
    pub fn compute_param_mask(&self) -> Result<u16, SimpleError> {
        if self.args.len() > 16 {
            bail!("too many arguments in instruction!");
        }
        let mut mask = 0;
        for arg in self.args.iter().rev(){
            let bit = match *arg {
                InstrArg::Raw(RawArg { is_var, .. }) => is_var as u16,
                InstrArg::TimeOf(_) |
                InstrArg::Label(_) => 0,
            };
            mask *= 2;
            mask += bit;
        }
        Ok(mask)
    }
}
