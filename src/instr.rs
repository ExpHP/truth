use std::collections::{HashMap};


use crate::error::{GatherErrorIteratorExt, CompileError};
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
        
        match &stmt.body.value {
            ast::StmtBody::Jump(goto) => {
                let time_arg = match goto.time {
                    Some(time) => InstrArg::Raw(time.into()),
                    None => InstrArg::TimeOf(goto.destination.clone()),
                };
                out.push(InstrOrLabel::Instr(Instr {
                    time: stmt.time,
                    opcode: match intrinsic_opcodes.get(&IntrinsicInstrKind::Jmp) {
                        Some(&opcode) => opcode,
                        None => return Err(error!(
                            message("feature not supported by format"),
                            primary(stmt.body, "'goto' not supported in this game"),
                        )),
                    },
                    args: vec![InstrArg::Label(goto.destination.clone()), time_arg],
                }));
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
        ast::Expr::Var(ref var) => match (ty_ctx.gvar_id(var), ty_ctx.var_type(var)) {
            (Some(opcode), Some(ty)) => {
                let lowered = InstrArg::Raw(RawArg::from_global_var(opcode, ty));
                Ok((lowered, ty))
            },
            (None, _) =>  return Err(error!(
                message("unrecognized global variable"),
                primary(var, "not a known global"),
            )),
            (Some(_), None) => return Err(error!(
                message("variable requires a type prefix"),
                primary(var, "needs a '$' or '%' prefix"),
            )),
        },
        _ => Err(unsupported(&arg.span)),
    }
}

pub fn raise_instrs_to_sub_ast(ty_ctx: &TypeSystem, instr_format: &dyn InstrFormat, script: &[Instr]) -> Vec<Sp<ast::Stmt>> {
    let opcode_intrinsics: HashMap<_, _> = {
        instr_format.intrinsic_opcode_pairs().into_iter()
            .map(|(a, b)| (b, a)).collect()
    };

    let default_label = |offset: usize| {
        Sp::null(format!("label_{}", offset).parse::<Ident>().unwrap())
    };

    let mut offset = 0;
    let code = script.iter().map(|instr| {
        // For now we give every instruction a label and strip the unused ones later.
        let this_instr_label = Sp::null(ast::StmtLabel::Label(default_label(offset)));
        offset += instr_format.instr_size(instr);

        let Instr { time, opcode, args } = instr;

        match opcode_intrinsics.get(&opcode) {
            Some(IntrinsicInstrKind::Jmp) => {
                assert!(args.len() >= 2); // FIXME: print proper error
                assert!(args[2..].iter().all(|a| a.expect_raw().bits == 0), "unsupported data in padding of intrinsic");

                let dest_offset = instr_format.decode_label(args[0].expect_raw().bits);
                let dest_time = args[1].expect_raw().bits as i32;
                return Sp::null(ast::Stmt {
                    time: *time,
                    labels: vec![this_instr_label],
                    body: Sp::null(ast::StmtBody::Jump(ast::StmtGoto {
                        destination: default_label(dest_offset),
                        time: Some(dest_time),
                    })),
                })
            },
            // Some(IntrinsicInstrKind::InterruptLabel) => unimplemented!(),
            // Some(IntrinsicInstrKind::AssignOp(_, _)) => unimplemented!(),
            // Some(IntrinsicInstrKind::Binop(_, _)) => unimplemented!(),
            // Some(IntrinsicInstrKind::CondJmp(_, _)) => unimplemented!(),
            // Some(IntrinsicInstrKind::Push(_)) => unimplemented!(),
            None => {}, // continue
        }

        let ins_ident = {
            ty_ctx.opcode_names.get(&(*opcode as u32)).cloned()
                .unwrap_or_else(|| Ident::new_ins(*opcode as u32))
        };

        Sp::null(ast::Stmt {
            time: *time,
            labels: vec![this_instr_label],
            body: Sp::null(ast::StmtBody::Expr(Sp::null(Expr::Call {
                args: match ty_ctx.ins_signature(&ins_ident) {
                    Some(siggy) => raise_args(args, siggy, ty_ctx),
                    None => raise_args(args, &Signature::auto(args.len()), ty_ctx),
                },
                func: Sp::null(ins_ident),
            }))),
        })
    }).collect();
    code
}

fn raise_args(args: &[InstrArg], siggy: &Signature, ty_ctx: &TypeSystem) -> Vec<Sp<Expr>> {
    let encodings = siggy.arg_encodings();

    // FIXME opcode would be nice
    assert_eq!(args.len(), encodings.len(), "provided arg count does not match stdmap!"); // FIXME: return Error
    let mut out = encodings.iter().zip(args).map(|(enc, arg)| {
        let raw = arg.expect_raw();
        if raw.is_var {
            let (ty, id) = match enc {
                ArgEncoding::Padding |
                ArgEncoding::Color |
                ArgEncoding::Dword => (ScalarType::Int, raw.bits as i32),
                ArgEncoding::Float => {
                    let float_id = f32::from_bits(raw.bits);
                    if float_id != f32::round(float_id) {
                        fast_warning!(
                            "non-integer float variable [{}] in binary file will be truncated!",
                            float_id,
                        );
                    }
                    (ScalarType::Float, float_id as i32)
                },
            };
            Sp::null(Expr::Var(Sp::null(ty_ctx.gvar_to_ast(id, ty))))
        } else {
            match enc {
                ArgEncoding::Padding |
                ArgEncoding::Dword => Sp::null(Expr::from(raw.bits as i32)),
                ArgEncoding::Color => Sp::null(Expr::LitInt { value: raw.bits as i32, hex: true }),
                ArgEncoding::Float => Sp::null(Expr::from(f32::from_bits(raw.bits))),
            }
        }
    }).collect::<Vec<_>>();

    // drop early STD padding args from the end as long as they're zero
    for (enc, arg) in encodings.iter().zip(args).rev() {
        match (enc, arg) {
            (ArgEncoding::Padding, InstrArg::Raw(RawArg { bits: 0, .. })) => out.pop(),
            _ => break,
        };
    }
    out
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
    /// Like `goto label @ t;`
    ///
    /// Args: `label, t`.
    Jmp,
    // /// Like `interrupt[n]:`
    // ///
    // /// Args: `n`.
    // InterruptLabel,
    // /// Like `a = b;` or `a += b;`
    // ///
    // /// Args: `a, b`.
    // AssignOp(ast::AssignOpKind, ScalarType),
    // /// Like `a = b + c;`
    // ///
    // /// Args: `a, b, c`.
    // Binop(ast::BinopKind, ScalarType),
    // /// Like `if (a == c) goto label @ t;`
    // ///
    // /// Args: `a, b, label, t`
    // CondJmp(ast::BinopKind, ScalarType),
    // /// Like `_push(a);`
    // ///
    // /// Args: `a`
    // Push(ScalarType),
}

// TODO: * recompile ANM
// TODO: * TH06: Error on instruction after delete/static
// TODO: * TH06: Implicit delete

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

    /// Used by TH06 to indicate that an instruction must be the last instruction in the script.
    ///
    /// Unlike most formats, TH06 doesn't have a marker for the end of a script.
    /// Instead, either of the opcodes that "return" mark the end of the script.
    fn is_th06_anm_terminating_instr(&self, instr: &Instr) -> bool { false }

    /// Opcode of an instruction to automatically insert at the end of a function.
    /// E.g. `delete` for ANM and `return` for ECL.
    ///
    ///
    fn implicit_end_instruction(&self) -> Option<u32> { None }

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
    assert_eq!(size % 4, 0);
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
    pub fn param_mask(&self) -> u16 {
        if self.args.len() > 16 {
            panic!("Too many arguments in instruction!")
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
        mask
    }
}
