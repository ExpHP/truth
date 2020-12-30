use std::io::{self, Cursor, Write};
use std::collections::{HashMap};


use crate::error::{GatherErrorIteratorExt, CompileError};
use crate::pos::{Sp};
use crate::ast::{self, Expr};
use crate::ident::Ident;
use crate::signature::{Functions, Signature, ArgEncoding};

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
    pub is_param: bool,
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
    pub fn as_int(&self) -> i32 { self.bits as i32 }
    pub fn as_float(&self) -> f32 { f32::from_bits(self.bits) }
}

impl From<u32> for RawArg {
    fn from(x: u32) -> RawArg { RawArg { bits: x, is_param: false } }
}

impl From<i32> for RawArg {
    fn from(x: i32) -> RawArg { RawArg { bits: x as u32, is_param: false } }
}

impl From<f32> for RawArg {
    fn from(x: f32) -> RawArg { RawArg { bits: x.to_bits(), is_param: false } }
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
    functions: &Functions,
) -> Result<Vec<Instr>, CompileError> {
    let intrinsic_opcodes: HashMap<_, _> = format.intrinsic_opcode_pairs().into_iter().collect();

    let mut out = vec![];
    code.iter().map(|stmt| {
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
                    let opcode = match functions.resolve_aliases(func).as_ins() {
                        Some(opcode) => opcode,
                        None => return Err(error!(
                            message("cannot find instruction '{}'", func),
                            primary(func, "not an instruction"),
                        )),
                    };
                    let siggy = match functions.ins_signature(func) {
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

                    out.push(InstrOrLabel::Instr(Instr {
                        time: stmt.time,
                        opcode: opcode as _,
                        args: lower_args(func, args, &encodings)?,
                    }));
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

fn lower_args(func: &Sp<Ident>, args: &[Sp<Expr>], encodings: &[ArgEncoding]) -> Result<Vec<InstrArg>, CompileError> {
    fn arg_type_error(index: usize, expected: &'static str, func: &Sp<Ident>, arg: &Sp<Expr>) -> CompileError {
        error!(
            message("argument {} to '{}' has wrong type", index+1, func),
            primary(arg, "wrong type"),
            secondary(func, "expects {} in arg {}", expected, index+1),
        )
    }

    encodings.iter().zip(args).enumerate().map(|(index, (enc, arg))| match enc {
        ArgEncoding::Padding |
        ArgEncoding::Dword |
        ArgEncoding::Color => match **arg {
            Expr::LitInt { value, .. } => Ok(InstrArg::Raw(value.into())),
            Expr::LitFloat { .. } |
            Expr::LitString { .. } => Err(arg_type_error(index, "an int", func, arg)),
            _ => Err(unsupported(&arg.span)),
        },
        ArgEncoding::Float => match **arg {
            Expr::LitFloat { value, .. } => Ok(InstrArg::Raw(value.into())),
            Expr::LitInt { .. } |
            Expr::LitString { .. } => Err(arg_type_error(index, "a float", func, arg)),
            _ => Err(unsupported(&arg.span)),
        },
    }).collect_with_recovery()
}

pub fn raise_instrs_to_sub_ast(functions: &Functions, instr_format: &dyn InstrFormat, script: &[Instr]) -> Vec<Sp<ast::Stmt>> {
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
                let dest_time = args[1].expect_raw().as_int();
                return Sp::null(ast::Stmt {
                    time: *time,
                    labels: vec![this_instr_label],
                    body: Sp::null(ast::StmtBody::Jump(ast::StmtGoto {
                        destination: default_label(dest_offset),
                        time: Some(dest_time),
                    })),
                })
            },
            Some(IntrinsicInstrKind::InterruptLabel) => unimplemented!(),
            Some(IntrinsicInstrKind::AssignOp(_, _)) => unimplemented!(),
            Some(IntrinsicInstrKind::Binop(_, _)) => unimplemented!(),
            Some(IntrinsicInstrKind::CondJmp(_, _)) => unimplemented!(),
            Some(IntrinsicInstrKind::Push(_)) => unimplemented!(),
            None => {}, // continue
        }

        let ins_ident = {
            functions.opcode_names.get(&(*opcode as u32)).cloned()
                .unwrap_or_else(|| Ident::new_ins(*opcode as u32))
        };

        Sp::null(ast::Stmt {
            time: *time,
            labels: vec![this_instr_label],
            body: Sp::null(ast::StmtBody::Expr(Sp::null(Expr::Call {
                args: match functions.ins_signature(&ins_ident) {
                    Some(siggy) => raise_args(args, siggy),
                    None => raise_args(args, &crate::signature::Signature::auto(args.len())),
                },
                func: Sp::null(ins_ident),
            }))),
        })
    }).collect();
    code
}

fn raise_args(args: &[InstrArg], siggy: &Signature) -> Vec<Sp<Expr>> {
    let encodings = siggy.arg_encodings();

    // FIXME opcode would be nice
    assert_eq!(args.len(), encodings.len(), "provided arg count does not match stdmap!"); // FIXME: return Error
    let mut out = encodings.iter().zip(args).map(|(enc, arg)| {
        let raw = arg.expect_raw();
        match enc {
            ArgEncoding::Dword => Sp::null(Expr::from(raw.as_int())),
            ArgEncoding::Padding => Sp::null(Expr::from(raw.as_int())),
            ArgEncoding::Color => Sp::null(Expr::LitInt { value: raw.as_int(), hex: true }),
            ArgEncoding::Float => Sp::null(Expr::from(raw.as_float())),
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
    /// Like `interrupt[n]:`
    ///
    /// Args: `n`.
    InterruptLabel,
    /// Like `a = b;` or `a += b;`
    ///
    /// Args: `a, b`.
    AssignOp(ast::AssignOpKind, IntrinsicDataType),
    /// Like `a = b + c;`
    ///
    /// Args: `a, b, c`.
    Binop(ast::BinopKind, IntrinsicDataType),
    /// Like `if (a == c) goto label @ t;`
    ///
    /// Args: `a, b, label, t`
    CondJmp(ast::BinopKind, IntrinsicDataType),
    /// Like `_push(a);`
    ///
    /// Args: `a`
    Push(IntrinsicDataType),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntrinsicDataType { Int, Float }

pub trait InstrFormat {
    /// Get the number of bytes in the binary encoding of an instruction.
    fn instr_size(&self, instr: &Instr) -> usize;

    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, u16)>;

    /// Read a single script instruction from an input stream.
    ///
    /// Should return `None` when it reaches the marker that indicates the end of the script.
    /// When this occurs, it may leave the `Cursor` in an indeterminate state.
    fn read_instr(&self, f: &mut Cursor<&[u8]>) -> Option<Instr>;

    /// Write a single script instruction into an output stream.
    fn write_instr(&self, f: &mut dyn Write, instr: &Instr) -> io::Result<()>;

    /// Write a marker that goes after the final instruction in a function or script.
    fn write_terminal_instr(&self, f: &mut dyn Write) -> io::Result<()>;

    // Most formats encode labels as offsets from the beginning of the script (in which case
    // these functions are trivial), but early STD is a special snowflake that writes the
    // instruction *index* instead.
    fn encode_label(&self, offset: usize) -> u32;
    fn decode_label(&self, bits: u32) -> usize;
}
