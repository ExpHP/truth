use std::collections::{HashMap};

use crate::raw;
use crate::ast;
use crate::context;
use crate::error::{ErrorReported, GatherErrorIteratorExt};
use crate::llir::{InstrFormat, InstrAbi, ArgEncoding};
use crate::diagnostic::{Diagnostic, Emitter};
use crate::pos::{Span, Sp};
use crate::value::{ScalarType};

/// Maps opcodes to and from intrinsics.
#[derive(Debug, Default)] // Default is used by --no-intrinsics
pub struct IntrinsicInstrs {
    intrinsic_opcodes: HashMap<IntrinsicInstrKind, raw::Opcode>,
    intrinsic_abi_props: HashMap<IntrinsicInstrKind, IntrinsicInstrAbiParts>,
    opcode_intrinsics: HashMap<raw::Opcode, IntrinsicInstrKind>,
}

#[test]
fn fix_from_instr_format() {
    panic!("fix from_instr_format to add intrinsics from mapfiles");
}

#[test]
fn fix_null_span() {
    panic!("fix null span in IntrinsicInstrAbiProps::from_abi call (put spans on abis in Defs)");
}

impl IntrinsicInstrs {
    /// Build from the builtin intrinsics list of the format, and user mapfiles.
    ///
    /// This will perform verification of the signatures for each intrinsic.
    pub fn from_format_and_mapfiles(instr_format: &dyn InstrFormat, defs: &context::Defs, emitter: &dyn Emitter) -> Result<Self, ErrorReported> {
        let intrinsic_opcodes: HashMap<_, _> = instr_format.intrinsic_opcode_pairs().into_iter().collect();
        let opcode_intrinsics = intrinsic_opcodes.iter().map(|(&k, &v)| (v, k)).collect();

        let intrinsic_abi_props = {
            intrinsic_opcodes.iter()
                .map(|(&kind, &opcode)| {
                    let abi = defs.ins_abi(instr_format.language(), opcode)
                        .unwrap_or_else(|| unimplemented!("error when intrinsic has no ABI"));
                    let abi_props = IntrinsicInstrAbiParts::from_abi(kind, sp!(Span::NULL => abi))
                        .map_err(|e| emitter.as_sized().emit(e))?;
                    Ok((kind, abi_props))
                })
                .collect_with_recovery()?
        };
        Ok(IntrinsicInstrs { opcode_intrinsics, intrinsic_opcodes, intrinsic_abi_props })
    }

    pub(crate) fn get_opcode_and_abi_props(&self, intrinsic: IntrinsicInstrKind, span: Span, descr: &str) -> Result<(raw::Opcode, &IntrinsicInstrAbiParts), Diagnostic> {
        match self.intrinsic_opcodes.get(&intrinsic) {
            Some(&opcode) => Ok((opcode, &self.intrinsic_abi_props[&intrinsic])),
            None => Err(error!(
                message("feature not supported by format"),
                primary(span, "{} not supported in this game", descr),
            )),
        }
    }

    pub(crate) fn get_opcode_opt(&self, intrinsic: IntrinsicInstrKind) -> Option<raw::Opcode> {
        self.intrinsic_opcodes.get(&intrinsic).copied()
    }

    pub(crate) fn get_intrinsic_and_props(&self, opcode: raw::Opcode) -> Option<(IntrinsicInstrKind, &IntrinsicInstrAbiParts)> {
        self.opcode_intrinsics.get(&opcode)
            .map(|&kind| (kind, &self.intrinsic_abi_props[&kind]))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntrinsicInstrKind {
    /// Like `goto label @ t;` (and `goto label;`)
    ///
    /// Args: `label, t`, in an order defined by the ABI. (use [`JumpIntrinsicArgOrder`])
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
    /// Like `a = sin(b);` (or `a = -a;`, but it seems no formats actually have this?)
    ///
    /// This is not used for casts like `a = _S(b);`.  Casts have no explicit representation in
    /// a compiled script; they're just a fundamental part of how the engine reads variables.
    ///
    /// Args: `a, b`.
    Unop(ast::UnopKind, ScalarType),
    /// Like `if (--x) goto label @ t`.
    ///
    /// Args: `x, label, t`, in an order defined by the ABI. (use [`JumpIntrinsicArgOrder`])
    CountJmp,
    /// Like `if (a == c) goto label @ t;`
    ///
    /// Args: `a, b, label, t`, in an order defined by the ABI. (use [`JumpIntrinsicArgOrder`])
    CondJmp(ast::BinopKind, ScalarType),
    /// First part of a conditional jump in languages where it is comprised of 2 instructions.
    /// Sets a hidden compare register.
    ///
    /// Args: `a, b`
    CondJmp2A(ScalarType),
    /// Second part of a 2-instruction conditional jump in languages where it is comprised of 2 instructions.
    /// Jumps based on the hidden compare register.
    ///
    /// Args: `label, t`, in an order defined by the ABI. (use [`JumpIntrinsicArgOrder`])
    CondJmp2B(ast::BinopKind),
}

impl IntrinsicInstrKind {
    pub fn descr(&self) -> &'static str {
        match self {
            Self::Jmp { .. } => "unconditional jump",
            Self::InterruptLabel { .. } => "interrupt label",
            Self::AssignOp { .. } => "assign op",
            Self::Binop { .. } => "binary op",
            Self::Unop { .. } => "unary op",
            Self::CountJmp { .. } => "decrement jump",
            Self::CondJmp { .. } => "conditional jump",
            Self::CondJmp2A { .. } => "dedicated cmp",
            Self::CondJmp2B { .. } => "conditional jump after cmp",
        }
    }

    /// More precise than descr(), but allocates.
    pub fn heavy_descr(&self) -> String {
        match self {
            | Self::Jmp { .. }
            | Self::InterruptLabel { .. }
            | Self::CountJmp { .. }
            | Self::CondJmp2A { .. }
            => format!("{}", self.descr()),

            Self::AssignOp(op, _ty) => format!("{} op", op),
            Self::Binop(op, _ty) => format!("binary {} op", op),
            Self::Unop(op, _ty) => format!("unary {} op", op),
            Self::CondJmp(op, _ty) => format!("conditional ({}) jump", op),
            Self::CondJmp2B(op) => format!("conditional ({}) jump after cmp", op),
        }
    }
}

impl IntrinsicInstrKind {
    /// Add intrinsic pairs for binary operations in `a = b op c` form in their canonical order,
    /// which is `+, -, *, /, %`, with each operator having an int version and a float version.
    pub fn register_binary_ops(pairs: &mut Vec<(IntrinsicInstrKind, raw::Opcode)>, start: raw::Opcode) {
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
    pub fn register_assign_ops(pairs: &mut Vec<(IntrinsicInstrKind, raw::Opcode)>, start: raw::Opcode) {
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
    pub fn register_cond_jumps(pairs: &mut Vec<(IntrinsicInstrKind, raw::Opcode)>, start: raw::Opcode) {
        use ast::BinopKind as B;

        let mut opcode = start;
        for op in vec![B::Eq, B::Ne, B::Lt, B::Le, B::Gt, B::Ge] {
            for ty in vec![ScalarType::Int, ScalarType::Float] {
                pairs.push((IntrinsicInstrKind::CondJmp(op, ty), opcode));
                opcode += 1;
            }
        }
    }

    /// Register a sequence of six comparison based ops in the order used by EoSD ECL: `<, <=, ==, >, >=, !=`
    pub fn register_olde_ecl_comp_ops(
        pairs: &mut Vec<(IntrinsicInstrKind, raw::Opcode)>,
        start: raw::Opcode,
        kind_fn: impl Fn(ast::BinopKind) -> IntrinsicInstrKind,
    ) {
        use ast::BinopKind as B;

        let mut opcode = start;
        for op in vec![B::Lt, B::Le, B::Eq, B::Gt, B::Ge, B::Ne] {
            pairs.push((kind_fn(op), opcode));
            opcode += 1;
        }
    }
}

/// Streamlines the relationship between the ABI of an intrinsic and how it is expressed
/// in the AST.
///
/// One can think of this as defining the relationship between syntax sugar
/// (e.g. `if (a == 3) goto label`) and raw instruction syntax
/// (e.g. `ins_2(a, 3, offsetof(label), timeof(label))`), as properties like argument order
/// can vary between languages.
///
/// Having one of these indicates that the ABI has been validated to be compatible with
/// this intrinsic and we know where all of the pieces of the statement belong in the
/// raw, encoded argument list.
///
/// The `usize`s are all indices into the encoded argument list.
#[derive(Debug)]
pub struct IntrinsicInstrAbiParts {
    pub num_instr_args: usize,
    /// Number of padding args at the end
    pub padding: abi_parts::PaddingInfo,
    /// Indices of args that should use the same logic as arguments in `ins_` instruction-call syntax.
    pub plain_args: Vec<usize>,
    /// Indices of args that are known registers.  These show up in intrinsics.
    pub outputs: Vec<(usize, abi_parts::OutputArgMode)>,
    /// Location and arrangement of offset and time args.
    pub jump: Option<(usize, abi_parts::JumpArgOrder)>,
}

pub mod abi_parts {
    /// Indicates that the ABI contains this many padding dwords at the end,
    /// which cannot be represented in the AST if they are nonzero.
    #[derive(Debug, Copy, Clone)]
    pub struct PaddingInfo {
        pub index: usize,
        pub count: usize,
    }

    #[derive(Debug, Copy, Clone)]
    pub enum OutputArgMode {
        /// It's a float register, but is written to file as an integer. (used by EoSD ECL)
        FloatAsInt,
        /// The register is saved to file using the same datatype as it has in the AST.
        Natural,
    }

    #[derive(Debug, Copy, Clone)]
    pub enum JumpArgOrder {
        TimeLoc,
        LocTime,
        /// Always uses timeof(destination).
        Loc,
    }
}

fn intrinsic_abi_error(abi_span: Span, message: &str) -> Diagnostic {
    error!(
        message("bad ABI for intrinsic: {}", message),
        primary(abi_span, "{}", message),
    )
}

fn remove_first_where<T>(vec: &mut Vec<T>, pred: impl FnMut(&T) -> bool) -> Option<T> {
    match vec.iter().position(pred) {
        Some(index) => Some(vec.remove(index)),
        None => None,
    }
}

fn find_and_remove_padding(arg_encodings: &mut Vec<(usize, ArgEncoding)>, _abi_span: Span) -> Result<abi_parts::PaddingInfo, Diagnostic> {
    let mut count = 0;
    let mut first_index = arg_encodings.len();
    while let Some(&(index, ArgEncoding::Padding)) = arg_encodings.last() {
        // assumption that this func always runs first (nothing is deleted before us)
        assert_eq!(index, arg_encodings.len() - 1);

        arg_encodings.pop();
        count += 1;
        first_index = index;
    }
    Ok(abi_parts::PaddingInfo { count, index: first_index })
}

fn find_and_remove_jump(arg_encodings: &mut Vec<(usize, ArgEncoding)>, abi_span: Span) -> Result<(usize, abi_parts::JumpArgOrder), Diagnostic> {
    let offset_data = remove_first_where(arg_encodings, |&(_, enc)| enc == ArgEncoding::JumpOffset);
    let time_data = remove_first_where(arg_encodings, |&(_, enc)| enc == ArgEncoding::JumpTime);

    let offset_index = offset_data.map(|(index, _)| index);
    let time_index = time_data.map(|(index, _)| index);

    let offset_index = offset_index.ok_or_else(|| {
        intrinsic_abi_error(abi_span, "missing jump offset ('o')")
    })?;

    if let Some(time_index) = time_index {
        if time_index == offset_index + 1 {
            Ok((offset_index, abi_parts::JumpArgOrder::LocTime))
        } else if time_index + 1 == offset_index {
            Ok((time_index, abi_parts::JumpArgOrder::TimeLoc))
        } else {
            Err(intrinsic_abi_error(abi_span, "offset ('o') and time ('t') args must be consecutive"))
        }
    } else {
        Ok((offset_index, abi_parts::JumpArgOrder::Loc))
    }
}

fn remove_out_arg(arg_encodings: &mut Vec<(usize, ArgEncoding)>, abi_span: Span, ty_in_ast: ScalarType) -> Result<(usize, abi_parts::OutputArgMode), Diagnostic> {
    // it is expected that previous detect_and_remove functions have already removed everything before the out operand.
    let (index, encoding) = match arg_encodings.len() {
        0 => return Err(intrinsic_abi_error(abi_span, "not enough arguments")),
        _ => arg_encodings.remove(0),
    };
    match (ty_in_ast, encoding) {
        | (ScalarType::Int, ArgEncoding::Dword)
        | (ScalarType::Float, ArgEncoding::Float)
        => Ok((index, abi_parts::OutputArgMode::Natural)),

        | (ScalarType::Float, ArgEncoding::Dword)
        => Ok((index, abi_parts::OutputArgMode::FloatAsInt)),

        | (_, _)
        => Err(intrinsic_abi_error(abi_span, &format!("output arg has unexpected encoding ({})", encoding.descr()))),
    }
}

fn remove_plain_arg(arg_encodings: &mut Vec<(usize, ArgEncoding)>, abi_span: Span, ty_in_ast: ScalarType) -> Result<usize, Diagnostic> {
    let (index, encoding) = match arg_encodings.len() {
        0 => return Err(intrinsic_abi_error(abi_span, "not enough arguments")),
        _ => arg_encodings.remove(0),
    };
    match (ty_in_ast, encoding) {
        | (ScalarType::Int, ArgEncoding::Dword)
        | (ScalarType::Float, ArgEncoding::Float)
        => Ok(index),

        | (_, _)
        => Err(intrinsic_abi_error(abi_span, &format!("ABI input arg has unexpected encoding ({})", encoding.descr()))),
    }
}

impl IntrinsicInstrAbiParts {
    pub fn from_abi(intrinsic: IntrinsicInstrKind, abi: Sp<&InstrAbi>) -> Result<Self, Diagnostic> {
        use IntrinsicInstrKind as I;

        let mut encodings = abi.arg_encodings().enumerate().collect::<Vec<_>>();
        let num_instr_args = encodings.len();

        let padding = find_and_remove_padding(&mut encodings, abi.span)?;
        let mut out = IntrinsicInstrAbiParts {
            num_instr_args, padding,
            plain_args: vec![], outputs: vec![], jump: None,
        };

        match intrinsic {
            I::Jmp => {
                out.jump = Some(find_and_remove_jump(&mut encodings, abi.span)?);
            },
            I::InterruptLabel => {
                out.plain_args.push(remove_plain_arg(&mut encodings, abi.span, ScalarType::Int)?);
            }
            I::AssignOp(_op, ty) => {
                out.outputs.push(remove_out_arg(&mut encodings, abi.span, ty)?);
                out.plain_args.push(remove_plain_arg(&mut encodings, abi.span, ty)?);
            },
            I::Binop(op, arg_ty) => {
                let out_ty = ast::Expr::binop_ty_from_arg_ty(op, arg_ty);
                out.outputs.push(remove_out_arg(&mut encodings, abi.span, out_ty)?);
                out.plain_args.push(remove_plain_arg(&mut encodings, abi.span, arg_ty)?);
                out.plain_args.push(remove_plain_arg(&mut encodings, abi.span, arg_ty)?);
            },
            I::Unop(_op, ty) => {
                out.outputs.push(remove_out_arg(&mut encodings, abi.span, ty)?);
                out.plain_args.push(remove_plain_arg(&mut encodings, abi.span, ty)?);
            },
            I::CountJmp => {
                out.jump = Some(find_and_remove_jump(&mut encodings, abi.span)?);
                out.outputs.push(remove_out_arg(&mut encodings, abi.span, ScalarType::Int)?);
            },
            I::CondJmp(_op, ty) => {
                out.jump = Some(find_and_remove_jump(&mut encodings, abi.span)?);
                out.plain_args.push(remove_plain_arg(&mut encodings, abi.span, ty)?);
                out.plain_args.push(remove_plain_arg(&mut encodings, abi.span, ty)?);
            },
            I::CondJmp2A(ty) => {
                out.plain_args.push(remove_plain_arg(&mut encodings, abi.span, ty)?);
                out.plain_args.push(remove_plain_arg(&mut encodings, abi.span, ty)?);
            },
            I::CondJmp2B(_op) => {
                out.jump = Some(find_and_remove_jump(&mut encodings, abi.span)?);
            },
        };

        if let Some(&(index, encoding)) = encodings.get(0) {
            return Err(intrinsic_abi_error(abi.span, &format!("unexpected {} arg at index {}", encoding.descr(), index + 1)));
        }
        Ok(out)
    }
}
