use indexmap::IndexMap;

use crate::raw;
use crate::ast;
use crate::context;
use crate::context::defs::InstrAbiLoc;
use crate::error::{ErrorReported, GatherErrorIteratorExt};
use crate::llir::{LanguageHooks, InstrAbi, ArgEncoding};
use crate::diagnostic::{Diagnostic, Emitter};
use crate::pos::{Span, Sp};
use crate::value::{ScalarType};

/// Maps opcodes to and from intrinsics.
#[derive(Debug, Default)] // Default is used by --no-intrinsics
pub struct IntrinsicInstrs {
    intrinsic_opcodes: IndexMap<IntrinsicInstrKind, raw::Opcode>,
    intrinsic_abi_props: IndexMap<IntrinsicInstrKind, IntrinsicInstrAbiParts>,
    opcode_intrinsics: IndexMap<raw::Opcode, Sp<IntrinsicInstrKind>>,
}

impl IntrinsicInstrs {
    /// Build from the builtin intrinsics list of the format, and user mapfiles.
    ///
    /// This will perform verification of the signatures for each intrinsic.
    pub fn from_format_and_mapfiles(instr_format: &dyn LanguageHooks, defs: &context::Defs, emitter: &dyn Emitter) -> Result<Self, ErrorReported> {
        let native_pairs = instr_format.intrinsic_opcode_pairs();
        let iter_pairs = || {
            native_pairs.iter().copied()
                .map(|(intrinsic, opcode)| (opcode, sp!(intrinsic))) // dummy spans for builtin defs
                .chain(defs.iter_user_intrinsics(instr_format.language()))
        };
        // duplicates can be crazy so we iterate twice instead of making one map from the other
        let opcode_intrinsics = iter_pairs().collect::<IndexMap<_, _>>();
        let intrinsic_opcodes = iter_pairs().map(|(k, v)| (v.value, k)).collect::<IndexMap<_, _>>();

        let intrinsic_abi_props = {
            opcode_intrinsics.iter()
                .map(|(&opcode, &kind)| {
                    let (abi, abi_loc) = defs.ins_abi(instr_format.language(), opcode)
                        .ok_or_else(|| emitter.as_sized().emit(error!(
                            message("opcode {} is an intrinsic but has no signature", opcode),
                            primary(kind, "defined as an intrinsic here"),
                        )))?;
                    let abi_props = IntrinsicInstrAbiParts::from_abi(kind.value, abi, abi_loc)
                        .map_err(|e| emitter.as_sized().emit(e))?;
                    Ok((kind.value, abi_props))
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
            .map(|&kind| (kind.value, &self.intrinsic_abi_props[&kind.value]))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(strum::EnumDiscriminants)]
#[strum_discriminants(derive(strum::Display, strum::EnumString))]
#[strum_discriminants(name(IntrinsicInstrTag))]
pub enum IntrinsicInstrKind {
    /// Like `goto label @ t;` (and `goto label;`)
    #[strum_discriminants(strum(serialize = "Jmp"))]
    Jmp,

    /// Like `interrupt[n]:`
    #[strum_discriminants(strum(serialize = "Interrupt"))]
    InterruptLabel,

    /// Like `a = b;` or `a += b;`
    #[strum_discriminants(strum(serialize = "AssignOp"))]
    AssignOp(ast::AssignOpKind, ScalarType),

    /// Like `a = b + c;`
    #[strum_discriminants(strum(serialize = "BinOp"))]
    BinOp(ast::BinOpKind, ScalarType),

    /// Like `a = sin(b);` (or `a = -a;`, but it seems no formats actually have this?)
    ///
    /// This is not used for casts like `a = _S(b);`.  Casts have no explicit representation in
    /// a compiled script; they're just a fundamental part of how the engine reads variables.
    #[strum_discriminants(strum(serialize = "UnOp"))]
    UnOp(ast::UnOpKind, ScalarType),

    /// Like `if (--x) goto label @ t`.
    #[strum_discriminants(strum(serialize = "CountJmp"))]
    CountJmp,

    /// Like `if (a == c) goto label @ t;`
    #[strum_discriminants(strum(serialize = "CondJmp"))]
    CondJmp(ast::BinOpKind, ScalarType),

    /// First part of a conditional jump in languages where it is comprised of 2 instructions.
    /// Sets a hidden compare register.
    #[strum_discriminants(strum(serialize = "DedicatedCmp"))]
    CondJmp2A(ScalarType),

    /// Second part of a 2-instruction conditional jump in languages where it is comprised of 2 instructions.
    /// Jumps based on the hidden compare register.
    #[strum_discriminants(strum(serialize = "DedicatedCmpJmp"))]
    CondJmp2B(ast::BinOpKind),

    /// Calls a sub in EoSD.  Takes two immediates for `I0` and `F0`.
    #[strum_discriminants(strum(serialize = "CallEosd"))]
    CallEosd,
}

impl IntrinsicInstrKind {
    pub fn descr(&self) -> &'static str {
        match self {
            Self::Jmp { .. } => "unconditional jump",
            Self::CallEosd { .. } => "call (EoSD)",
            Self::InterruptLabel { .. } => "interrupt label",
            Self::AssignOp { .. } => "assign op",
            Self::BinOp { .. } => "binary op",
            Self::UnOp { .. } => "unary op",
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
            | Self::CallEosd { .. }
            | Self::InterruptLabel { .. }
            | Self::CountJmp { .. }
            | Self::CondJmp2A { .. }
            => format!("{}", self.descr()),

            Self::AssignOp(op, _ty) => format!("{} op", op),
            Self::BinOp(op, _ty) => format!("binary {} op", op),
            Self::UnOp(op, _ty) => format!("unary {} op", op),
            Self::CondJmp(op, _ty) => format!("conditional ({}) jump", op),
            Self::CondJmp2B(op) => format!("conditional ({}) jump after cmp", op),
        }
    }
}

impl IntrinsicInstrKind {
    /// Add intrinsic pairs for binary operations in `a = b op c` form in their canonical order,
    /// which is `+, -, *, /, %`, with each operator having an int version and a float version.
    pub fn register_binary_ops(pairs: &mut Vec<(IntrinsicInstrKind, raw::Opcode)>, start: raw::Opcode) {
        use ast::BinOpKind as B;

        let mut opcode = start;
        for op in vec![B::Add, B::Sub, B::Mul, B::Div, B::Rem] {
            for ty in vec![ScalarType::Int, ScalarType::Float] {
                pairs.push((IntrinsicInstrKind::BinOp(op, ty), opcode));
                opcode += 1;
            }
        }
    }

    /// Like [`Self::register_binary_ops`] but instead of alternating int/float pairs it's just one type.
    pub fn register_binary_ops_of_type(pairs: &mut Vec<(IntrinsicInstrKind, raw::Opcode)>, start: raw::Opcode, ty: ScalarType) {
        use ast::BinOpKind as B;

        let mut opcode = start;
        for op in vec![B::Add, B::Sub, B::Mul, B::Div, B::Rem] {
            pairs.push((IntrinsicInstrKind::BinOp(op, ty), opcode));
            opcode += 1;
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
        use ast::BinOpKind as B;

        let mut opcode = start;
        for op in vec![B::Eq, B::Ne, B::Lt, B::Le, B::Gt, B::Ge] {
            for ty in vec![ScalarType::Int, ScalarType::Float] {
                pairs.push((IntrinsicInstrKind::CondJmp(op, ty), opcode));
                opcode += 1;
            }
        }
    }

    /// Register a sequence of six comparison based ops in the order used by EoSD ECL: `<, <=, ==, >, >=, !=`
    pub fn register_eosd_ecl_comp_ops(
        pairs: &mut Vec<(IntrinsicInstrKind, raw::Opcode)>,
        start: raw::Opcode,
        kind_fn: impl Fn(ast::BinOpKind) -> IntrinsicInstrKind,
    ) {
        use ast::BinOpKind as B;

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
    /// Location of a called sub id (an index or a string name).
    pub sub_id: Option<usize>
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

fn intrinsic_abi_error(abi_loc: &InstrAbiLoc, message: &str) -> Diagnostic {
    let mut diag = error!(message("bad ABI for intrinsic: {}", message));
    match abi_loc {
        InstrAbiLoc::Span(span) => diag.primary(span, message.to_string()),
        InstrAbiLoc::CoreMapfile { language, opcode, abi_str } => {
            diag.note(format!("the built-in signature for {} opcode {} is \"{}\"", language.descr(), opcode, abi_str))
        },
    };
    diag
}

fn remove_first_where<T>(vec: &mut Vec<T>, pred: impl FnMut(&T) -> bool) -> Option<T> {
    match vec.iter().position(pred) {
        Some(index) => Some(vec.remove(index)),
        None => None,
    }
}

fn find_and_remove_padding(arg_encodings: &mut Vec<(usize, ArgEncoding)>, _abi_loc: &InstrAbiLoc) -> Result<abi_parts::PaddingInfo, Diagnostic> {
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

fn find_and_remove_jump(arg_encodings: &mut Vec<(usize, ArgEncoding)>, abi_span: &InstrAbiLoc) -> Result<(usize, abi_parts::JumpArgOrder), Diagnostic> {
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

fn find_and_remove_sub_id(arg_encodings: &mut Vec<(usize, ArgEncoding)>, abi_span: &InstrAbiLoc) -> Result<usize, Diagnostic> {
    let data = remove_first_where(arg_encodings, |&(_, enc)| enc == ArgEncoding::Sub);
    let index = data.map(|(index, _)| index);
    let index = index.ok_or_else(|| {
        intrinsic_abi_error(abi_span, "missing sub id ('E')")
    })?;
    Ok(index)
}

fn remove_out_arg(arg_encodings: &mut Vec<(usize, ArgEncoding)>, abi_span: &InstrAbiLoc, ty_in_ast: ScalarType) -> Result<(usize, abi_parts::OutputArgMode), Diagnostic> {
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

fn remove_plain_arg(arg_encodings: &mut Vec<(usize, ArgEncoding)>, abi_span: &InstrAbiLoc, ty_in_ast: ScalarType) -> Result<usize, Diagnostic> {
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
    pub fn from_abi(intrinsic: IntrinsicInstrKind, abi: &InstrAbi, abi_loc: &InstrAbiLoc) -> Result<Self, Diagnostic> {
        use IntrinsicInstrKind as I;

        let mut encodings = abi.arg_encodings().enumerate().collect::<Vec<_>>();
        let num_instr_args = encodings.len();

        let padding = find_and_remove_padding(&mut encodings, abi_loc)?;
        let mut out = IntrinsicInstrAbiParts {
            num_instr_args, padding,
            plain_args: vec![], outputs: vec![], jump: None, sub_id: None,
        };

        match intrinsic {
            I::Jmp => {
                out.jump = Some(find_and_remove_jump(&mut encodings, abi_loc)?);
            },
            I::CallEosd => {
                out.sub_id = Some(find_and_remove_sub_id(&mut encodings, abi_loc)?);
                out.plain_args.push(remove_plain_arg(&mut encodings, abi_loc, ScalarType::Int)?);
                out.plain_args.push(remove_plain_arg(&mut encodings, abi_loc, ScalarType::Float)?);
            },
            I::InterruptLabel => {
                out.plain_args.push(remove_plain_arg(&mut encodings, abi_loc, ScalarType::Int)?);
            }
            I::AssignOp(_op, ty) => {
                out.outputs.push(remove_out_arg(&mut encodings, abi_loc, ty)?);
                out.plain_args.push(remove_plain_arg(&mut encodings, abi_loc, ty)?);
            },
            I::BinOp(op, arg_ty) => {
                let out_ty = ast::Expr::binop_ty_from_arg_ty(op, arg_ty);
                out.outputs.push(remove_out_arg(&mut encodings, abi_loc, out_ty)?);
                out.plain_args.push(remove_plain_arg(&mut encodings, abi_loc, arg_ty)?);
                out.plain_args.push(remove_plain_arg(&mut encodings, abi_loc, arg_ty)?);
            },
            I::UnOp(_op, ty) => {
                out.outputs.push(remove_out_arg(&mut encodings, abi_loc, ty)?);
                out.plain_args.push(remove_plain_arg(&mut encodings, abi_loc, ty)?);
            },
            I::CountJmp => {
                out.jump = Some(find_and_remove_jump(&mut encodings, abi_loc)?);
                out.outputs.push(remove_out_arg(&mut encodings, abi_loc, ScalarType::Int)?);
            },
            I::CondJmp(_op, ty) => {
                out.jump = Some(find_and_remove_jump(&mut encodings, abi_loc)?);
                out.plain_args.push(remove_plain_arg(&mut encodings, abi_loc, ty)?);
                out.plain_args.push(remove_plain_arg(&mut encodings, abi_loc, ty)?);
            },
            I::CondJmp2A(ty) => {
                out.plain_args.push(remove_plain_arg(&mut encodings, abi_loc, ty)?);
                out.plain_args.push(remove_plain_arg(&mut encodings, abi_loc, ty)?);
            },
            I::CondJmp2B(_op) => {
                out.jump = Some(find_and_remove_jump(&mut encodings, abi_loc)?);
            },
        };

        if let Some(&(index, encoding)) = encodings.get(0) {
            return Err(intrinsic_abi_error(abi_loc, &format!("unexpected {} arg at index {}", encoding.descr(), index + 1)));
        }
        Ok(out)
    }
}

// =============================================================================

#[derive(Debug, thiserror::Error)]
#[error("{}", .message)]
pub struct ParseIntrinsicError {
    message: String,
}

impl From<strum::ParseError> for ParseIntrinsicError {
    fn from(e: strum::ParseError) -> Self { ParseIntrinsicError { message: format!("{}", e) }}
}

/// Parse from a mapfile string.
impl std::str::FromStr for IntrinsicInstrKind {
    type Err = ParseIntrinsicError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use IntrinsicInstrTag as Tag;
        use IntrinsicInstrKind as IKind;

        let fail = |msg: &str| ParseIntrinsicError { message: msg.to_string() };

        let (prefix, mut args) = if let Some(lparen_index) = s.find("(") {
            if s.chars().next_back() != Some(')') {
                return Err(fail("missing ')'"));
            }
            let (before_paren, at_paren) = s.split_at(lparen_index);
            let args = at_paren[1..at_paren.len() - 1].split(",").collect::<Vec<_>>();
            (before_paren, args)
        } else {
            return Err(fail("missing '('"));
        };

        if args == [""] {
            args.pop();
        }

        let parse_type = |s: &str| match s {
            "int" => Ok(ScalarType::Int),
            "float" => Ok(ScalarType::Float),
            _ => Err(fail("bad type; expected int or float"))
        };

        let tag = prefix.parse::<Tag>().map_err(|s| fail(&s.to_string()))?;
        let mut args = args.into_iter();
        let mut next_arg = || {
            args.next().ok_or_else(|| fail("not enough arguments to intrinsic name"))
        };
        let out = match tag {
            Tag::Jmp => IKind::Jmp,
            Tag::CallEosd => IKind::CallEosd,
            Tag::InterruptLabel => IKind::InterruptLabel,
            Tag::AssignOp => IKind::AssignOp(next_arg()?.parse()?, parse_type(next_arg()?)?),
            Tag::BinOp => IKind::BinOp(next_arg()?.parse()?, parse_type(next_arg()?)?),
            Tag::UnOp => IKind::UnOp(next_arg()?.parse()?, parse_type(next_arg()?)?),
            Tag::CountJmp => IKind::CountJmp,
            Tag::CondJmp => IKind::CondJmp(next_arg()?.parse()?, parse_type(next_arg()?)?),
            Tag::CondJmp2A => IKind::CondJmp2A(parse_type(next_arg()?)?),
            Tag::CondJmp2B => IKind::CondJmp2B(next_arg()?.parse()?),
        };

        if let Some(_) = args.next() {
            Err(fail("too many arguments to intrinsic name"))
        } else {
            Ok(out)
        }
    }
}

impl std::fmt::Display for IntrinsicInstrKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use IntrinsicInstrKind as IKind;

        let render_ty = |ty| match ty {
            &ScalarType::Int => "int",
            &ScalarType::Float => "float",
            _ => unreachable!(),
        };
        let tag = IntrinsicInstrTag::from(self);
        match self {
            IKind::Jmp => write!(f, "{}()", tag),
            IKind::CallEosd => write!(f, "{}()", tag),
            IKind::InterruptLabel => write!(f, "{}()", tag),
            IKind::AssignOp(op, ty) => write!(f, "{}({},{})", tag, op, render_ty(ty)),
            IKind::BinOp(op, ty) => write!(f, "{}({},{})", tag, op, render_ty(ty)),
            IKind::UnOp(op, ty) => write!(f, "{}({},{})", tag, op, render_ty(ty)),
            IKind::CountJmp => write!(f, "{}()", tag),
            IKind::CondJmp(op, ty) => write!(f, "{}({},{})", tag, op, render_ty(ty)),
            IKind::CondJmp2A(ty) => write!(f, "{}({})", tag, render_ty(ty)),
            IKind::CondJmp2B(op) => write!(f, "{}({})", tag, op),
        }
    }
}
