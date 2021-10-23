use std::collections::{HashMap};

use crate::raw;
use crate::ast;
use crate::llir::{InstrAbi, ArgEncoding};
use crate::diagnostic::{Diagnostic};
use crate::pos::{Span};
use crate::value::{ScalarType};

/// Maps opcodes to and from intrinsics.
#[derive(Default)]
pub struct IntrinsicInstrs {
    intrinsic_opcodes: HashMap<IntrinsicInstrKind, raw::Opcode>,
    opcode_intrinsics: HashMap<raw::Opcode, IntrinsicInstrKind>,
}
impl IntrinsicInstrs {
    pub fn from_pairs(pairs: impl IntoIterator<Item=(IntrinsicInstrKind, raw::Opcode)>) -> Self {
        let intrinsic_opcodes: HashMap<_, _> = pairs.into_iter().collect();
        let opcode_intrinsics = intrinsic_opcodes.iter().map(|(&k, &v)| (v, k)).collect();
        IntrinsicInstrs { opcode_intrinsics, intrinsic_opcodes }
    }

    pub fn get_opcode(&self, intrinsic: IntrinsicInstrKind, span: Span, descr: &str) -> Result<raw::Opcode, Diagnostic> {
        match self.intrinsic_opcodes.get(&intrinsic) {
            Some(&opcode) => Ok(opcode),
            None => Err(error!(
                message("feature not supported by format"),
                primary(span, "{} not supported in this game", descr),
            )),
        }
    }

    pub fn get_opcode_opt(&self, intrinsic: IntrinsicInstrKind) -> Option<raw::Opcode> {
        self.intrinsic_opcodes.get(&intrinsic).copied()
    }

    pub fn get_intrinsic(&self, opcode: raw::Opcode) -> Option<IntrinsicInstrKind> {
        self.opcode_intrinsics.get(&opcode).copied()
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
    /// The abomination in EoSD known as a "conditional call."
    CondCall(ast::BinopKind),
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
            Self::CondCall { .. } => "conditional comparison",
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


/// Helper for inspecting the signature of a jump related intrinsic to determine the
/// order of the arguments.  (which varies from language to language)
pub struct JumpIntrinsicArgOrder<T> {
    pub offset: T,
    /// This will be `None` if the signature has no time arguments. (basically just TH06 ANM)
    pub time: Option<T>,
    /// The rest of the args in the order they were found.
    pub other_args: Vec<T>,
    /// Encodings of `other_args`.
    pub other_arg_encodings: Vec<ArgEncoding>,
}

impl<T> JumpIntrinsicArgOrder<T> {
    /// Pull out the items in an iterator that correspond to jump arguments.
    pub fn from_iter(args: impl ExactSizeIterator<Item=T>, abi: &InstrAbi, expected_extra_args: usize) -> Result<Self, Diagnostic> {
        if args.len() != abi.arg_encodings().len() {
            return Err(error!(
                "jump intrinsic got {} args but its signature has {}. (signature is probably wrong)",
                args.len(), abi.arg_encodings().len(),
            ));
        }

        let mut offset = None;
        let mut time = None;
        let mut other_args = vec![];
        let mut other_arg_encodings = vec![];
        for (arg, encoding) in args.zip(abi.arg_encodings()) {
            match encoding {
                ArgEncoding::JumpOffset => offset = Some(arg),
                ArgEncoding::JumpTime => time = Some(arg),
                _ => {
                    other_args.push(arg);
                    other_arg_encodings.push(encoding);
                },
            }
        }

        if other_args.len() != expected_extra_args {
            let hint = if other_args.len() == expected_extra_args + 1 && time.is_none() {
                r#" (possibly missing "t" in signature)"#
            } else {
                ""
            };
            return Err(error!(
                "jump intrinsic expected {} non-jump args but got {}{}",
                expected_extra_args, other_args.len(), hint
            ));
        }

        match offset {
            Some(offset) => Ok(JumpIntrinsicArgOrder { offset, time, other_args, other_arg_encodings }),
            _ => Err(error!("jump intrinsic signature is missing offset argument")),
        }
    }

    /// Use the given signature to convert this into a list of arguments.
    ///
    /// `other_arg_encodings` does not need to be populated.
    pub fn into_vec(self, abi: &InstrAbi) -> Result<Vec<T>, Diagnostic>
    where T: Clone, // HACK, shouldn't be necessary, we're only cloning a const None
    {
        let nargs = abi.arg_encodings().len();

        let mut out_things = vec![None; nargs];

        // "Clever." Use JumpIntrinsicArgs::from_iter on an iterator of `Item=&mut Option<T>`.
        // Then assign those Options to fill in the vec.
        let mut out_jump = JumpIntrinsicArgOrder::from_iter(out_things.iter_mut(), abi, self.other_args.len())?;
        *out_jump.offset = Some(self.offset);
        for (out_time, time) in out_jump.time.iter_mut().zip(self.time) {
            **out_time = Some(time);
        }
        for (out_arg, arg) in out_jump.other_args.iter_mut().zip(self.other_args) {
            **out_arg = Some(arg);
        }

        // all items should be filled now
        Ok(out_things.into_iter().map(|opt| opt.unwrap()).collect())
    }
}


// XXX
impl IntrinsicInstrKind {
    fn validate_abi(&self, abi: &InstrAbi) -> Result<(), Diagnostic> {
//         use IntrinsicInstrKind as I;
//         use ArgEncoding as E;
//         use crate::llir::ArgEncoding;
//
//         let check_operator_out_encoding = |encoding: ArgEncoding, op_ty: ScalarType, op_class: ast::OpClass| {
//             let is_suitable = match op_ty {
//                 ScalarType::Int => matches!(encoding, E::Dword),
//                 ScalarType::Float => matches!(encoding, E::Dword | E::Float),  // EoSD ECL uses ints
//                 ScalarType::String => false,
//             };
//             if !is_suitable {
//                 return Err(error!("bad output type for {} {} {}", op_ty.descr(), op_class.descr(), self.descr()));
//             }
//             Ok(())
//         };
//
//         let check_op_arg_encoding = |encoding: ArgEncoding, arg_ty: ScalarType, op_class: ast::OpClass| {
//             match (arg_ty, encoding) {
//                 | (ScalarType::Int, E::Dword)
//                 | (ScalarType::Float, E::Float)
//                 => Ok(()),
//                 // "this" instead of arg_ty.descr() because of casts
//                 _ => Err(error!("bad arg type for this {} {}", op_class.descr(), self.descr())),
//             }
//         };
//
//         let check_num_args = |encodings: &[ArgEncoding], expected: usize| {
//             if encodings.len() != expected {
//                 return Err(error!("wrong number of args for {} (expected {})", self.descr(), expected));
//             }
//             Ok(())
//         };
//
//         let encodings  = abi.arg_encodings.collect::<Vec<_>>();
//         match *self {
//             I::Jmp => {
//                 // this can show up in early STD
//                 let mut encodings = encodings;
//                 while encodings.last() == Some(&E::Padding) {
//                     encodings.pop();
//                 }
//                 if !encodings.contains(&E::JumpOffset) {
//                     return Err(error!("signature for {} is missing offset argument", self.descr()));
//                 }
//
//                 for encoding in encodings {
//                     if encoding != E::JumpOffset && encoding != E::JumpTime {
//                         return Err(error!("signature for {} has unexpected {}", self.descr(), encoding.descr()));
//                     }
//                 }
//             },
//             I::InterruptLabel => {
//                 if encodings != vec![E::Dword] {
//                     return Err(error!("signature for {} must be a single integer", self.descr()));
//                 }
//             },
//             I::AssignOp(op, ty) => {
//                 check_num_args(&encodings, 2)?;
//                 check_operator_out_encoding(encodings[0], ty, op.class())?;
//                 let arg_ty = ty;
//                 for encoding in &encodings[1..] {
//                     check_op_arg_encoding(encoding, arg_ty, op.class())?;
//                 }
//             },
//             I::Binop(op, ty) => {
//                 check_num_args(&encodings, 3);
//                 check_operator_out_encoding(encodings[0], ty, op.class())?;
//                 let arg_ty = ty;
//                 for encoding in &encodings[1..] {
//                     check_op_arg_encoding(encoding, arg_ty, op.class())?;
//                 }
//             },
//             I::Unop(op, ty) => {
//                 check_num_args(&encodings, 2)?;
//                 check_operator_out_encoding(encodings[0], ty, op.class())?;
//                 let arg_ty = match op {
//                     ast::UnopKind::CastI => ScalarType::Float,
//                     ast::UnopKind::CastF => ScalarType::Int,
//                     _ => ty,
//                 };
//                 for encoding in &encodings[1..] {
//                     check_op_arg_encoding(encoding, arg_ty, op.class())?;
//                 }
//             },
//             I::CountJmp => panic!(),
//             I::CondJmp(op, ty) => panic!(),
//             I::CondJmp2A(ty) => {
//                 check_num_args(&encodings, 2)?;
//             },
//             I::CondJmp2B(op) => panic!(),
//             I::CondCall(op) => panic!(),
//         }
        panic!();
    }
}
