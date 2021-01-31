use anyhow::Context;
use std::collections::HashMap;
use crate::error::{CompileError, SimpleError};
use crate::ident::{Ident, GensymContext};
use crate::eclmap::Eclmap;
use crate::ast;
use crate::var::{Variables, VarId, RegId};
use crate::pos::{Span, Sp};

// FIXME: The overall design of this is messy and kind of dumb.
//  * `RegsAndInstrs` was the original TypeSystem, which only deals with global stuff.
//    This was sufficient for STD.
//    Its responsibilities were not very clear (it was basically supposed to be "the ECLMAP but not")
//    and a bunch of fields are marked `pub` when they shouldn't be. (easily fixable, I just haven't)
//  * `Variables` arose as sort of a separate thing while working on ANM.
//    It tracks information on local variables. Originally it was separate from TypeSystem but that
//    seemed cumbersome so I tacked it on.
//  * Which methods are provided on which struct is a bit messy simply because I haven't really
//    put a lot of thought into it.
#[derive(Debug, Clone, Default)]
pub struct TypeSystem {
    pub regs_and_instrs: RegsAndInstrs,
    pub variables: Variables,
    pub gensym: GensymContext,
}

/// Information about raw instructions and registers, usually derived from a mapfile.
#[derive(Debug, Clone, Default)]
pub struct RegsAndInstrs {
    /// List of all loaded mapfiles
    mapfiles: Vec<std::path::PathBuf>,

    // Functions
    func_aliases: HashMap<Ident, Ident>,

    // Instructions
    opcode_signatures: HashMap<u16, Signature>,
    pub opcode_names: HashMap<u16, Ident>,

    // Registers
    pub reg_default_types: HashMap<RegId, ScalarType>,
    pub reg_map: HashMap<Ident, RegId>,
    pub reg_names: HashMap<RegId, Ident>,
}

impl TypeSystem {
    pub fn new() -> Self { Self::default() }

    /// Add info from an eclmap.  Its path (if one is provided) is recorded in order to emit
    /// import directives into a decompiled script file.
    pub fn extend_from_eclmap(&mut self, path: Option<&std::path::Path>, eclmap: &Eclmap) {
        if let Some(path) = path {
            self.regs_and_instrs.mapfiles.push(path.to_owned());
        }

        for (&opcode, name) in &eclmap.ins_names {
            self.regs_and_instrs.opcode_names.insert(opcode as u16, name.clone());
            self.regs_and_instrs.func_aliases.insert(name.clone(), Ident::new_ins(opcode as u16));
        }
        for (&opcode, value) in &eclmap.ins_signatures {
            self.regs_and_instrs.add_signature(opcode as u16, value).unwrap(); // XXX XXX FIXME propagate to caller
        }
        for (&reg, name) in &eclmap.gvar_names {
            self.regs_and_instrs.reg_names.insert(RegId(reg), name.clone());
            self.regs_and_instrs.reg_map.insert(name.clone(), RegId(reg));
            self.variables.declare_global_register_alias(name.clone(), RegId(reg));
        }
        for (&id, value) in &eclmap.gvar_types {
            let ty = match &value[..] {
                "%" => ScalarType::Float,
                "$" => ScalarType::Int,
                _ => {
                    fast_warning!(
                        "In mapfile: Ignoring invalid variable type '{}' for gvar {}",
                        value, id,
                    );
                    continue;
                },
            };
            self.regs_and_instrs.reg_default_types.insert(RegId(id), ty);
        }
    }

    /// Get the effective type of a variable at a place where it is referenced.
    ///
    /// This can be different from the variable's innate type.  E.g. an integer global `I0` can be
    /// cast as a float using `%I0`.
    pub fn var_read_type_from_ast(&self, var: &Sp<ast::Var>) -> Result<ScalarType, CompileError> {
        match var.value {
            ast::Var::Named { .. } => panic!("this method requires name resolution! (got: {:?})", var),

            ast::Var::Resolved { ty_sigil, var_id } => {
                if let Some(ty_sigil) = ty_sigil {
                    return Ok(ty_sigil.into()); // explicit type from user
                }
                self.var_default_type(var_id).ok_or({
                    let mut err = crate::error::Diagnostic::error();
                    err.message(format!("variable requires a type prefix"));
                    err.primary(var, format!("needs a '$' or '%' prefix"));
                    match var_id {
                        VarId::Local(_) => err.note(format!("consider adding an explicit type to its declaration")),
                        VarId::Reg(reg) => err.note(format!("consider adding {} to !gvar_types in your mapfile", reg)),
                    };
                    err.into()
                })
            },
        }
    }

    /// Get the innate type of a variable.  This comes into play when a variable is referenced by name
    /// without a type sigil.
    pub fn var_name(&self, var_id: VarId) -> Option<&Ident> {
        match var_id {
            VarId::Local(local) => Some(self.variables.get_name(local)),
            VarId::Reg(reg) => self.regs_and_instrs.reg_names.get(&reg),
        }
    }

    /// Get the innate type of a variable.  This comes into play when a variable is referenced by name
    /// without a type sigil.
    pub fn var_default_type(&self, var_id: VarId) -> Option<ScalarType> {
        // NOTE: one might think, "hey, can't we just track LocalIds for regs so that we don't
        //       have two different places that track default types of things?"
        //
        //       ...no, we cannot.  If a register has a type in the mapfile but no name, then
        //       Variables won't know about it.
        match var_id {
            VarId::Local(local) => self.variables.get_type(local),
            VarId::Reg(reg) => self.regs_and_instrs.reg_default_types.get(&reg).copied(),
        }
    }

    /// Generate an AST node with the ideal appearance for a variable.
    ///
    /// If `append_local_ids` is `true`, local variables will get their id numbers appended,
    /// making them distinct.  This is only for testing purposes.
    pub fn var_to_ast(&self, var_id: VarId, read_ty: ScalarType, append_local_ids: bool) -> ast::Var {
        // const simplification should substitute any non-numeric type var reads (like string vars)
        // before this function is ever called.  Probably.
        let explicit_sigil = read_ty.sigil().expect("(bug!) tried to raise read of non-numeric type");

        let name = self.var_name(var_id);
        let name = match (name, var_id) {
            // For registers with no alias, best we can do is emit `[10004]` syntax.  This requires ty_sigil.
            (None, VarId::Reg(_)) => return ast::Var::Resolved { var_id, ty_sigil: Some(explicit_sigil) },

            (Some(name), VarId::Reg(_)) => name.clone(),
            (Some(name), VarId::Local(local_id)) => match append_local_ids {
                true => format!("{}_{}", name, local_id),
                false => format!("{}", name),
            }.parse().unwrap(),

            // NOTE: I don't think this should ever show because locals always have names...
            (None, VarId::Local(local_id)) => format!("__localvar_{}", local_id).parse().unwrap(),
        };

        // Suppress the type prefix if it matches the default
        if self.var_default_type(var_id) == Some(read_ty) {
            ast::Var::Named { ident: name.clone(), ty_sigil: None }
        } else {
            ast::Var::Named { ident: name.clone(), ty_sigil: Some(explicit_sigil) }
        }
    }

    /// Compute the type of an expression through introspection.
    ///
    /// This will not fully typecheck everything.
    pub fn compute_type_shallow(&self, expr: &Sp<ast::Expr>) -> Result<ScalarType, CompileError> {
        match &expr.value {
            ast::Expr::Ternary { left, .. } => self.compute_type_shallow(left),
            ast::Expr::Binop(a, op, _) => Ok(op.result_type_shallow(self.compute_type_shallow(a)?)),
            ast::Expr::Call { func, .. } => Err(error!(
                message("function used in expression"),
                primary(func, "function call in expression"),
                note("currently, the only kind of function implemented is raw instructions"),
            )),
            ast::Expr::Unop(op, a) => Ok(op.result_type_shallow(self.compute_type_shallow(a)?)),
            ast::Expr::LitInt { .. } => Ok(ScalarType::Int),
            ast::Expr::LitFloat { .. } => Ok(ScalarType::Float),
            ast::Expr::LitString(_) => Ok(ScalarType::String),
            ast::Expr::Var(var) => self.var_read_type_from_ast(var),
        }
    }
}

// --------------------------------------------

impl RegsAndInstrs {
    pub fn new() -> Self { Self::default() }

    /// Get the signature of an instruction, if known.
    pub fn ins_signature(&self, opcode: u16) -> Option<&Signature> {
        self.opcode_signatures.get(&(opcode as _))
    }

    pub fn add_signature(&mut self, opcode: u16, str: &str) -> Result<(), SimpleError> {
        let siggy = str.parse().with_context(|| format!("in signature for opcode {}", opcode))?;
        self.opcode_signatures.insert(opcode as u16, siggy);
        Ok(())
    }

    pub fn resolve_func_aliases<'a>(&'a self, name: &'a Ident) -> &'a Ident {
        let mut name: &Ident = name;
        loop {
            if let Some(new_name) = self.func_aliases.get(name) {
                name = new_name;
                continue;
            }
            return name;
        }
    }

    pub fn mapfiles_to_ast(&self) -> Vec<crate::pos::Sp<ast::LitString>> {
        self.mapfiles.iter().map(|s| {
            let string = s.to_str().expect("unpaired surrogate not supported!").into();
            sp!(ast::LitString { string })
        }).collect()
    }
}

pub use siggy::{Signature, ArgEncoding};
mod siggy {
    use super::*;

    use ArgEncoding as Enc;

    /// A signature for an instruction. (typically parsed from a string in a mapfile)
    ///
    /// The signature of an instruction describes not only the types of its arguments, but also
    /// can provide information on how to encode them in binary (e.g. integer width, string padding)
    /// and how to present them in a decompiled file (e.g. hexadecimal for colors).
    ///
    /// Construct using [`std::str::FromStr`].
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Signature {
        encodings: Vec<ArgEncoding>,
    }

    /// Type of an argument to an instruction.
    ///
    /// This is a bit more nuanced compared to [`ScalarType`].  Arguments with the same type
    /// may have different encodings based on how they are either stored in the file, or on how they
    /// may be written in a source file.
    ///
    /// By this notion, [`ArgEncoding`] tends to be more relevant for immediate/literal arguments, while
    /// [`ScalarType`] tends to be more relevant for variables.
    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum ArgEncoding {
        /// `S` in mapfile. 4-byte integer immediate or register.  Displayed as signed.
        Dword,
        /// `s` in mapfile. 2-byte integer immediate.  Displayed as signed.
        Word,
        /// `o` in mapfile. Max of one per instruction. Is decoded to a label.
        JumpOffset,
        /// `t` in mapfile. Max of one per instruction, and requires an accompanying `o` arg.
        JumpTime,
        /// `_` in mapfile. Unused 4-byte space after script arguments, optionally displayed as integer in text.
        ///
        /// Only exists in pre-StB STD where instructions have fixed sizes.
        Padding,
        /// `C` in mapfile. 4-byte integer immediate or register, printed as hex when immediate.
        Color,
        /// `f` in mapfile. Single-precision float.
        Float,
        /// `#[0-9]` in mapfile. A null-terminated string argument padded to a multiple of the given block size.
        String { block_size: usize },
    }

    impl Signature {
        pub fn from_encodings(encodings: Vec<ArgEncoding>) -> Result<Self, SimpleError> {
            validate(&encodings)?;
            Ok(Signature { encodings })
        }

        pub fn arg_encodings(&self) -> impl crate::VeclikeIterator<Item=ArgEncoding> + '_ {
            self.encodings.iter().copied()
        }

        /// Get the minimum number of args allowed in the AST.
        pub fn min_args(&self) -> usize { self.count_args_incl_padding() - self.count_padding() }
        /// Get the maximum number of args allowed in the AST.
        pub fn max_args(&self) -> usize { self.count_args_incl_padding() }

        fn count_args_incl_padding(&self) -> usize {
            self.encodings.len()
        }

        fn count_padding(&self) -> usize {
            self.arg_encodings().rev().position(|c| c != Enc::Padding)
                .unwrap_or(self.count_args_incl_padding())
        }

        pub fn split_padding<'a, T>(&self, args: &'a [T]) -> Option<(&'a [T], &'a [T])> {
            let i = self.count_args_incl_padding() - self.count_padding();
            if i <= args.len() {
                Some(args.split_at(i))
            } else { None }
        }
    }

    impl ArgEncoding {
        pub fn expr_type(self) -> ScalarType {
            match self {
                ArgEncoding::JumpOffset |
                ArgEncoding::JumpTime |
                ArgEncoding::Padding |
                ArgEncoding::Color |
                ArgEncoding::Word |
                ArgEncoding::Dword => ScalarType::Int,
                ArgEncoding::Float => ScalarType::Float,
                ArgEncoding::String { .. } => ScalarType::String,
            }
        }
    }

    fn validate(encodings: &[ArgEncoding]) -> Result<(), SimpleError> {
        let o_count = encodings.iter().filter(|&&c| c == Enc::JumpOffset).count();
        let t_count = encodings.iter().filter(|&&c| c == Enc::JumpTime).count();

        for &(char, count) in &[('o', o_count), ('t', t_count)][..] {
            if count > 1 {
                anyhow::bail!("signature has multiple '{}' args", char);
            }
        }
        if t_count == 1 && o_count == 0 {
            anyhow::bail!("signature has a 't' arg without an 'o' arg");
        }
        Ok(())
    }

    impl std::str::FromStr for Signature {
        type Err = SimpleError;

        fn from_str(s: &str) -> Result<Self, Self::Err> {
            let mut iter = s.bytes().peekable();

            let mut encodings = vec![];
            while let Some(b) = iter.next() {
                let enc = match b {
                    b'S' => ArgEncoding::Dword,
                    b's' => ArgEncoding::Word,
                    b'C' => ArgEncoding::Color,
                    b'o' => ArgEncoding::JumpOffset,
                    b't' => ArgEncoding::JumpTime,
                    b'f' => ArgEncoding::Float,
                    b'_' => ArgEncoding::Padding,
                    b'n' => ArgEncoding::Dword, // FIXME sprite
                    b'N' => ArgEncoding::Dword, // FIXME script
                    b'A' => {
                        let block_size = read_positive_decimal_from_iter(&mut iter)? as usize;
                        ArgEncoding::String { block_size }
                    },
                    0x80..=0xff => anyhow::bail!("non-ascii byte in signature: {:#04x}", b),
                    _ => anyhow::bail!("bad signature character: {:?}", b as char)
                };
                encodings.push(enc);
            }
            Signature::from_encodings(encodings)
        }
    }

    fn read_positive_decimal_from_iter(iter: &mut std::iter::Peekable<std::str::Bytes<'_>>) -> Result<u64, SimpleError> {
        let mut digits = vec![];
        while let Some(b'0'..=b'9') = iter.peek() {
            digits.push(iter.next().unwrap());
        }
        std::str::from_utf8(&digits).unwrap().parse().map_err(Into::into)
    }

    #[test]
    fn test_parse() {
        let parse = <str>::parse::<Signature>;

        assert_eq!(parse("SSS").unwrap(), Signature::from_encodings(vec![Enc::Dword, Enc::Dword, Enc::Dword]).unwrap());

        // fail at end of string
        assert!(parse("SSA").is_err());
        // fail with other content
        assert!(parse("SSAf").is_err());
        // succeed at end of string
        assert_eq!(parse("SA04").unwrap(), Signature::from_encodings(vec![Enc::Dword, Enc::String { block_size: 4 }]).unwrap());
        // succeed with other content
        assert_eq!(parse("A4S").unwrap(), Signature::from_encodings(vec![Enc::String { block_size: 4 }, Enc::Dword]).unwrap());
        // multiple digits
        assert_eq!(parse("A16S").unwrap(), Signature::from_encodings(vec![Enc::String { block_size: 16 }, Enc::Dword]).unwrap());
    }

    #[test]
    fn offset_time_restrictions() {
        let parse = <str>::parse::<Signature>;

        assert!(parse("SSot").is_ok());
        assert!(parse("SSt").is_err());
        assert!(parse("SSo").is_ok());
        assert!(parse("SSoto").is_err());
        assert!(parse("SSott").is_err());
    }
}

/// Type of an expression.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(enum_map::Enum)]
pub enum ScalarType {
    Int,
    Float,
    String,
}

impl ScalarType {
    /// Textual description, e.g. `"an integer"`.
    pub fn descr(self) -> &'static str {
        match self {
            ScalarType::Int => "an integer",
            ScalarType::Float => "a float",
            ScalarType::String => "a string",
        }
    }

    pub fn sigil(self) -> Option<ast::VarReadType> {
        match self {
            ScalarType::Int => Some(ast::VarReadType::Int),
            ScalarType::Float => Some(ast::VarReadType::Float),
            ScalarType::String => None,
        }
    }

    pub fn check_same(self, other: ScalarType, cause: Span, spans: (Span, Span)) -> Result<ScalarType, CompileError> {
        if self == other {
            Ok(self)
        } else {
            Err(error!(
                message("type error"),
                primary(spans.1, "{}", other.descr()),
                secondary(cause, "same types required due to this"),
                secondary(spans.0, "{}", self.descr()),
            ))
        }
    }

    fn require_int(self, cause: Span, value_span: Span) -> Result<(), CompileError> {
        match self {
            ScalarType::Int => Ok(()),
            _ => Err(error!(
                message("type error"),
                primary(value_span, "{}", self.descr()),
                secondary(cause, "only defined on integers"),
            )),
        }
    }

    fn require_float(self, cause: Span, value_span: Span) -> Result<(), CompileError> {
        match self {
            ScalarType::Float => Ok(()),
            _ => Err(error!(
                message("type error"),
                primary(value_span, "{}", self.descr()),
                secondary(cause, "only defined on floats"),
            )),
        }
    }
}

impl Sp<ast::BinopKind> {
    /// Get the result type assuming both args are the same type and without any further validation.
    pub fn result_type_shallow(&self, arg_ty: ScalarType) -> ScalarType {
        use ast::BinopKind as B;

        match self.value {
            B::Add | B::Sub | B::Mul | B::Div | B::Rem | B::LogicOr | B::LogicAnd => arg_ty,
            B::Eq | B::Ne | B::Lt | B::Le | B::Gt | B::Ge => ScalarType::Int,
            B::BitXor | B::BitAnd | B::BitOr => ScalarType::Int,
        }
    }

    /// Perform type-checking.
    pub fn type_check(&self, a: ScalarType, b: ScalarType, arg_spans: (Span, Span)) -> Result<(), CompileError> {
        self.result_type(a, b, arg_spans).map(|_| ())
    }

    /// Get the output type, performing type-checking.
    pub fn result_type(&self, a: ScalarType, b: ScalarType, arg_spans: (Span, Span)) -> Result<ScalarType, CompileError> {
        use ast::BinopKind as B;

        // they ALL require matching types
        let ty = a.check_same(b, self.span, arg_spans)?;
        match self.value {
            B::Add | B::Sub | B::Mul | B::Div | B::Rem | B::LogicOr | B::LogicAnd => Ok(ty),
            B::Eq | B::Ne | B::Lt | B::Le | B::Gt | B::Ge => Ok(ScalarType::Int),
            B::BitXor | B::BitAnd | B::BitOr => {
                ty.require_int(self.span, arg_spans.0)?;
                Ok(ScalarType::Int)
            },
        }
    }
}

impl Sp<ast::UnopKind> {
    /// Figure out the output type without full type-checking.
    pub fn result_type_shallow(&self, arg_ty: ScalarType) -> ScalarType {
        match self.value {
            token![unop -] => arg_ty,
            token![unop !] => ScalarType::Int,
            token![unop sin] |
            token![unop cos] |
            token![unop sqrt] => ScalarType::Float,
            token![unop _S] => ScalarType::Int,
            token![unop _f] => ScalarType::Float,
        }
    }

    /// Perform type-checking.
    pub fn type_check(&self, ty: ScalarType, arg_span: Span) -> Result<(), CompileError> {
        match self.value {
            token![unop -] => Ok(()),
            token![unop _f] |
            token![unop !] => ty.require_int(self.span, arg_span),
            token![unop _S] |
            token![unop sin] |
            token![unop cos] |
            token![unop sqrt] => ty.require_float(self.span, arg_span),
        }
    }

    /// Get the output type, performing type-checking.
    pub fn result_type(&self, ty: ScalarType, arg_span: Span) -> Result<ScalarType, CompileError> {
        self.type_check(ty, arg_span)?;
        Ok(self.result_type_shallow(ty))
    }
}
