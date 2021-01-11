use std::collections::HashMap;
use crate::error::CompileError;
use crate::ident::Ident;
use crate::eclmap::Eclmap;
use crate::ast;
use crate::var::{Variables, VarId};
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
    pub reg_default_types: HashMap<i32, ScalarType>,
    pub reg_map: HashMap<Ident, i32>,
    pub reg_names: HashMap<i32, Ident>,
}

impl TypeSystem {
    pub fn new() -> Self { Self::default() }

    /// Add info from an eclmap.  Its path is recorded in order to help emit import directives
    /// into the file.
    pub fn extend_from_eclmap(&mut self, path: &std::path::Path, eclmap: &Eclmap) {
        self.regs_and_instrs.mapfiles.push(path.to_owned());

        for (&opcode, name) in &eclmap.ins_names {
            self.regs_and_instrs.opcode_names.insert(opcode as u16, name.clone());
            self.regs_and_instrs.func_aliases.insert(name.clone(), Ident::new_ins(opcode as u16));
        }
        for (&opcode, value) in &eclmap.ins_signatures {
            let arg_string = value.to_string();
            self.regs_and_instrs.opcode_signatures.insert(opcode as u16, Signature { arg_string });
        }
        for (&reg, name) in &eclmap.gvar_names {
            self.regs_and_instrs.reg_names.insert(reg, name.clone());
            self.regs_and_instrs.reg_map.insert(name.clone(), reg);
            self.variables.declare_global_register_alias(name.clone(), reg);
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
            self.regs_and_instrs.reg_default_types.insert(id, ty);
        }
    }

    /// Resolve names in a script parsed from text, replacing all variables with unique [`VarId`]s.
    ///
    /// After calling this, information containing the names and declared types of all variables
    /// will be stored on the [`Variables`] type.
    pub fn resolve_names(&mut self, ast: &mut ast::Script) -> Result<(), CompileError> {
        let mut v = crate::var::ResolveVarsVisitor::new(&mut self.variables);
        ast::walk_mut_script(&mut v, ast);
        v.finish()
    }

    pub fn resolve_names_block(&mut self, ast: &mut ast::Block) -> Result<(), CompileError> {
        let mut v = crate::var::ResolveVarsVisitor::new(&mut self.variables);
        <_ as ast::VisitMut>::visit_block(&mut v, ast);
        v.finish()
    }

    /// Convert [`VarId`]s in the AST back into their original identifiers.
    ///
    /// When used on decompiled code from a binary file, this will typically just replace raw register
    /// access with their mapfile aliases (e.g. from `[10004]` to `I3`).
    ///
    /// It can also be used on partially-compiled source code, though *this particular usage is only supported
    /// strictly for testing and debugging purposes.*  In this case, setting `append_ids` to `true` will rename
    /// local variables from `x` to e.g. `x_3` by appending their [`LocalId`], enabling them to be differentiated
    /// by scope.  Note that compiler-generated temporaries may render as something unusual.
    pub fn unresolve_names(&self, ast: &mut ast::Script, append_ids: bool) -> Result<(), CompileError> {
        let mut v = unresolve_names::Visitor::new(self, append_ids);
        ast::walk_mut_script(&mut v, ast);
        v.finish()
    }

    pub fn unresolve_names_block(&mut self, ast: &mut ast::Block, append_ids: bool) -> Result<(), CompileError> {
        let mut v = unresolve_names::Visitor::new(self, append_ids);
        <_ as ast::VisitMut>::visit_block(&mut v, ast);
        v.finish()
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
        let name = self.var_name(var_id);
        let name = match (name, var_id) {
            // For registers with no alias, best we can do is emit `[10004]` syntax.
            (None, VarId::Reg(_)) => return ast::Var::Resolved { var_id, ty_sigil: Some(read_ty.into()) },

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
            ast::Var::Named { ident: name.clone(), ty_sigil: Some(read_ty.into()) }
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
            ast::Expr::LitString(_) => Err(error!(
                message("string used in expression"),
                primary(expr, "string in expression"),
            )),
            ast::Expr::Var(var) => self.var_read_type_from_ast(var),
        }
    }
}

// --------------------------------------------

mod unresolve_names {
    use super::*;

    /// Visitor for "unresolving" local variables and recovering their original names.
    pub struct Visitor<'ts> {
        ty_ctx: &'ts TypeSystem,
        append_ids: bool,
        errors: CompileError,
    }

    impl<'ts> Visitor<'ts> {
        pub fn new(ty_ctx: &'ts TypeSystem, append_ids: bool) -> Self {
            Visitor { ty_ctx, append_ids, errors: CompileError::new_empty() }
        }
        pub fn finish(self) -> Result<(), CompileError> { self.errors.into_result(()) }
    }

    impl ast::VisitMut for Visitor<'_> {
        fn visit_var(&mut self, var: &mut Sp<ast::Var>) {
            if let ast::Var::Resolved { ty_sigil: _, var_id } = var.value {
                // FIXME this seems weird because we ought to just be able to reuse ty_sigil in the output,
                //       but 'var_read_type_from_ast' seems to require a definite type.
                match self.ty_ctx.var_read_type_from_ast(var) {
                    Ok(ty) => var.value = self.ty_ctx.var_to_ast(var_id, ty, self.append_ids),
                    Err(e) => self.errors.append(e),
                }
            }
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


#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signature {
    /// String representing the signature.
    arg_string: String,
}

impl Signature {
    /// Get an automatic signature for reading an unknown instruction with this many dwords.
    pub fn auto(n: usize) -> Signature {
        Signature { arg_string: String::from_utf8(vec![b'S'; n]).unwrap() }
    }

    pub fn arg_encodings(&self) -> Vec<ArgEncoding> {
        self.arg_string.chars().map(|c| match c {
            'S' => ArgEncoding::Dword,
            'C' => ArgEncoding::Color,
            // o and t get no special encoding because we translate jumps directly into `goto`
            'o' => ArgEncoding::Dword, // offset
            't' => ArgEncoding::Dword, // time
            'f' => ArgEncoding::Float,
            '_' => ArgEncoding::Padding,
            'n' => ArgEncoding::Dword, // FIXME sprite
            'N' => ArgEncoding::Dword, // FIXME script
            _ => panic!("In mapfile: unknown signature character: {:?}", c)
        }).collect()
    }

    /// Get the minimum number of args allowed in the AST.
    pub fn min_args(&self) -> usize { self.count_args_incl_padding() - self.count_padding() }
    /// Get the maximum number of args allowed in the AST.
    pub fn max_args(&self) -> usize { self.count_args_incl_padding() }

    fn count_args_incl_padding(&self) -> usize {
        self.arg_string.len()
    }

    fn count_padding(&self) -> usize {
        self.arg_string.bytes().rev().position(|c| c != b'_').unwrap_or(self.count_args_incl_padding())
    }

    pub fn split_padding<'a, T>(&self, args: &'a [T]) -> Option<(&'a [T], &'a [T])> {
        let i = self.count_args_incl_padding() - self.count_padding();
        if i <= args.len() {
            Some(args.split_at(i))
        } else { None }
    }
}

/// Type of a value that exists at runtime in the script.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(enum_map::Enum)]
pub enum ScalarType { Int, Float }

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
    /// Script argument encoded as a 4-byte integer.
    Dword,
    /// Unused 4-byte space after script arguments, optionally displayed as integer in text.
    ///
    /// Only exists in pre-StB STD where instructions have fixed sizes.
    Padding,
    /// Script argument encoded as a 4-byte integer, printed as hex.
    Color,
    /// Script argument encoded as a 4-byte float.
    Float,
}

impl ScalarType {
    pub fn default_encoding(self) -> ArgEncoding {
        match self {
            ScalarType::Int => ArgEncoding::Dword,
            ScalarType::Float => ArgEncoding::Float,
        }
    }

    /// Textual description, e.g. `"an integer"`.
    pub fn descr(self) -> &'static str {
        match self {
            ScalarType::Int => "an integer",
            ScalarType::Float => "a float",
        }
    }

    /// `$` or `%`.
    pub fn sigil(self) -> &'static str {
        match self {
            ScalarType::Int => "$",
            ScalarType::Float => "%",
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
            ast::UnopKind::Neg => arg_ty,
            ast::UnopKind::Not => ScalarType::Int,
            ast::UnopKind::Sin |
            ast::UnopKind::Cos |
            ast::UnopKind::Sqrt => ScalarType::Float,
            ast::UnopKind::CastI => ScalarType::Int,
            ast::UnopKind::CastF => ScalarType::Float,
        }
    }

    /// Perform type-checking.
    pub fn type_check(&self, ty: ScalarType, arg_span: Span) -> Result<(), CompileError> {
        match self.value {
            ast::UnopKind::Neg => Ok(()),
            ast::UnopKind::CastF |
            ast::UnopKind::Not => ty.require_int(self.span, arg_span),
            ast::UnopKind::CastI |
            ast::UnopKind::Sin |
            ast::UnopKind::Cos |
            ast::UnopKind::Sqrt => ty.require_float(self.span, arg_span),
        }
    }

    /// Get the output type, performing type-checking.
    pub fn result_type(&self, ty: ScalarType, arg_span: Span) -> Result<ScalarType, CompileError> {
        self.type_check(ty, arg_span)?;
        Ok(self.result_type_shallow(ty))
    }
}
