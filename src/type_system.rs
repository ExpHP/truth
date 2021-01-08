use std::collections::HashMap;
use crate::{CompileError, Expr};
use crate::ident::Ident;
use crate::eclmap::Eclmap;
use crate::ast;
use crate::scope::Variables;
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
    variables: Option<Variables>,
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

    /// Resolve names in a script parsed from text, replacing all variables with unique [`VarId`]s.
    ///
    /// After calling this, information containing the names and declared types of all variables
    /// will be stored on this type, available through the [`Self::variables`] method.
    pub fn resolve_names(&mut self, ast: &mut ast::Script) -> Result<(), CompileError> {
        use crate::passes::resolve_vars;

        let mut v = resolve_vars::Visitor::new(&self.regs_and_instrs);
        ast::walk_mut_script(&mut v, ast);
        self.variables = Some(v.finish()?);
        Ok(())
    }

    /// Convert [`VarId`]s in the AST back into their original identifiers.
    ///
    /// This may produce unusual output for temporaries, and is intended for testing and debugging purposes only.
    pub fn unresolve_names(&self, ast: &mut ast::Script, append_ids: bool) -> Result<(), CompileError> {
        use crate::passes::resolve_vars;

        let mut v = resolve_vars::Unvisitor::new(self.variables(), append_ids);
        ast::walk_mut_script(&mut v, ast);
        Ok(())
    }

    /// Add info from an eclmap.  Its path is recorded in order to help emit import directives
    /// into the file.
    pub fn extend_from_eclmap(&mut self, path: &std::path::Path, eclmap: &Eclmap) {
        assert!(self.variables.is_none(), "(bug!) attempted to load ECLmap after resolving names, \
            but the resolver assumed it had all globals during initialization!");

        self.regs_and_instrs.extend_from_eclmap(path, eclmap);
    }

    /// Get access to the [`Variables`] instance.
    ///
    /// This will panic if name resolution has not been performed.
    #[track_caller]
    pub fn variables(&self) -> &Variables {
        self.variables.as_ref().expect("(bug!) tried to access variables without performing name resolution!")
    }

    /// Get mutable access to the [`Variables`] instance.
    ///
    /// This will panic if name resolution has not been performed.
    #[track_caller]
    pub fn variables_mut(&mut self) -> &mut Variables {
        self.variables.as_mut().expect("(bug!) tried to access variables without performing name resolution!")
    }

    /// Get the type of a variable (int or float), if known.
    pub fn var_type(&self, var: &ast::Var) -> Option<ScalarType> {
        match *var {
            ast::Var::Register { ty, .. } => Some(ty.into()),

            ast::Var::Named { ty_sigil, ref ident } => {
                // NOTE: no need to consider locals here because resolution gets rid of Named...
                if let Some(ty_sigil) = ty_sigil {
                    return Some(ty_sigil.into()); // explicit type from user
                }
                let number = self.regs_and_instrs.reg_map.get(ident)?;
                self.regs_and_instrs.reg_default_types.get(number).copied()
            },

            ast::Var::Local { ty_sigil, var_id } => {
                if let Some(ty_sigil) = ty_sigil {
                    return Some(ty_sigil.into()); // explicit type from user
                }
                self.variables().get_type(var_id)
            },
        }
    }

    /// Compute the type of an expression through introspection.
    ///
    /// This will not fully typecheck everything.
    pub fn compute_type_shallow(&self, expr: &Sp<ast::Expr>) -> Result<ScalarType, CompileError> {
        match &expr.value {
            Expr::Ternary { left, .. } => self.compute_type_shallow(left),
            Expr::Binop(a, op, _) => Ok(op.result_type_shallow(self.compute_type_shallow(a)?)),
            Expr::Call { func, .. } => Err(error!(
                message("function used in expression"),
                primary(func, "function call in expression"),
                note("currently, the only kind of function implemented is raw instructions"),
            )),
            Expr::Unop(op, a) => Ok(op.result_type_shallow(self.compute_type_shallow(a)?)),
            Expr::LitInt { .. } => Ok(ScalarType::Int),
            Expr::LitFloat { .. } => Ok(ScalarType::Float),
            Expr::LitString(_) => Err(error!(
                message("string used in expression"),
                primary(expr, "string in expression"),
            )),
            Expr::Var(var) => self.var_type(var).ok_or_else(|| error!(
                message("cannot determine type of variable read"),
                primary(var, "type sigil required ('$' or '%')"),
            )),
        }
    }
}

impl RegsAndInstrs {
    pub fn new() -> Self { Self::default() }

    /// Add info from an eclmap.  Its path is recorded in order to help emit import directives
    /// into the file.
    pub fn extend_from_eclmap(&mut self, path: &std::path::Path, eclmap: &Eclmap) {
        self.mapfiles.push(path.to_owned());

        for (&opcode, name) in &eclmap.ins_names {
            self.opcode_names.insert(opcode as u16, name.clone());
            self.func_aliases.insert(name.clone(), Ident::new_ins(opcode as u16));
        }
        for (&opcode, value) in &eclmap.ins_signatures {
            let arg_string = value.to_string();
            self.opcode_signatures.insert(opcode as u16, Signature { arg_string });
        }
        for (&id, name) in &eclmap.gvar_names {
            self.reg_names.insert(id, name.clone());
            self.reg_map.insert(name.clone(), id);
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
            self.reg_default_types.insert(id, ty);
        }
    }

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

    /// Get the "opcode" of a variable, if it is a register.
    pub fn reg_id(&self, var: &ast::Var) -> Option<i32> {
        match *var {
            ast::Var::Named { ref ident, .. } => self.reg_map.get(ident).copied(),
            ast::Var::Local { var_id: _, .. } => None,
            ast::Var::Register { reg: number, .. } => Some(number),
        }
    }

    /// Generate an AST node with the ideal appearance for a register.
    pub fn reg_to_ast(&self, reg: i32, ty: ScalarType) -> ast::Var {
        match self.reg_names.get(&reg) {
            Some(name) => {
                // Suppress the type prefix if it matches the default
                if self.reg_default_types.get(&reg) == Some(&ty) {
                    ast::Var::Named { ident: name.clone(), ty_sigil: None }
                } else {
                    ast::Var::Named { ident: name.clone(), ty_sigil: Some(ty.into()) }
                }
            },
            None => ast::Var::Register { reg, ty: ty.into() },
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

    pub fn result_type(&self, a: ScalarType, b: ScalarType, arg_spans: (Span, Span)) -> Result<ScalarType, CompileError> {
        use ast::BinopKind as B;

        // they ALL require matching types
        let ty = a.check_same(b, self.span, arg_spans)?;
        match self.value {
            B::Add | B::Sub | B::Mul | B::Div | B::Rem | B::LogicOr | B::LogicAnd => Ok(ty),
            B::Eq | B::Ne | B::Lt | B::Le | B::Gt | B::Ge => Ok(ScalarType::Int),
            B::BitXor | B::BitAnd | B::BitOr => {
                if ty == ScalarType::Int {
                    Ok(ScalarType::Int)
                } else {
                    Err(error!(
                        message("type error"),
                        primary(arg_spans.0, "{}", a.descr()),
                        secondary(self, "only defined on integers"),
                    ))
                }
            },
        }
    }
}

impl Sp<ast::UnopKind> {
    pub fn result_type_shallow(&self, arg_ty: ScalarType) -> ScalarType {
        match self.value {
            ast::UnopKind::Neg => arg_ty,
            ast::UnopKind::Not => ScalarType::Int,
        }
    }

    pub fn result_type(&self, ty: ScalarType, arg_span: Span) -> Result<ScalarType, CompileError> {
        match self.value {
            ast::UnopKind::Neg => Ok(ty),
            ast::UnopKind::Not => {
                if ty == ScalarType::Int {
                    Ok(ScalarType::Int)
                } else {
                    Err(error!(
                        message("type error"),
                        primary(arg_span, "{}", ty.descr()),
                        secondary(self, "only defined on integers"),
                    ))
                }
            },
        }
    }
}
