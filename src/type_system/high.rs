use std::collections::HashMap;
use std::path::PathBuf;

use anyhow::Context;

use crate::ast;
use crate::error::{CompileError, SimpleError};
use crate::pos::{Sp, Span};
use crate::ident::{Ident, ResIdent, GensymContext};
use crate::resolve::{RegId, Namespace, DefId, ResId, Resolutions};
use crate::eclmap::Eclmap;
use crate::value::ScalarValue;
use crate::type_system::{ScalarType, InstrAbi};

/// Context object for the majority of compilation.
///
/// This is a context object that holds a significant portion of the mutable state that is shared between
/// compiler passes (in particular passes that traverse the AST or that convert between the AST and
/// low-level representations).
///
/// It provides some methods for creating definitions and returning [`DefId`]s.  This is partly historical,
/// but also because it's not clear how to move these methods to [`Defs`] where they might conceptually belong.
///
/// # Limitation of scope
///
//   NOTE: To the future me who is about to delete this section from the documentation:
//         Please consider the examples of concessions in the section.
//         Are you absolutely certain you cannot do something similar to achieve your current goal?
//
/// While there is no doubt a great deal of code which depends on this type (or at least on one or more of
/// its fields), there are a number of phases of compilation that are **forbidden** to depend on this type
/// or any of its fields, just as a matter of principle.  These are:
///
/// * Parsing of text to AST
/// * Formatting of AST to text
/// * Reading binary files to the low-level representation
/// * Writing the low-level representation to a binary file
///
/// There have been numerous instances of things in the past which appeared that they may require breaking
/// this rule, but it has always been found possible to make concessions in favor of keeping this separation.
/// (e.g. [`llir::RawInstr`] holds an args blob so that reading/writing doesn't require signatures.
/// [`crate::passes::resolve_names::assign_res_ids`] allows the parser to not require `Resolutions`, and
/// [`crate::passes::debug::make_idents_unique`] does the same for the formatter)
#[derive(Debug, Clone)]
pub struct TypeSystem {
    /// Catalogues all loaded mapfiles for generating imports.
    mapfiles: Vec<PathBuf>,
    /// Results of name resolution.  Maps [`ResId`]s to [`DefId`]s.
    pub resolutions: Resolutions,
    /// Stores information about [`DefId`]s.
    pub defs: Defs,
    /// For generating identifiers.
    pub gensym: GensymContext,
}

/// Retains information about all definitions in the program.
///
/// This object is responsible for storing information that is immediately available at the definition
/// site of a variable or function, such as: type information, spans, function signatures, expressions
/// for consts.
///
/// It is also currently the type responsible for holding type information about registers and opcodes,
/// despite these not having [`DefId`]s.
///
/// **Note:** The methods for creating new definitions are currently on [`TypeSystem`], where they can
/// more easily record information for name resolution.
#[derive(Debug, Clone, Default)]
pub struct Defs {
    regs: HashMap<RegId, RegData>,
    instrs: HashMap<u16, InsData>,

    vars: HashMap<DefId, VarData>,
    funcs: HashMap<DefId, FuncData>,

    // Preferred aliases.  These are used during decompilation to make the output readable.
    reg_aliases: HashMap<RegId, DefId>,
    ins_aliases: HashMap<u16, DefId>,

    /// Ids for names available in the global scope.  These form the baseline set of names
    /// available to name resolution.
    ///
    /// NOTE: This is specifically for *externally-defined things* that are defined before name
    /// resolution even begins.  Things like user-defined functions are not included here;
    /// name resolution handles those in the same way it handles anything else.
    global_ids: Vec<(Namespace, DefId)>,
}

// =============================================================================

impl TypeSystem {
    pub fn new() -> Self {
        TypeSystem {
            mapfiles: Default::default(),
            resolutions: Default::default(),
            defs: Default::default(),
            gensym: Default::default(),
        }
    }
}

impl Defs {
    pub fn new() -> Self { Default::default() }
}

/// # Definitions
impl TypeSystem {
    /// Set the inherent type of a register.
    pub fn set_reg_ty(&mut self, reg: RegId, ty: VarType) {
        self.defs.regs.insert(reg, RegData { ty });
    }

    /// Add an alias for a register from a mapfile, attaching a brand new ID to the ident.
    ///
    /// The alias will also become the new preferred alias for decompiling that register.
    pub fn define_global_reg_alias(&mut self, reg: RegId, ident: Ident) -> DefId {
        let res_ident = self.resolutions.attach_fresh_res(ident);
        let def_id = self.create_new_def_id(&res_ident);

        self.defs.vars.insert(def_id, VarData {
            ty: None,
            kind: VarKind::RegisterAlias { reg, ident: res_ident },
        });
        self.defs.reg_aliases.insert(reg, def_id);
        self.defs.global_ids.push((Namespace::Vars, def_id));
        def_id
    }

    /// Declare a local variable, attaching a brand new ID to the ident.
    pub fn define_local(&mut self, ident: Sp<ResIdent>, ty: VarType) -> DefId {
        let def_id = self.create_new_def_id(&ident);

        self.defs.vars.insert(def_id, VarData {
            ty: Some(ty),
            kind: VarKind::Local { ident },
        });
        def_id
    }

    /// Declare a fully-evaluated compile-time constant variable, attaching a brand new ID to the ident.
    pub fn define_global_const_var(&mut self, ident: Sp<ResIdent>, value: ScalarValue) -> Sp<ResIdent> {
        let def_id = self.create_new_def_id(&ident);

        self.defs.vars.insert(def_id, VarData {
            ty: Some(Some(value.ty())),
            kind: VarKind::Const { ident: ident.clone(), value },
        });
        self.defs.global_ids.push((Namespace::Vars, def_id));
        ident
    }

    /// Set the low-level ABI of an instruction.
    ///
    /// A high-level [`Signature`] will also be generated from the ABI.
    pub fn set_ins_abi(&mut self, opcode: u16, abi: InstrAbi) {
        // also update the high-level signature
        let sig = abi.create_signature(self);
        sig.validate(self).expect("invalid signature from InstrAbi");

        self.defs.instrs.insert(opcode, InsData { abi, sig });
    }

    /// Add an alias for an instruction from a mapfile, attaching a brand new ID for name resolution to the ident.
    ///
    /// The alias will also become the new preferred alias for decompiling that instruction.
    pub fn define_global_ins_alias(&mut self, opcode: u16, ident: Ident) -> DefId {
        let res_ident = self.resolutions.attach_fresh_res(ident);
        let def_id = self.create_new_def_id(&res_ident);

        self.defs.funcs.insert(def_id, FuncData {
            sig: None,
            kind: FuncKind::InstructionAlias { opcode, ident: res_ident },
        });
        self.defs.ins_aliases.insert(opcode, def_id);
        self.defs.global_ids.push((Namespace::Funcs, def_id));
        def_id
    }

    /// Add a user-defined function.
    ///
    /// FIXME: Should take signature, inline/const-ness, etc.
    pub fn define_user_func(&mut self, ident: Sp<ResIdent>) -> DefId {
        let def_id = self.create_new_def_id(&ident);

        self.defs.funcs.insert(def_id, FuncData {
            sig: None,  // FIXME
            kind: FuncKind::User { ident },
        });
        def_id
    }

    /// Create a [`DefId`] for the name in a declaration, and automatically resolve the input
    /// ident to that ID.
    fn create_new_def_id(&mut self, ident: &ResIdent) -> DefId {
        let def_id = Self::synthesize_def_id_from_res_id(ident.expect_res());
        self.resolutions.record_resolution(ident, def_id);
        def_id
    }

    fn synthesize_def_id_from_res_id(res: ResId) -> DefId {
        // no need to invent new numbers
        DefId(res.0)
    }
}

/// # Global names
impl Defs {
    /// Iterate over all things that are available to the initial (global) scope during
    /// name resolution.
    pub fn globals(&self) -> impl Iterator<Item=(Namespace, DefId)> + '_ {
        self.global_ids.iter().copied()
    }
}

/// # Recovering low-level information
impl Defs {
    /// Get the register mapped to this variable, if it is a register alias.
    ///
    /// Returns `None` for variables that do not represent registers.
    ///
    /// IMPORTANT:  In some formats like ANM and old ECL, local variables are also ultimately
    /// allocated to registers, but that is unrelated to this and this function will always
    /// return `None` for them.
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a variable.
    pub fn var_reg(&self, def_id: DefId) -> Option<RegId> {
        match self.vars[&def_id] {
            VarData { kind: VarKind::RegisterAlias { reg, .. }, .. } => Some(reg),
            _ => None,
        }
    }

    /// If this function is an instruction alias, get its opcode.
    ///
    /// Returns `None` for functions that do not represent instructions.
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a function.
    pub fn func_opcode(&self, def_id: DefId) -> Option<u16> {
        match self.funcs[&def_id] {
            FuncData { kind: FuncKind::InstructionAlias { opcode, .. }, .. } => Some(opcode),
            _ => None,
        }
    }

    /// Recovers the ABI of an opcode, if it is known.
    pub fn ins_abi(&self, opcode: u16) -> Option<&InstrAbi> {
        self.instrs.get(&opcode).map(|x| &x.abi)
    }
}

/// # Accessing high-level information
impl Defs {
    /// Get the identifier that makes something a candidate for name resolution.
    ///
    /// # Panics
    ///
    /// Panics if the namespace is wrong.
    ///
    /// (FIXME: this is silly because Defs ought to know what namespace each
    ///         id belongs to without having to be reminded...)
    pub fn name(&self, ns: Namespace, def_id: DefId) -> &ResIdent {
        match ns {
            Namespace::Vars => self.var_name(def_id),
            Namespace::Funcs => self.func_name(def_id),
        }
    }

    /// Get the fully-resolved name of a variable.
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a variable.
    pub fn var_name(&self, def_id: DefId) -> &ResIdent {
        match self.vars[&def_id] {
            VarData { kind: VarKind::RegisterAlias { ref ident, .. }, .. } => ident,
            VarData { kind: VarKind::Local { ref ident, .. }, .. } => ident,
            VarData { kind: VarKind::Const { ref ident, .. }, .. } => ident,
        }
    }

    /// Get the fully resolved name of a function.
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a variable.
    pub fn func_name(&self, def_id: DefId) -> &ResIdent {
        match self.funcs[&def_id] {
            FuncData { kind: FuncKind::InstructionAlias { ref ident, .. }, .. } => ident,
            FuncData { kind: FuncKind::User { ref ident, .. }, .. } => ident,
        }
    }

    /// Get the inherent type of any kind of named variable. (register aliases, locals, temporaries, consts)
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a variable.
    pub fn var_inherent_ty(&self, def_id: DefId) -> VarType {
        match self.vars[&def_id] {
            VarData { kind: VarKind::RegisterAlias { reg, .. }, .. } => self.reg_inherent_ty(reg),
            VarData { ty, .. } => ty.expect("shouldn't be alias"),
        }
    }

    /// Get the inherent type of a register.
    fn reg_inherent_ty(&self, reg: RegId) -> VarType {
        match self.regs.get(&reg) {
            Some(&RegData { ty }) => ty,
            None => {
                // This is a register whose type is not in any mapfile.
                // This is actually fine, and is expected for stack registers.
                None  // unspecified type
            },
        }
    }

    /// Get the signature of any kind of named function. (instruction aliases, inline and const functions...)
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a function.
    pub fn func_signature(&self, def_id: DefId) -> Result<&Signature, MissingSigError> {
        match self.funcs[&def_id] {
            FuncData { kind: FuncKind::InstructionAlias { opcode, .. }, .. } => self.ins_signature(opcode),
            FuncData { kind: FuncKind::User { .. }, .. } => unimplemented!("need to create signatures for user funcs!"),
        }
    }

    /// Get the high-level signature of an instruction.
    fn ins_signature(&self, opcode: u16) -> Result<&Signature, MissingSigError> {
        match self.instrs.get(&opcode) {
            Some(InsData { sig, .. }) => Ok(sig),
            None => Err(MissingSigError { opcode }),
        }
    }

    /// Get the span most closely associated with a variable (ident at declaration site,
    /// or expr of a temporary), if there is one.
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a variable.
    pub fn var_decl_span(&self, def_id: DefId) -> Option<Span> {
        match &self.vars[&def_id] {
            VarData { kind: VarKind::RegisterAlias { .. }, .. } => None,
            VarData { kind: VarKind::Local { ident, .. }, .. } => Some(ident.span),
            VarData { kind: VarKind::Const { ident, .. }, .. } => Some(ident.span),
        }
    }

    /// Get the span of the ident at the declaration site for any kind of function,
    /// if there is such an ident.
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a function.
    pub fn func_decl_span(&self, def_id: DefId) -> Option<Span> {
        match &self.funcs[&def_id] {
            FuncData { kind: FuncKind::InstructionAlias { .. }, .. } => None,
            FuncData { kind: FuncKind::User { ident, .. }, .. } => Some(ident.span),
        }
    }

    /// Get the value of a variable if it is a fully-evaluated const.
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a variable.
    pub fn var_const_value(&mut self, def_id: DefId) -> Option<ScalarValue> {
        match &self.vars[&def_id] {
            VarData { kind: VarKind::Const { value, .. }, .. } => Some(value.clone()),
            _ => None,
        }
    }
}

impl TypeSystem {
    /// Add info from an eclmap.
    ///
    /// Its path (if one is provided) is recorded in order to emit import directives into a decompiled script file.
    pub fn extend_from_eclmap(&mut self, path: Option<&std::path::Path>, eclmap: &Eclmap) -> Result<(), SimpleError> {
        if let Some(path) = path {
            self.mapfiles.push(path.to_owned());
        }

        for (&opcode, ident) in &eclmap.ins_names {
            self.define_global_ins_alias(opcode as u16, ident.clone());
        }
        for (&opcode, abi_str) in &eclmap.ins_signatures {
            let abi = abi_str.parse().with_context(|| format!("in signature for opcode {}", opcode))?;
            self.set_ins_abi(opcode as u16, abi);
        }
        for (&reg, ident) in &eclmap.gvar_names {
            self.define_global_reg_alias(RegId(reg), ident.clone());
        }
        for (&reg, value) in &eclmap.gvar_types {
            let ty = match &value[..] {
                "%" => Some(ScalarType::Float),
                "$" => Some(ScalarType::Int),
                _ => anyhow::bail!("In mapfile: Ignoring invalid variable type '{}' for gvar {}", value, reg),
            };
            self.set_reg_ty(RegId(reg), ty);
        }
        Ok(())
    }

    pub fn mapfiles_to_ast(&self) -> Vec<crate::pos::Sp<ast::LitString>> {
        self.mapfiles.iter().map(|s| {
            let string = s.to_str().expect("unpaired surrogate not supported!").into();
            sp!(ast::LitString { string })
        }).collect()
    }
}

/// A variable's inherent type.  `None` means untyped (i.e. annotations are always required).
pub type VarType = Option<ScalarType>;

#[derive(Debug, Clone)]
struct RegData {
    ty: VarType,
}

#[derive(Debug, Clone)]
struct VarData {
    kind: VarKind,
    /// Inherent type.  `None` for [`VarKind::RegisterAlias`].
    ty: Option<VarType>,
}

#[derive(Debug, Clone)]
enum VarKind {
    RegisterAlias {
        ident: ResIdent,
        reg: RegId,
        // TODO: location where alias is defined
    },
    Local {
        /// NOTE: For auto-generated temporaries, the span may point to their expression instead.
        ident: Sp<ResIdent>,
    },
    Const {
        ident: Sp<ResIdent>,
        value: ScalarValue,
    }
}

#[derive(Debug, Clone)]
struct InsData {
    abi: InstrAbi,
    sig: Signature,
}

#[derive(Debug, Clone)]
struct FuncData {
    kind: FuncKind,
    /// `None` for [`FuncKind::InstructionAlias`].
    sig: Option<Signature>,
}

#[derive(Debug, Clone)]
pub enum FuncKind {
    InstructionAlias {
        ident: ResIdent,
        opcode: u16,
        // TODO: location where alias is defined
    },
    User {
        ident: Sp<ResIdent>,
        // TODO: const-ness, inline-ness
    }
}

// =============================================================================

impl TypeSystem {
    /// Get the effective type of a variable at a place where it is referenced.
    ///
    /// This can be different from the variable's innate type.  E.g. an integer global `I0` can be
    /// cast as a float using `%I0`.
    ///
    /// This returns [`ScalarType`] instead of [`ast::VarReadType`] because const vars could be strings.
    pub fn var_read_ty_from_ast(&self, var: &ast::Var) -> VarType {
        var.ty_sigil.map(Into::into)
            .or_else(|| self.var_inherent_ty_from_ast(var))
    }

    /// Get the innate type of a variable at a place where it is referenced, ignoring its sigils.
    ///
    /// `None` means it has no inherent type. (is untyped, e.g. via `var` keyword)
    pub fn var_inherent_ty_from_ast(&self, var: &ast::Var) -> VarType {
        match var.name {
            ast::VarName::Reg { reg, .. } => self.defs.reg_inherent_ty(reg),
            ast::VarName::Normal { ref ident, .. } => self.defs.var_inherent_ty(self.resolutions.expect_def(ident)),
        }
    }

    /// If the variable is a register or register alias, gets the associated register id.
    ///
    /// Otherwise, it must be something else (e.g. a local, a const...), whose unique
    /// name resolution id is returned.
    pub fn var_reg_from_ast(&self, var: &ast::VarName) -> Result<RegId, DefId> {
        match var {
            &ast::VarName::Reg { reg, .. } => Ok(reg),  // register
            ast::VarName::Normal { ident, .. } => {
                let def_id = self.resolutions.expect_def(ident);
                match self.defs.var_reg(def_id) {
                    Some(reg) => Ok(reg),  // register alias
                    None => Err(def_id),  // something else
                }
            },
        }
    }

    /// If the function name is an instruction or instruction alias, gets the associated register id.
    ///
    /// Otherwise, it must be something else (e.g. a local, a const...), whose unique
    /// name resolution id is returned.
    pub fn func_opcode_from_ast(&self, name: &ast::CallableName) -> Result<u16, DefId> {
        match name {
            &ast::CallableName::Ins { opcode, .. } => Ok(opcode),  // instruction
            ast::CallableName::Normal { ident, .. } => {
                let def_id = self.resolutions.expect_def(ident);
                match self.defs.func_opcode(def_id) {
                    Some(opcode) => Ok(opcode),  // instruction alias
                    None => Err(def_id),  // something else
                }
            },
        }
    }

    /// Get the signature of any kind of callable function. (instructions, inline and const functions...)
    pub fn func_signature_from_ast(&self, name: &ast::CallableName) -> Result<&Signature, MissingSigError> {
        match *name {
            ast::CallableName::Ins { opcode } => self.defs.ins_signature(opcode),
            ast::CallableName::Normal { ref ident } => self.defs.func_signature(self.resolutions.expect_def(ident)),
        }
    }

    /// Suppress the type sigil of a variable if it is unnecessary.
    pub fn var_simplify_ty_sigil(&self, var: &mut ast::Var) {
        let inherent_ty = self.var_inherent_ty_from_ast(var);
        if let Some(read_ty) = var.ty_sigil {
            if inherent_ty == Some(ScalarType::from(read_ty)) {
                var.ty_sigil = None;
            }
        }
    }

    /// Generate an AST node with the ideal appearance for a register, automatically using
    /// an alias if one exists.
    pub fn reg_to_ast(&self, reg: RegId) -> ast::VarName {
        match self.defs.reg_aliases.get(&reg) {
            None => reg.into(),
            Some(&def_id) => self.defs.var_name(def_id).clone().into(),
        }
    }

    /// Generate an AST node with the ideal appearance for an instruction call,
    /// automatically using an alias if one exists.
    pub fn ins_to_ast(&self, opcode: u16) -> ast::CallableName {
        match self.defs.ins_aliases.get(&opcode) {
            None => ast::CallableName::Ins { opcode },
            Some(&def_id) => ast::CallableName::Normal { ident: self.defs.func_name(def_id).clone() },
        }
    }
}

// =============================================================================

/// Indicates that a function name is an alias for an instruction, but this instruction
/// has no signature available.
///
/// (this error can't really be caught earlier, because we only want to flag instructions that
/// are actually used...)
#[derive(Debug, Clone)]
pub struct MissingSigError { pub opcode: u16 }

/// High-level function signature.
///
/// This contains the information necessary to understand how to apply a function to arguments
/// **at the high level picture of the AST only**.  Examples of things that would use this signature
/// are [the type-checker][`crate::passes::type_check`], [const folding][`crate::passes::const_simplify`],
/// the [virtual machine][`crate::vm::AstVM`], and inlining.
///
/// For low-level information about an instruction, see [`crate::type_system::InstrAbi`].
#[derive(Debug, Clone)]
pub struct Signature {
    pub params: Vec<SignatureParam>,
    pub return_ty: Option<Sp<ScalarType>>,
}

#[derive(Debug, Clone)]
pub struct SignatureParam {
    pub ty: Sp<ScalarType>,
    pub name: Sp<ResIdent>,
    pub default: Option<Sp<ast::Expr>>,
}

impl Signature {
    pub(crate) fn validate(&self, ty_ctx: &TypeSystem) -> Result<(), CompileError> {
        self._check_non_optional_after_optional(ty_ctx)
    }

    fn _check_non_optional_after_optional(&self, ty_ctx: &TypeSystem) -> Result<(), CompileError> {
        let mut first_optional = None;
        for param in self.params.iter() {
            if param.default.is_some() {
                first_optional = Some(&param.name);
            } else if let Some(optional) = first_optional {
                let opt_span = ty_ctx.defs.var_decl_span(ty_ctx.resolutions.expect_def(optional)).expect("func params must have spans");
                let non_span = ty_ctx.defs.var_decl_span(ty_ctx.resolutions.expect_def(&param.name)).expect("func params must have spans");
                return Err(error!(
                    message("invalid function signature"),
                    primary(non_span, "non-optional parameter after optional"),
                    secondary(opt_span, "optional parameter"),
                ));
            }
        }
        Ok(())
    }

    /// Minimum number of arguments accepted.
    pub fn min_args(&self) -> usize {
        self.params.iter().take_while(|param| param.default.is_none()).count()
    }

    /// Maximum number of arguments accepted.
    pub fn max_args(&self) -> usize {
        self.params.len()
    }
}
