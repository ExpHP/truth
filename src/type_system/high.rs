use std::collections::HashMap;
use std::path::PathBuf;
use std::num::NonZeroU64;

use anyhow::Context;

use crate::ast;
use crate::error::{CompileError, SimpleError};
use crate::pos::{Sp, Span};
use crate::ident::{Ident, ResIdent, GensymContext};
use crate::var::{RegId, Namespace, ResolveId};
use crate::eclmap::Eclmap;
use crate::type_system::{ScalarType, InstrAbi};

// TODO: document
#[derive(Debug, Clone)]
pub struct TypeSystem {
    mapfiles: Vec<PathBuf>,

    vars: HashMap<ResolveId, VarData>,
    funcs: HashMap<ResolveId, FuncData>,
    regs: HashMap<RegId, RegData>,
    instrs: HashMap<u16, InsData>,

    // Preferred aliases.  These are used during decompilation to make the output readable.
    reg_aliases: HashMap<RegId, ResolveId>,
    ins_aliases: HashMap<u16, ResolveId>,

    // HACK because we do not yet do name resolution for functions
    func_ident_ids: HashMap<Ident, ResolveId>,

    /// Ids for names available in the global scope.  These form the baseline set of names
    /// available to name resolution.
    ///
    /// NOTE: This is specifically for *externally-defined things* that are defined before name
    /// resolution even begins.  Things like user-defined functions are not included here;
    /// name resolution handles those in the same way it handles anything else.
    global_ids: Vec<(Namespace, ResolveId)>,

    unused_ids: UnusedIds,
    gensym: GensymContext,
}

// =============================================================================

impl TypeSystem {
    pub fn new() -> Self {
        TypeSystem {
            mapfiles: Default::default(),
            vars: Default::default(),
            funcs: Default::default(),
            regs: Default::default(),
            instrs: Default::default(),
            reg_aliases: Default::default(),
            ins_aliases: Default::default(),
            func_ident_ids: Default::default(),
            global_ids: Default::default(),
            unused_ids: UnusedIds(1..),
            gensym: GensymContext::new(),
        }
    }
}

/// # General modification and adding new entries
impl TypeSystem {
    /// Takes a [`ResIdent`] that has no name resolution id, and assigns it a new one.
    #[track_caller]
    fn make_resolvable(&mut self, mut ident: ResIdent) -> ResIdent {
        assert!(ident.res().is_none(), "tried to assign multiple ids to {}", ident);
        ident.set_res(self.unused_ids.next());
        ident
    }

    /// Set the inherent type of a register.
    pub fn set_reg_ty(&mut self, reg: RegId, ty: VarType) {
        self.regs.insert(reg, RegData { ty });
    }

    /// Add an alias for a register from a mapfile, attaching a brand new ID to the ident.
    ///
    /// The alias will also become the new preferred alias for decompiling that register.
    pub fn add_global_reg_alias(&mut self, reg: RegId, ident: ResIdent) -> ResIdent {
        let ident = self.make_resolvable(ident);
        let res = ident.expect_res();

        self.vars.insert(res, VarData {
            ty: None,
            kind: VarKind::RegisterAlias { reg, ident: ident.clone() },
        });
        self.reg_aliases.insert(reg, res);
        self.global_ids.push((Namespace::Vars, res));
        ident
    }

    /// Declare a local variable, attaching a brand new ID to the ident.
    pub fn add_local(&mut self, ident: Sp<ResIdent>, ty: VarType) -> Sp<ResIdent> {
        let ident = sp!(ident.span => self.make_resolvable(ident.value));
        let res = ident.expect_res();

        self.vars.insert(res, VarData {
            ty: Some(ty),
            kind: VarKind::Local { ident: ident.clone() },
        });
        ident
    }

    /// Set the low-level ABI of an instruction.
    pub fn set_ins_abi(&mut self, opcode: u16, abi: InstrAbi) {
        // also update the high-level signature
        let sig = abi.create_signature(self);
        sig.validate(self).expect("invalid signature from InstrAbi");

        self.instrs.insert(opcode, InsData { abi, sig });
    }

    /// Add an alias for an instruction from a mapfile, attaching a brand new ID for name resolution to the ident.
    ///
    /// The alias will also become the new preferred alias for decompiling that instruction.
    pub fn add_global_ins_alias(&mut self, opcode: u16, ident: ResIdent) -> ResIdent {
        let ident = self.make_resolvable(ident);
        let res = ident.expect_res();

        self.funcs.insert(res, FuncData {
            sig: None,
            kind: FuncKind::InstructionAlias { opcode, ident: ident.clone() },
        });
        self.ins_aliases.insert(opcode, res);
        self.global_ids.push((Namespace::Funcs, res));
        ident
    }

    /// Add a user-defined function.
    ///
    /// FIXME: Should take signature, inline/const-ness, etc.
    pub fn add_user_func(&mut self, ident: Sp<ResIdent>) -> Sp<ResIdent> {
        let ident = sp!(ident.span => self.make_resolvable(ident.value));
        let res = ident.expect_res();

        self.funcs.insert(res, FuncData {
            sig: None,  // FIXME
            kind: FuncKind::User { ident: ident.clone() },
        });
        ident
    }
}

/// # Global names
impl TypeSystem {
    /// Iterate over all things that are available to the initial (global) scope during
    /// name resolution.
    pub fn globals(&self) -> impl Iterator<Item=(Namespace, ResolveId)> + '_ {
        self.global_ids.iter().copied()
    }
}

/// # Recovering low-level information
impl TypeSystem {
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
    pub fn var_reg(&self, res: ResolveId) -> Option<RegId> {
        match self.vars[&res] {
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
    pub fn func_opcode(&self, res: ResolveId) -> Option<u16> {
        match self.funcs[&res] {
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
impl TypeSystem {
    /// Get the identifier that makes something a candidate for name resolution.
    ///
    /// # Panics
    ///
    /// Panics if the namespace is wrong.
    ///
    /// (FIXME: this is silly because TypeSystem ought to know what namespace each
    ///         id belongs to without having to be reminded...)
    pub fn name(&self, ns: Namespace, res: ResolveId) -> &ResIdent {
        match ns {
            Namespace::Vars => self.var_name(res),
            Namespace::Funcs => self.func_name(res),
        }
    }

    /// Get the fully-resolved name of a variable.
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a variable.
    pub fn var_name(&self, res: ResolveId) -> &ResIdent {
        match self.vars[&res] {
            VarData { kind: VarKind::RegisterAlias { ref ident, .. }, .. } => ident,
            VarData { kind: VarKind::Local { ref ident, .. }, .. } => ident,
        }
    }

    /// Get the fully resolved name of a function.
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a variable.
    pub fn func_name(&self, res: ResolveId) -> &ResIdent {
        match self.funcs[&res] {
            FuncData { kind: FuncKind::InstructionAlias { ref ident, .. }, .. } => ident,
            FuncData { kind: FuncKind::User { ref ident, .. }, .. } => ident,
        }
    }

    /// Get the inherent type of any kind of named variable. (register aliases, locals, temporaries, consts)
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a variable.
    pub fn var_inherent_ty(&self, res: ResolveId) -> VarType {
        match self.vars[&res] {
            VarData { kind: VarKind::RegisterAlias { reg, .. }, .. } => self.reg_inherent_ty(reg),
            VarData { ty, .. } => ty.expect("shouldn't be alias"),
        }
    }

    /// Get the signature of any kind of named function. (instruction aliases, inline and const functions...)
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a function.
    pub fn func_signature(&self, res: ResolveId) -> Result<&Signature, MissingSigError> {
        match self.funcs[&res] {
            FuncData { kind: FuncKind::InstructionAlias { opcode, .. }, .. } => self.ins_signature(opcode),
            FuncData { kind: FuncKind::User { .. }, .. } => unimplemented!("need to create signatures for user funcs!"),
        }
    }

    /// Get the signature of any kind of callable function. (instructions, inline and const functions...)
    pub fn func_signature_from_ast(&self, name: &ast::CallableName) -> Result<&Signature, MissingSigError> {
        match *name {
            ast::CallableName::Ins { opcode } => self.ins_signature(opcode),
            ast::CallableName::Normal { ref ident } => self.func_signature(ident.expect_res()),
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
    pub fn var_decl_span(&self, res: ResolveId) -> Option<Span> {
        match &self.vars[&res] {
            VarData { kind: VarKind::RegisterAlias { .. }, .. } => None,
            VarData { kind: VarKind::Local { ident, .. }, .. } => Some(ident.span),
        }
    }

    /// Get the span of the ident at the declaration site for any kind of function,
    /// if there is such an ident.
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a function.
    pub fn func_decl_span(&self, res: ResolveId) -> Option<Span> {
        match &self.funcs[&res] {
            FuncData { kind: FuncKind::InstructionAlias { .. }, .. } => None,
            FuncData { kind: FuncKind::User { ident, .. }, .. } => Some(ident.span),
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
            self.add_global_ins_alias(opcode as u16, ResIdent::from(ident.clone()));
        }
        for (&opcode, abi_str) in &eclmap.ins_signatures {
            let abi = abi_str.parse().with_context(|| format!("in signature for opcode {}", opcode))?;
            self.set_ins_abi(opcode as u16, abi);
        }
        for (&reg, ident) in &eclmap.gvar_names {
            self.add_global_reg_alias(RegId(reg), ResIdent::from(ident.clone()));
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

// Really small helper that *would* have just been a `fn next_res_id(&mut self) -> ResolveId` helper method
// on TypeSystem, but can't be because we want to call it in places where other fields of self are borrowed.
#[derive(Debug, Clone)]
struct UnusedIds(std::ops::RangeFrom<u64>);
impl UnusedIds {
    fn next(&mut self) -> ResolveId {
        let num = self.0.next().expect("too many names!");
        ResolveId(NonZeroU64::new(num).expect("range started from 1"))
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
    pub fn var_read_ty_from_ast(&self, var: &Sp<ast::Var>) -> VarType {
        match var.value {
            ast::Var::Reg { ty_sigil, .. } => Some(ty_sigil.into()),
            ast::Var::Named { ty_sigil: Some(ty_sigil), .. } => Some(ty_sigil.into()),
            ast::Var::Named { ty_sigil: None, ref ident } => self.var_inherent_ty(ident.expect_res()),
        }
    }

    /// Get the innate type of a variable at a place where it is referenced, ignoring its sigils.
    ///
    /// `None` means it has no inherent type. (is untyped, e.g. via `var` keyword)
    pub fn var_inherent_ty_from_ast(&self, var: &Sp<ast::Var>) -> VarType {
        match var.value {
            ast::Var::Reg { reg, .. } => self.reg_inherent_ty(reg),
            ast::Var::Named { ref ident, .. } => self.var_inherent_ty(ident.expect_res()),
        }
    }

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

    /// If the variable is a register or register alias, gets the associated register id.
    ///
    /// Otherwise, it must be something else (e.g. a local, a const...), whose unique
    /// name resolution id is returned.
    pub fn var_reg_from_ast(&self, var: &ast::Var) -> Result<RegId, ResolveId> {
        match var {
            &ast::Var::Reg { reg, .. } => Ok(reg),  // register
            ast::Var::Named { ident, .. } => {
                match self.var_reg(ident.expect_res()) {
                    Some(reg) => Ok(reg),  // register alias
                    None => Err(ident.expect_res()),  // something else
                }
            },
        }
    }

    /// If the function name is an instruction or instruction alias, gets the associated register id.
    ///
    /// Otherwise, it must be something else (e.g. a local, a const...), whose unique
    /// name resolution id is returned.
    pub fn func_opcode_from_ast(&self, name: &ast::CallableName) -> Result<u16, ResolveId> {
        match name {
            &ast::CallableName::Ins { opcode, .. } => Ok(opcode),  // instruction
            ast::CallableName::Normal { ident, .. } => {
                match self.func_opcode(ident.expect_res()) {
                    Some(opcode) => Ok(opcode),  // instruction alias
                    None => Err(ident.expect_res()),  // something else
                }
            },
        }
    }

    /// Produces a var from a name-resolved ident, suppressing the type sigil if it is unnecessary.
    fn nice_ident_to_var(&self, ident: ResIdent, read_ty: ast::VarReadType) -> ast::Var {
        let inherent_ty = self.var_inherent_ty(ident.expect_res());
        match inherent_ty == Some(ScalarType::from(read_ty)) {
            true => ast::Var::Named { ident, ty_sigil: None },
            false => ast::Var::Named { ident, ty_sigil: Some(read_ty) },
        }
    }

    /// Generate an AST node with the ideal appearance for a register, automatically using
    /// an alias if one exists.
    pub fn reg_to_ast(&self, reg: RegId, read_ty: ast::VarReadType) -> ast::Var {
        match self.reg_aliases.get(&reg) {
            None => ast::Var::Reg { reg, ty_sigil: read_ty },
            Some(&res) => {
                let ident = self.var_name(res).clone();
                self.nice_ident_to_var(ident, read_ty)
            },
        }
    }

    /// Generate an AST node with the ideal appearance for an instruction call,
    /// automatically using an alias if one exists.
    pub fn ins_to_ast(&self, opcode: u16) -> ast::CallableName {
        match self.ins_aliases.get(&opcode) {
            None => ast::CallableName::Ins { opcode },
            Some(&res) => ast::CallableName::Normal { ident: self.func_name(res).clone() },
        }
    }

    /// Generate a new, raw identifier.
    ///
    /// E.g. for a prefix of `"temp_"`, this could create an ident like `"temp_23"`.
    ///
    /// In an ideal world, this perhaps wouldn't be needed, since we already have [`ResolveId`]
    /// for representing unique identifiers.  But we need it anyways since those ids are stored
    /// on [`ResIdent`], which requires an [`Ident`].
    ///
    /// FIXME: The generated name can potentially clash with existing user-defined names.
    /// For now, to protect against this, any identifier that is gensym-ed should either be a
    /// [`ResIdent`] (and have a new [`ResolveId`] assigned to it immediately), or it should
    /// contain a non-identifier character.
    pub fn gensym(&mut self, prefix: &str) -> Ident {
        self.gensym.gensym(prefix)
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
                first_optional = Some(param.name.clone());
            } else if let Some(optional) = first_optional {
                let opt_span = ty_ctx.var_decl_span(optional.expect_res()).expect("func params must have spans");
                let non_span = ty_ctx.var_decl_span(param.name.expect_res()).expect("func params must have spans");
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