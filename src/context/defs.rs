use std::collections::HashMap;

use crate::ast;
use crate::context::CompilerContext;
use crate::diagnostic::{unspanned, UnspannedEmitter};
use crate::error::{GatherErrorIteratorExt, ErrorReported};
use crate::pos::{Sp, Span};
use crate::ident::{Ident, ResIdent};
use crate::resolve::{RegId, Namespace, DefId, ResId, rib};
use crate::eclmap::Eclmap;
use crate::value::{ScalarType, VarType, ExprType};
use crate::llir::InstrAbi;

/// Retains information about all definitions in the program.
///
/// This object is responsible for storing information that is immediately available at the definition
/// site of a variable or function, such as: type information, spans, function signatures, expressions
/// for consts.
///
/// It is also currently the type responsible for holding type information about registers and opcodes,
/// despite these not having [`DefId`]s.
///
/// **Note:** The methods for creating new definitions are currently on [`CompilerContext`], where they can
/// more easily record information for name resolution.
#[derive(Debug, Clone)]
pub struct Defs {
    regs: HashMap<RegId, RegData>,
    instrs: HashMap<u16, InsData>,

    vars: HashMap<DefId, VarData>,
    funcs: HashMap<DefId, FuncData>,

    /// Preferred alias (i.e. the one we decompile to) for each register.
    reg_aliases: HashMap<RegId, DefId>,
    /// Preferred alias (i.e. the one we decompile to) for each instruction.
    ins_aliases: HashMap<u16, DefId>,

    /// One of the initial ribs for name resolution, containing register aliases from mapfiles.
    reg_alias_rib: rib::Rib,
    /// One of the initial ribs for name resolution, containing instruction aliases from mapfiles.
    ins_alias_rib: rib::Rib,
    /// One of the initial ribs for name resolution, containing consts from meta.
    auto_const_rib: rib::Rib,
}

// =============================================================================

impl Default for Defs {
    fn default() -> Self {
        use rib::{Rib, RibKind};

        Defs {
            regs: Default::default(),
            instrs: Default::default(),
            vars: Default::default(),
            funcs: Default::default(),
            reg_aliases: Default::default(),
            ins_aliases: Default::default(),
            reg_alias_rib: Rib::new(Namespace::Vars, RibKind::Mapfile),
            ins_alias_rib: Rib::new(Namespace::Funcs, RibKind::Mapfile),
            auto_const_rib: Rib::new(Namespace::Vars, RibKind::Generated),
        }
    }
}

impl Defs {
    pub fn new() -> Self { Default::default() }
}

/// # Definitions
impl CompilerContext<'_> {
    /// Set the inherent type of a register.
    pub fn set_reg_ty(&mut self, reg: RegId, ty: VarType) {
        self.defs.regs.insert(reg, RegData { ty });
    }

    /// Add an alias for a register from a mapfile.
    ///
    /// The alias will also become the new preferred alias for decompiling that register.
    pub fn define_global_reg_alias(&mut self, reg: RegId, ident: Ident) -> DefId {
        let res_ident = self.resolutions.attach_fresh_res(ident.clone());
        let def_id = self.create_new_def_id(&res_ident);

        self.defs.vars.insert(def_id, VarData {
            ty: None,
            kind: VarKind::RegisterAlias { reg, ident: res_ident },
        });
        self.defs.reg_aliases.insert(reg, def_id);

        if let Err(old) = self.defs.reg_alias_rib.insert(sp!(ident.clone()), def_id) {
            let old_reg = self.defs.var_reg(old.def_id).unwrap();
            if old_reg != reg {
                self.diagnostics.emit(warning!("name '{}' used for multiple registers in mapfiles: {}, {}", ident, old_reg, reg)).ignore();
            }
        }

        def_id
    }

    /// Declare a local variable, resolving the ident to a brand new [`DefId`].
    pub fn define_local(&mut self, ident: Sp<ResIdent>, ty: VarType) -> DefId {
        let def_id = self.create_new_def_id(&ident);

        self.defs.vars.insert(def_id, VarData {
            ty: Some(ty),
            kind: VarKind::Local { ident },
        });
        def_id
    }

    /// Declare an automatic const, resolving the ident to a brand new [`DefId`].
    ///
    /// Automatic consts are language-specific consts generated from certain syntactic features
    /// that don't normally generate consts in other languages.  ANM sprites (which come from the
    /// `id:` fields in the `entry` meta) and ANM script IDs (which come from `script` items) are
    /// the most notable examples.
    ///
    /// Automatic consts have the unusual property that name clashes are allowed, but only if they
    /// equate to the same value.  This is useful for ANM sprites appearing in decompiled code, as
    /// there may be e.g. multiple `sprite10`s all with an ID of `10`.
    pub fn define_auto_const_var(&mut self, ident: Sp<ResIdent>, ty: ScalarType, expr: Sp<ast::Expr>) -> DefId {
        let def_id = self.define_const_var(ident.clone(), ty, expr);

        if let Err(old) = self.defs.auto_const_rib.insert(ident.clone(), def_id) {
            self.consts.defer_equality_check(self.defs.auto_const_rib.noun(), old.def_id, def_id);
        }
        def_id
    }

    /// Declare a compile-time constant variable, resolving the ident to a brand new [`DefId`].
    pub fn define_const_var(&mut self, ident: Sp<ResIdent>, ty: ScalarType, expr: Sp<ast::Expr>) -> DefId {
        let def_id = self.create_new_def_id(&ident);

        self.defs.vars.insert(def_id, VarData {
            ty: Some(VarType::Typed(ty)),
            kind: VarKind::Const { ident: ident.clone(), expr },
        });
        self.consts.defer_evaluation_of(def_id);
        def_id
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

    /// Add an alias for an instruction from a mapfile.  If this ident has been used previously, the old opcode
    /// is also returned.
    ///
    /// The alias will also become the new preferred alias for decompiling that instruction.
    pub fn define_global_ins_alias(&mut self, opcode: u16, ident: Ident) -> (DefId, Option<u16>) {
        let res_ident = self.resolutions.attach_fresh_res(ident.clone());
        let def_id = self.create_new_def_id(&res_ident);

        self.defs.funcs.insert(def_id, FuncData {
            sig: None,
            kind: FuncKind::InstructionAlias { opcode, ident: res_ident },
        });
        self.defs.ins_aliases.insert(opcode, def_id);

        let old_opcode = match self.defs.ins_alias_rib.insert(sp!(ident.clone()), def_id) {
            Err(old) => Some(self.defs.func_opcode(old.def_id).unwrap()),
            Ok(_) => None,
        };
        (def_id, old_opcode)
    }

    /// Add a user-defined function, resolving the ident to a brand new [`DefId`]
    pub fn define_user_func(
        &mut self,
        ident: Sp<ResIdent>,
        qualifier: Option<Sp<ast::FuncQualifier>>,
        siggy: Signature,
    ) -> DefId {
        let def_id = self.create_new_def_id(&ident);

        self.defs.funcs.insert(def_id, FuncData {
            sig: Some(siggy),
            kind: FuncKind::User { ident, qualifier },
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
            VarData { ty, .. } => ty.expect("not alias"),
        }
    }

    /// Get the inherent type of a register.
    fn reg_inherent_ty(&self, reg: RegId) -> VarType {
        match self.regs.get(&reg) {
            Some(&RegData { ty }) => ty,
            // This is a register whose type is not in any mapfile.
            // This is actually fine, and is expected for stack registers.
            None => VarType::Untyped,
        }
    }

    /// Get the signature of any kind of named function. (instruction aliases, inline and const functions...)
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a function.
    pub fn func_signature(&self, def_id: DefId) -> Result<&Signature, InsMissingSigError> {
        match self.funcs[&def_id] {
            FuncData { kind: FuncKind::InstructionAlias { opcode, .. }, .. } => self.ins_signature(opcode),
            FuncData { ref sig, .. } => Ok(sig.as_ref().expect("not alias")),
        }
    }

    /// Get the high-level signature of an instruction.
    fn ins_signature(&self, opcode: u16) -> Result<&Signature, InsMissingSigError> {
        match self.instrs.get(&opcode) {
            Some(InsData { sig, .. }) => Ok(sig),
            None => Err(InsMissingSigError { opcode }),
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
    pub fn var_const_expr(&self, def_id: DefId) -> Option<&Sp<ast::Expr>> {
        match &self.vars[&def_id] {
            VarData { kind: VarKind::Const { expr, .. }, .. } => Some(expr),
            _ => None,
        }
    }
}

impl CompilerContext<'_> {
    /// Add info from an eclmap.
    ///
    /// Its path (if one is provided) is recorded in order to emit import directives into a decompiled script file.
    pub fn extend_from_eclmap(&mut self, path: Option<&std::path::Path>, eclmap: &Eclmap) -> Result<(), ErrorReported> {
        let emitter = {
            let error_label = match path {
                Some(path) => path.to_string_lossy().into_owned(),
                None => format!("in mapfile"),
            };
            unspanned::make_root(error_label, self.diagnostics)
        };

        if let Some(path) = path {
            self.mapfiles.push(path.to_owned());
        }

        for (&opcode, ident) in &eclmap.ins_names {
            let (_, old_opcode) = self.define_global_ins_alias(opcode as u16, ident.clone());
            if let Some(old_opcode) = old_opcode {
                if opcode as u16 != old_opcode {
                    emitter.emit(warning!("name '{}' used for multiple opcodes: {}, {}", ident, old_opcode, opcode)).ignore();
                }
            }
        }

        eclmap.ins_signatures.iter().map(|(&opcode, abi_str)| {
            emitter.chain_with(|f| write!(f, "in signature for opcode {}", opcode), |emitter| {
                let abi = abi_str.parse().map_err(|e| emitter.emit(e))?;
                self.set_ins_abi(opcode as u16, abi);
                Ok::<_, ErrorReported>(())
            })
        }).collect_with_recovery()?;

        for (&reg, ident) in &eclmap.gvar_names {
            self.define_global_reg_alias(RegId(reg), ident.clone());
        }

        for (&reg, value) in &eclmap.gvar_types {
            let ty = match &value[..] {
                "%" => VarType::Typed(ScalarType::Float),
                "$" => VarType::Typed(ScalarType::Int),
                _ => {
                    emitter.emit(warning!("ignoring invalid variable type '{}' for gvar {}", value, reg)).ignore();
                    continue;
                },
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

impl Defs {
    /// Get the initial ribs for name resolution.
    pub fn initial_ribs(&self) -> Vec<rib::Rib> {
        vec![
            self.ins_alias_rib.clone(),
            self.reg_alias_rib.clone(),
            self.auto_const_rib.clone(),
        ]
    }
}

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
        expr: Sp<ast::Expr>,
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
        qualifier: Option<Sp<ast::FuncQualifier>>,
    }
}

// =============================================================================

impl CompilerContext<'_> {
    /// Get the effective type of a variable at a place where it is referenced.
    ///
    /// This can be different from the variable's innate type.  E.g. an integer global `I0` can be
    /// cast as a float using `%I0`.
    ///
    /// This returns [`ScalarType`] instead of [`ast::VarReadType`] because const vars could be strings.
    pub fn var_read_ty_from_ast(&self, var: &ast::Var) -> VarType {
        match var.ty_sigil {
            Some(sigil) => VarType::Typed(sigil.into()),
            None => self.var_inherent_ty_from_ast(var),
        }
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
    pub fn func_signature_from_ast(&self, name: &ast::CallableName) -> Result<&Signature, InsMissingSigError> {
        match *name {
            ast::CallableName::Ins { opcode } => self.defs.ins_signature(opcode),
            ast::CallableName::Normal { ref ident } => self.defs.func_signature(self.resolutions.expect_def(ident)),
        }
    }

    /// Suppress the type sigil of a variable if it is unnecessary.
    pub fn var_simplify_ty_sigil(&self, var: &mut ast::Var) {
        let inherent_ty = self.var_inherent_ty_from_ast(var);
        if let Some(sigil) = var.ty_sigil {
            if inherent_ty == VarType::Typed(ScalarType::from(sigil)) {
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
pub struct InsMissingSigError { pub opcode: u16 }

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
    pub return_ty: Sp<ExprType>,
}

#[derive(Debug, Clone)]
pub struct SignatureParam {
    pub ty: Sp<VarType>,
    pub name: Sp<ResIdent>,
    pub default: Option<Sp<ast::Expr>>,
}

impl Signature {
    pub fn from_func_params(ty_keyword: Sp<ast::TypeKeyword>, params: &[ast::FuncParam]) -> Self {
        signature_from_func_ast(ty_keyword, params)
    }

    pub(crate) fn validate(&self, ctx: &CompilerContext) -> Result<(), ErrorReported> {
        self._check_non_optional_after_optional(ctx)
    }

    fn _check_non_optional_after_optional(&self, ctx: &CompilerContext) -> Result<(), ErrorReported> {
        let mut first_optional = None;
        for param in self.params.iter() {
            if param.default.is_some() {
                first_optional = Some(&param.name);
            } else if let Some(optional) = first_optional {
                let opt_span = ctx.defs.var_decl_span(ctx.resolutions.expect_def(optional)).expect("func params must have spans");
                let non_span = ctx.defs.var_decl_span(ctx.resolutions.expect_def(&param.name)).expect("func params must have spans");
                return Err(ctx.diagnostics.emit(error!(
                    message("invalid function signature"),
                    primary(non_span, "non-optional parameter after optional"),
                    secondary(opt_span, "optional parameter"),
                )));
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

fn signature_from_func_ast(return_ty_keyword: Sp<ast::TypeKeyword>, params: &[ast::FuncParam]) -> Signature {
    Signature {
        params: params.iter().map(|(ty_keyword, ident)| SignatureParam {
            ty: ty_keyword.sp_map(ast::TypeKeyword::var_ty),
            name: ident.clone(),
            default: None,
        }).collect(),
        return_ty: return_ty_keyword.sp_map(ast::TypeKeyword::expr_ty),
    }
}
