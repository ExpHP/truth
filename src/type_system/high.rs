use std::collections::HashMap;
use std::path::PathBuf;
use std::num::NonZeroU64;

use anyhow::Context;

use crate::ast;
use crate::error::{CompileError, SimpleError};
use crate::pos::{Sp, Span};
use crate::ident::{Ident, ResolveId, GensymContext};
use crate::var::{RegId, VarId};
use crate::eclmap::Eclmap;
use crate::type_system::{ScalarType, InstrAbi};

// TODO: document
#[derive(Debug, Clone)]
pub struct TypeSystem {
    mapfiles: Vec<PathBuf>,

    vars: HashMap<ResolveId, VarData>,
    funcs: HashMap<ResolveId, FuncData>,

    ins_abis: HashMap<u16, InstrAbi>,

    // Ids corresponding to raw regs/instrs.  Used to look up their type info without an ident.
    reg_reses: HashMap<RegId, ResolveId>,
    ins_reses: HashMap<u16, ResolveId>,

    // Preferred aliases.  These are used during decompilation to make the output readable.
    reg_aliases: HashMap<RegId, ResolveId>,
    ins_aliases: HashMap<u16, ResolveId>,

    // HACK because we do not yet do name resolution for functions
    func_ident_ids: HashMap<Ident, ResolveId>,

    /// Ids for names available in the global scope.  These form the baseline set of names
    /// available to name resolution.
    global_ids: Vec<ResolveId>,

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
            ins_abis: Default::default(),
            reg_reses: Default::default(),
            ins_reses: Default::default(),
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
    /// Takes an [`Ident`] that has no name resolution id, and assigns it a new one.
    #[track_caller]
    fn make_resolvable(&mut self, mut ident: Ident) -> Ident {
        assert!(ident.res().is_none(), "tried to assign multiple ids to {}", ident);
        ident.set_id(self.unused_ids.next());
        ident
    }

    /// Returns the unique [`ResolveId`] for a raw register. (e.g. `[10004.0]` syntax)
    ///
    /// If the register does not yet have an ID, one will be generated.
    pub fn ensure_reg(&mut self, reg: RegId) -> ResolveId {
        let unused_ids = &mut self.unused_ids;
        *self.reg_reses.entry(reg).or_insert_with(|| unused_ids.next())
    }

    /// Returns the unique [`ResolveId`] for a raw instruction. (e.g. `ins_23` syntax)
    ///
    /// If the instruction does not yet have an ID, one will be generated.
    pub fn ensure_ins(&mut self, opcode: u16) -> ResolveId {
        let unused_ids = &mut self.unused_ids;
        *self.ins_reses.entry(opcode).or_insert_with(|| unused_ids.next())
    }

    /// Set the inherent type of a register.
    ///
    /// Returns the register's ID, which may be newly generated or it may already exist.
    pub fn set_reg_ty(&mut self, reg: RegId, ty: VarType) -> ResolveId {
        let res = self.ensure_reg(reg);
        self.vars.insert(res, VarData {
            ty: Some(ty),
            kind: VarKind::Register { reg },
        });
        res
    }

    /// Add an alias for a register from a mapfile, attaching a brand new ID to the ident.
    ///
    /// The alias will also become the new preferred alias for decompiling that register.
    ///
    /// (this ID is different from the one produced by [`Self::ensure_reg`], and refers to the identifier
    ///  as opposed to raw register syntax)
    pub fn add_global_reg_alias(&mut self, reg: RegId, ident: Ident) -> Ident {
        let ident = self.make_resolvable(ident);
        let res = ident.expect_res();

        self.vars.insert(res, VarData {
            ty: None,
            kind: VarKind::RegisterAlias { reg, ident: ident.clone() },
        });
        self.reg_aliases.insert(reg, res);
        self.global_ids.push(res);
        ident
    }

    /// Declare a local variable, attaching a brand new ID to the ident.
    pub fn add_local(&mut self, ident: Sp<Ident>, ty: VarType) -> Sp<Ident> {
        let ident = sp!(ident.span => self.make_resolvable(ident.value));
        let res = ident.expect_res();

        self.vars.insert(res, VarData {
            ty: Some(ty),
            kind: VarKind::Local { ident: ident.clone() },
        });
        ident
    }

    /// Declare an automatically-generated variable, generating a new ID.
    pub fn add_temporary(&mut self, cause: Span, ty: ScalarType) -> ResolveId {
        let res = self.unused_ids.next();
        self.vars.insert(res, VarData {
            ty: Some(Some(ty)),
            kind: VarKind::Temporary { expr: sp!(cause => ()) },
        });
        res
    }

    /// Set the low-level ABI of an instruction.
    ///
    /// The high-level signature (available through [`Self::func_signature`]) will also automatically
    /// be updated to be consistent with the new ABI.
    ///
    /// Returns the instruction's ID, which may be newly generated or it may already exist.
    pub fn set_ins_abi(&mut self, opcode: u16, abi: InstrAbi) -> ResolveId {
        let siggy = abi.create_signature(self);
        self.ins_abis.insert(opcode, abi);

        siggy.validate(self).expect("invalid signature from InstrAbi");

        let name = self.ensure_ins(opcode);
        self.funcs.insert(name, FuncData {
            sig: Some(siggy),
            kind: FuncKind::Instruction { opcode },
        });
        name
    }

    /// Add an alias for an instruction from a mapfile, attaching a brand new ID for name resolution to the ident.
    ///
    /// The alias will also become the new preferred alias for decompiling that instruction.
    ///
    /// (this ID is different from the one produced by [`Self::ensure_ins`], and refers to the alias
    ///  as opposed to raw `ins_` syntax)
    pub fn add_global_ins_alias(&mut self, opcode: u16, ident: Ident) -> Ident {
        let ident = self.make_resolvable(ident);
        let res = ident.expect_res();

        self.func_ident_ids.insert(ident.clone(), res);
        self.funcs.insert(res, FuncData {
            sig: None,
            kind: FuncKind::InstructionAlias { opcode, ident: ident.clone() },
        });
        self.ins_aliases.insert(opcode, res);
        // self.global_ids.push(res);  FIXME XXX commented out until name resolution handles functions
        ident
    }
}

/// # Global names
impl TypeSystem {
    /// Iterate over all things that are available to the initial (global) scope during
    /// name resolution.
    pub fn globals(&self) -> impl Iterator<Item=ResolveId> + '_ {
        self.global_ids.iter().copied()
    }
}

/// # Recovering low-level information
impl TypeSystem {
    // FIXME delete if not needed
    // /// Get the unique [`ResolveId`] for a raw register, if one has been generated for it.
    // pub fn reg_id(&mut self, reg: RegId) -> Option<ResolveId> {
    //     self.reg_ids.get(&reg).copied()
    // }
    //
    // /// Get the unique [`ResolveId`] for an opcode, if one has been generated for it.
    // pub fn ins_id(&mut self, opcode: u16) -> Option<ResolveId> {
    //     self.ins_ids.get(&opcode).copied()
    // }

    /// Get the register mapped to this variable, if it is a register or an alias for one.
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
            VarData { kind: VarKind::Register { reg, .. }, .. } => Some(reg),
            _ => None,
        }
    }

    /// If this function is an instruction or alias for one, get its opcode.
    ///
    /// Returns `None` for functions that do not represent instructions.
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a function.
    pub fn ins_opcode(&self, res: ResolveId) -> Option<u16> {
        match self.funcs[&res] {
            FuncData { kind: FuncKind::InstructionAlias { opcode, .. }, .. } => Some(opcode),
            FuncData { kind: FuncKind::Instruction { opcode, .. }, .. } => Some(opcode),
        }
    }

    /// Recovers the ABI of an opcode, if it is known.
    pub fn ins_abi(&self, opcode: u16) -> Option<&InstrAbi> {
        self.ins_abis.get(&opcode)
    }
}

/// # Accessing high-level information
impl TypeSystem {
    /// If the variable has an identifier makes it a candidate for name resolution, returns that identifier.
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a variable.
    pub fn var_resolvable_ident(&self, res: ResolveId) -> Option<&Ident> {
        match self.vars[&res] {
            VarData { kind: VarKind::RegisterAlias { ref ident, .. }, .. } => Some(ident),
            VarData { kind: VarKind::Local { ref ident, .. }, .. } => Some(ident),
            VarData { kind: VarKind::Temporary { .. }, .. } => None,
            VarData { kind: VarKind::Register { .. }, .. } => None,
        }
    }

    /// Get the inherent type of any kind of variable. (registers, locals, temporaries, consts)
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a variable.
    pub fn var_inherent_ty(&self, res: ResolveId) -> VarType {
        match self.vars[&res] {
            VarData { kind: VarKind::RegisterAlias { reg, .. }, .. } => {
                match self.reg_reses.get(&reg) {
                    Some(&reg_res) => self.vars[&reg_res].ty.expect("shouldn't be alias"),
                    None => {
                        // This is a register whose type is not in any mapfile.
                        // This is actually fine, and is expected for stack registers.
                        None  // unspecified type
                    },
                }
            },
            VarData { ty, .. } => ty.expect("shouldn't be alias"),
        }
    }

    /// Get the signature of any kind of callable function. (instructions, inline and const functions...)
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a function.
    pub fn func_signature(&self, res: ResolveId) -> Result<&Signature, MissingSigError> {
        match self.funcs[&res] {
            FuncData { kind: FuncKind::InstructionAlias { opcode, .. }, .. } => {
                match self.ins_reses.get(&opcode) {
                    Some(&ins_res) => Ok(self.funcs[&ins_res].sig.as_ref().expect("shouldn't be alias")),
                    None => Err(MissingSigError { opcode }),
                }
            },
            FuncData { ref sig, .. } => Ok(sig.as_ref().expect("shouldn't be alias")),
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
            VarData { kind: VarKind::Register { .. }, .. } => None,
            VarData { kind: VarKind::Temporary { expr, .. }, .. } => Some(expr.span),
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
            FuncData { kind: FuncKind::Instruction { .. }, .. } => None,
        }
    }

    // FIXME FIXME FIXME FIXME
    // FIXME FIXME FIXME FIXME
    // FIXME FIXME FIXME FIXME
    /// Gets the id of a function.  Name resolution has not yet been updated to
    /// apply to functions, so all functions currently have global scope, making this possible.
    pub fn func_ident_id(&self, ident: &Ident) -> ResolveId {
        self.func_ident_ids.get(ident).copied().unwrap_or_else(|| panic!("{}", ident))
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
            self.add_global_ins_alias(opcode as u16, ident.clone());
        }
        for (&opcode, abi_str) in &eclmap.ins_signatures {
            let abi = abi_str.parse().with_context(|| format!("in signature for opcode {}", opcode))?;
            self.set_ins_abi(opcode as u16, abi);
        }
        for (&reg, ident) in &eclmap.gvar_names {
            self.add_global_reg_alias(RegId(reg), ident.clone());
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
struct VarData {
    kind: VarKind,
    /// Inherent type.  `None` for [`VarKind::RegisterAlias`].
    ty: Option<VarType>,
}

#[derive(Debug, Clone)]
enum VarKind {
    Register {
        reg: RegId,
        // TODO: location where type is specified, if any
    },
    RegisterAlias {
        ident: Ident,
        reg: RegId,
        // TODO: location where alias is defined
    },
    Local {
        ident: Sp<Ident>,
    },
    Temporary {
        expr: Sp<()>,
    },
}

#[derive(Debug, Clone)]
struct FuncData {
    kind: FuncKind,
    /// `None` for [`FuncKind::InstructionAlias`].
    sig: Option<Signature>,
}

#[derive(Debug, Clone)]
pub enum FuncKind {
    Instruction {
        opcode: u16,
        // TODO: location where signature is provided
    },
    InstructionAlias {
        ident: Ident,
        opcode: u16,
        // TODO: location where alias is defined
    },
}

// =============================================================================

// FIXME FIXME FIXME FIXME FIXME FIXME
// FIXME FIXME FIXME FIXME FIXME FIXME
// FIXME FIXME FIXME FIXME FIXME FIXME   These should be rewritten to take advantage
// FIXME FIXME FIXME FIXME FIXME FIXME     of new things, but for now I just tried
// FIXME FIXME FIXME FIXME FIXME FIXME     to make it compile.
// FIXME FIXME FIXME FIXME FIXME FIXME
impl TypeSystem {
    /// Get the effective type of a variable at a place where it is referenced.
    ///
    /// This can be different from the variable's innate type.  E.g. an integer global `I0` can be
    /// cast as a float using `%I0`.
    ///
    /// This returns [`ScalarType`] instead of [`ast::VarReadType`] because const vars could be strings.
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

    // FIXME FIXME FIXME FIXME
    // FIXME FIXME FIXME FIXME
    // FIXME FIXME FIXME FIXME
    // FIXME FIXME FIXME FIXME
    fn var_name(&self, var_id: VarId) -> Option<&Ident> {
        match var_id {
            VarId::Local(local) => match &self.vars[&local] {
                VarData { kind: VarKind::Local { ident, .. }, .. } => Some(&ident.value),
                _ => unreachable!(),
            },
            VarId::Reg(reg) => {
                self.reg_aliases.get(&reg).map(|id| match &self.vars[&id] {
                    VarData { kind: VarKind::RegisterAlias { ident, .. }, .. } => ident,
                    _ => unreachable!(),
                })
            },
        }
    }

    pub fn ins_name(&self, opcode: u16) -> Option<&Ident> {
        self.ins_aliases.get(&opcode).map(|&id| match &self.funcs[&id] {
            FuncData { kind: FuncKind::InstructionAlias { ident, .. }, .. } => ident,
            _ => unreachable!(),
        })
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
            VarId::Local(res) => self.var_inherent_ty(res),
            VarId::Reg(reg) => self.reg_reses.get(&reg).and_then(|&id| self.var_inherent_ty(id)),
        }
    }

    /// Generate an AST node with the ideal appearance for a variable.
    ///
    /// If `append_res_ids` is `true`, local variables will get their id numbers appended,
    /// making them distinct.  This is only for testing purposes.
    pub fn var_to_ast(&self, var_id: VarId, read_ty: ScalarType, append_res_ids: bool) -> ast::Var {
        // const simplification should substitute any non-numeric type var reads (like string vars)
        // before this function is ever called.  Probably.
        let explicit_sigil = read_ty.sigil().expect("(bug!) tried to raise read of non-numeric type");

        let name = self.var_name(var_id);
        let name = match (name, var_id) {
            // For registers with no alias, best we can do is emit `[10004]` syntax.  This requires ty_sigil.
            (None, VarId::Reg(_)) => return ast::Var::Resolved { var_id, ty_sigil: Some(explicit_sigil) },

            (Some(name), VarId::Reg(_)) => name.clone(),
            (Some(name), VarId::Local(res)) => match append_res_ids {
                true => format!("{}_{}", name, res),
                false => format!("{}", name),
            }.parse().unwrap(),

            // NOTE: I don't think this should ever show because locals always have names...
            (None, VarId::Local(res)) => format!("__localvar_{}", res).parse().unwrap(),
        };

        // Suppress the type prefix if it matches the default
        if self.var_default_type(var_id) == Some(read_ty) {
            ast::Var::Named { ident: name.clone(), ty_sigil: None }
        } else {
            ast::Var::Named { ident: name.clone(), ty_sigil: Some(explicit_sigil) }
        }
    }

    // FIXME: all uses of gensym should enventually be replaced by ResolveIds, no?
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
    pub name: Ident,
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
}
