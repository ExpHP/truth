use enum_map::{EnumMap, enum_map};
use indexmap::IndexMap;
use core::fmt;

use crate::raw;
use crate::ast;
use crate::context::{self, CompilerContext};
use crate::error::{GatherErrorIteratorExt, ErrorReported};
use crate::pos::{Sp, Span, SourceStr};
use crate::game::{Game, LanguageKey};
use crate::ident::{Ident, ResIdent};
use crate::resolve::{RegId, Namespace, DefId, NodeId, LoopId, ConstId, AliasableId, IdMap, id_map, rib};
use crate::mapfile::Mapfile;
use crate::value::{ScalarValue, ScalarType, VarType, ExprType};
use crate::llir::{InstrAbi, IntrinsicInstrKind};

/// Bit representation of the NAN constant in the compiler.
pub const CANONICAL_NAN_BITS: u32 = 0x7FC0_0000;

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
    regs: IdMap<(LanguageKey, RegId), RegData>,
    instrs: IdMap<(LanguageKey, raw::Opcode), InsData>,

    vars: IdMap<DefId, VarData>,
    funcs: IdMap<DefId, FuncData>,
    enums: IdMap<Ident, EnumData>,

    /// Preferred alias (i.e. the one we decompile to) for each register.
    reg_aliases: IdMap<(LanguageKey, RegId), DefId>,
    /// Preferred alias (i.e. the one we decompile to) for each instruction.
    ins_aliases: IdMap<(LanguageKey, raw::Opcode), DefId>,

    global_ribs: GlobalRibs,

    /// Intrinsics from mapfiles.
    intrinsic_instrs: EnumMap<LanguageKey, Vec<(raw::Opcode, Sp<IntrinsicInstrKind>)>>,

    /// Maps enum const names to their enum if they are unique, or to None if they are shared by
    /// multiple enums.
    unique_enums: IdMap<Ident, Option<Ident>>,

    /// The first name resolution pass maps all enum consts to this.
    enum_const_dummy_def_id: Option<DefId>,
}

/// Ribs for the global scope, which are built incrementally as things are defined.
#[derive(Debug, Clone)]
pub struct GlobalRibs {
    /// Some of the initial ribs for name resolution, containing register aliases from mapfiles.
    reg_alias_ribs: EnumMap<LanguageKey, rib::Rib>,
    /// Some of the initial ribs for name resolution, containing instruction aliases from mapfiles.
    ins_alias_ribs: EnumMap<LanguageKey, rib::Rib>,
    /// One of the initial ribs for name resolution, containing consts from enums.
    enum_const_rib: rib::Rib,
    /// One of the initial ribs for name resolution, containing consts like INF.
    builtin_const_rib: rib::Rib,
}

pub mod auto_enum_names {
    use super::*;

    macro_rules! define_auto_enum_names {
        ($( $const_func_name:ident => $ident_str:literal, )*) => {
            $( pub fn $const_func_name() -> Ident { ident!($ident_str) } )*

            pub fn all() -> Vec<Ident> {
                vec![ $($const_func_name()),* ]
            }
        }
    }

    define_auto_enum_names!{
        anm_sprite => "AnmSprite",
        ecl_sub => "EclSub",
        msg_script => "MsgScript",
        anm_script => "AnmScript",
        color_format => "BitmapColorFormat",
        bool => "bool",
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
        language: LanguageKey,
        reg: RegId,
        // TODO: location where alias is defined, follow the example set by InstrAbiLoc
    },
    Local {
        /// NOTE: For auto-generated temporaries, the span may point to their expression instead.
        ident: Sp<ResIdent>,
    },
    BuiltinConst {
        ident: ResIdent,
        expr: ast::Expr,
    },
    Const {
        ident: Sp<ResIdent>,
        expr: Sp<ast::Expr>,
    },
    // FIXME: Strictly speaking, enum consts are not vars, so this perhaps doesn't belong here.
    //        However, assigning them DefIds and storing their expressions in here is very
    //        convenient for the const evaluator.
    EnumConst {
        #[allow(unused)]
        enum_name: Sp<Ident>,
        ident: Sp<ResIdent>,
        expr: Sp<ast::Expr>,
    },
    /// All unqualified enum consts map to this initially during name resolution.
    EnumConstDummy,
}

#[derive(Debug, Clone)]
pub enum ConstExprLoc {
    Span(Span),  // string in a mapfile
    Builtin,
}

impl From<Span> for ConstExprLoc {
    fn from(s: Span) -> Self { ConstExprLoc::Span(s) }
}

#[derive(Debug, Clone)]
struct InsData {
    abi_loc: InstrAbiLoc,
    abi: InstrAbi,
    sig: Signature,
}

/// Diagnostic information about where an instruction ABI is defined.
#[derive(Debug, Clone)]
pub enum InstrAbiLoc {
    Span(Span),  // string in a mapfile
    CoreMapfile {
        language: LanguageKey,
        opcode: raw::Opcode,
        abi_str: String,
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
    InstructionAlias {
        ident: ResIdent,
        language: LanguageKey,
        opcode: raw::Opcode,
        // TODO: location where alias is defined
    },
    User {
        ident: Sp<ResIdent>,
        qualifier: Option<Sp<ast::FuncQualifier>>,
    },
}

#[derive(Debug, Clone, Default)]
struct EnumData {
    /// Tracks all consts defined for this enum. Later entries in the IndexMap take priority
    /// during decompilation.
    ///
    /// (Under normal circumstances, Defs would prefer not to use IndexMap, and to instead
    /// track the latest name for each value (e.g. a `i32 -> Ident` map).  But in the future
    /// when we have standard enum syntax, the consts will be able to be arbitrary exprs which
    /// require a const evaluation pass.
    consts: IndexMap<Sp<Ident>, ConstId>,
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
            enums: auto_enum_names::all().into_iter().map(|enum_name| (enum_name, Default::default())).collect(),
            reg_aliases: Default::default(),
            ins_aliases: Default::default(),
            global_ribs: GlobalRibs {
                reg_alias_ribs: enum_map![language => Rib::new(Namespace::Vars, RibKind::Mapfile { language })],
                ins_alias_ribs: enum_map![language => Rib::new(Namespace::Funcs, RibKind::Mapfile { language })],
                enum_const_rib: Rib::new(Namespace::Vars, RibKind::EnumConsts),
                builtin_const_rib: Rib::new(Namespace::Vars, RibKind::BuiltinConsts),
            },
            intrinsic_instrs: Default::default(),
            unique_enums: Default::default(),
            enum_const_dummy_def_id: None,
        }
    }
}

impl Defs {
    pub fn new() -> Self { Default::default() }
}

/// # Definitions
impl CompilerContext<'_> {
    /// Set the inherent type of a register.
    pub fn set_reg_ty(&mut self, language: LanguageKey, reg: RegId, ty: VarType) {
        self.defs.regs.insert((language, reg), RegData { ty });
    }

    /// Add an alias for a register from a mapfile.
    ///
    /// The alias will also become the new preferred alias for decompiling that register.
    pub fn define_global_reg_alias(&mut self, language: LanguageKey, reg: RegId, ident: Sp<Ident>) -> DefId {
        let res_ident = self.resolutions.attach_fresh_res(ident.value.clone());
        let def_id = self.create_new_def_id(&res_ident);

        self.defs.vars.insert(def_id, VarData {
            ty: None,
            kind: VarKind::RegisterAlias { language, reg, ident: res_ident },
        });
        self.defs.reg_aliases.insert((language, reg), def_id);

        if let Err(old) = self.defs.global_ribs.reg_alias_ribs[language].insert(sp!(ident.clone()), def_id) {
            let old_reg = self.defs.var_reg(old.def_id).unwrap().1;
            if old_reg != reg {
                self.emitter.emit(warning!(
                    "name '{}' used for multiple registers in mapfiles: {}, {}",
                    ident, old_reg, reg,
                )).ignore();
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

    /// Declare an enum const without a span, creating a brand new [`ConstId`].
    ///
    /// This alternative to [`Self::define_enum_const`] takes simpler arguments and is designed
    /// for use during decompilation.
    pub fn define_enum_const_fresh(&mut self, ident: Ident, value: i32, enum_name: Ident) -> ConstId {
        let res_ident = self.resolutions.attach_fresh_res(ident);
        self.define_enum_const(sp!(res_ident), sp!(value.into()), sp!(enum_name))
    }

    /// Declare an enum.  This may be done multiple times.
    pub fn declare_enum(&mut self, ident: Sp<Ident>) {
        self.defs.enums.entry(ident.value.clone()).or_insert_with(Default::default);
    }

    /// Declare an enum const, creating a brand new [`ConstId`].
    ///
    /// Panics if the enum has not been declared.
    ///
    /// Enums have the property that name clashes are allowed within an enum type, but only if
    /// they equate to the same value.  This is useful for ANM sprites appearing in decompiled code,
    /// as there may be e.g. multiple `sprite10`s all with an ID of `10`.
    pub fn define_enum_const(&mut self, res_ident: Sp<ResIdent>, value: Sp<ast::Expr>, enum_name: Sp<Ident>) -> ConstId {
        let ident = sp!(res_ident.span => res_ident.as_raw().clone());
        let def_id = self.create_new_def_id(&res_ident);
        let const_id = self.consts.defer_evaluation_of(def_id);

        self.defs.vars.insert(def_id, VarData {
            ty: Some(VarType::Typed(ScalarType::Int)),
            kind: VarKind::EnumConst {
                enum_name: enum_name.clone(),
                ident: res_ident,
                expr: value,
            },
        });

        let this_enum_data = self.defs.enums.get_mut(&enum_name.value).expect("enum not defined");
        if let Some(old_const_id) = this_enum_data.consts.insert(ident.clone(), const_id) {
            // redefinition of this name within this enum
            self.consts.defer_equality_check("enum const", old_const_id, const_id);
        } else {
            // first definition within this enum
            match self.defs.unique_enums.entry(ident.value.clone()) {
                id_map::Entry::Occupied(mut entry) => {
                    // mark as ambiguous, replacing whatever's already there
                    entry.insert(None);
                },
                id_map::Entry::Vacant(entry) => {
                    entry.insert(Some(enum_name.value.clone()));
                },
            }
        }

        let _ = self.defs.global_ribs.enum_const_rib.insert(ident.clone(), self.defs.enum_const_dummy_def_id());

        const_id
    }

    /// Define a const like `INF`.
    pub fn define_builtin_const_var(&mut self, ident: Ident, value: ScalarValue) -> ConstId {
        let ident = self.resolutions.attach_fresh_res(ident);
        let def_id = self.create_new_def_id(&ident);

        self.defs.vars.insert(def_id, VarData {
            ty: Some(VarType::Typed(value.ty())),
            kind: VarKind::BuiltinConst { ident: ident.clone(), expr: value.into() },
        });
        self.defs.global_ribs.builtin_const_rib.insert(sp!(ident.clone()), def_id).expect("redefinition of builtin");
        self.consts.defer_evaluation_of(def_id)
    }

    /// Declare a compile-time constant variable, resolving the ident to a brand new [`DefId`].
    pub fn define_const_var(&mut self, ident: Sp<ResIdent>, ty: ScalarType, expr: Sp<ast::Expr>) -> ConstId {
        let def_id = self.create_new_def_id(&ident);

        self.defs.vars.insert(def_id, VarData {
            ty: Some(VarType::Typed(ty)),
            kind: VarKind::Const { ident: ident.clone(), expr },
        });
        self.consts.defer_evaluation_of(def_id)
    }

    /// Set the low-level ABI of an instruction.
    ///
    /// A high-level [`Signature`] will also be generated from the ABI.
    pub fn set_ins_abi(&mut self, language: LanguageKey, opcode: raw::Opcode, abi: Sp<InstrAbi>, abi_loc: InstrAbiLoc) {
        // also update the high-level signature
        let sig = abi.create_signature(abi.span, self);
        sig.validate(self).expect("invalid signature from InstrAbi");

        self.defs.instrs.insert((language, opcode), InsData { abi: abi.value, abi_loc, sig });
    }

    /// Add an alias for an instruction from a mapfile.
    ///
    /// The alias will also become the new preferred alias for decompiling that instruction.
    pub fn define_global_ins_alias(&mut self, language: LanguageKey, opcode: raw::Opcode, ident: Sp<Ident>) -> DefId {
        let res_ident = self.resolutions.attach_fresh_res(ident.value.clone());
        let def_id = self.create_new_def_id(&res_ident);

        self.defs.funcs.insert(def_id, FuncData {
            sig: None,
            kind: FuncKind::InstructionAlias { language, opcode, ident: res_ident },
        });
        self.defs.ins_aliases.insert((language, opcode), def_id);

        if let Err(old) = self.defs.global_ribs.ins_alias_ribs[language].insert(ident.clone(), def_id) {
            let old_opcode = self.defs.func_opcode(old.def_id).unwrap().1;
            if opcode as u16 != old_opcode {
                self.emitter.emit(warning!(
                    "name '{}' used for multiple opcodes in {}: {}, {}",
                    ident, language.descr(), old_opcode, opcode,
                )).ignore();
            }
        };
        def_id
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
        self.resolutions.record_self_resolution(ident)
    }

    /// Get a fresh node ID for a newly constructed AST node.
    ///
    /// If you're unable to use this because a smaller portion of [`CompilerContext`] is
    /// already borrowed, you may alternatively borrow [`CompilerContext::unused_node_ids`].
    pub fn next_node_id(&self) -> NodeId {
        self.unused_node_ids.next()
    }

    /// Get a fresh loop ID for a newly constructed AST loop or switch in the AST.
    pub fn next_loop_id(&self) -> LoopId {
        self.unused_loop_ids.next()
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
    pub fn var_reg(&self, def_id: DefId) -> Option<(LanguageKey, RegId)> {
        match self.vars[&def_id] {
            VarData { kind: VarKind::RegisterAlias { reg, language, .. }, .. } => Some((language, reg)),
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
    pub fn func_opcode(&self, def_id: DefId) -> Option<(LanguageKey, raw::Opcode)> {
        match self.funcs[&def_id] {
            FuncData { kind: FuncKind::InstructionAlias { opcode, language, .. }, .. } => Some((language, opcode)),
            _ => None,
        }
    }

    /// Recovers the ABI of an opcode, if it is known.
    pub fn ins_abi(&self, language: LanguageKey, opcode: raw::Opcode) -> Option<(&InstrAbi, &InstrAbiLoc)> {
        self.instrs.get(&(language, opcode)).map(|x| (&x.abi, &x.abi_loc))
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
            VarData { kind: VarKind::BuiltinConst { ref ident, .. }, .. } => ident,
            VarData { kind: VarKind::EnumConst { ref ident, .. }, .. } => ident,
            VarData { kind: VarKind::EnumConstDummy { .. }, .. } => panic!("var_name called on enum dummy"),
        }
    }

    /// Get the fully resolved name of a function.
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a function.
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
            VarData { kind: VarKind::RegisterAlias { language, reg, .. }, .. } => {
                self.reg_inherent_ty(language, reg)
            },
            VarData { ty, .. } => ty.expect("not alias"),
        }
    }

    /// Get the inherent type of a register.
    pub fn reg_inherent_ty(&self, language: LanguageKey, reg: RegId) -> VarType {
        match self.regs.get(&(language, reg)) {
            Some(&RegData { ty }) => ty,
            // This is a register whose type is not in any mapfile.
            // This is actually fine, and is expected for stack registers.
            None => VarType::Untyped { explicit: false },
        }
    }

    /// Get the signature of any kind of named function. (instruction aliases, inline and const functions...)
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a function.
    pub fn func_signature(&self, def_id: DefId) -> Result<&Signature, InsMissingSigError> {
        match self.funcs[&def_id] {
            FuncData { kind: FuncKind::InstructionAlias { language, opcode, .. }, .. } => {
                self.ins_signature(language, opcode)
            },
            FuncData { ref sig, .. } => Ok(sig.as_ref().expect("not alias")),
        }
    }

    /// Get the high-level signature of an instruction.
    fn ins_signature(&self, language: LanguageKey, opcode: raw::Opcode) -> Result<&Signature, InsMissingSigError> {
        match self.instrs.get(&(language, opcode)) {
            Some(InsData { sig, .. }) => Ok(sig),
            None => Err(InsMissingSigError { language, opcode }),
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
            VarData { kind: VarKind::BuiltinConst { .. }, .. } => None,
            VarData { kind: VarKind::EnumConst { ident, .. }, .. } => Some(ident.span),
            VarData { kind: VarKind::EnumConstDummy { .. }, .. } => None,
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

    /// Look up the qualifier for a user-defined function.  `None` if not a user function.
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a function.
    pub fn user_func_qualifier(&self, def_id: DefId) -> Option<Option<Sp<ast::FuncQualifier>>> {
        match &self.funcs[&def_id] {
            FuncData { kind: FuncKind::InstructionAlias { .. }, .. } => None,
            FuncData { kind: FuncKind::User { qualifier, .. }, .. } => Some(qualifier.clone()),
        }
    }

    /// Get the expression assigned to a const var.
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a variable.
    pub fn var_const_expr(&self, def_id: DefId) -> Option<(ConstExprLoc, &ast::Expr)> {
        match &self.vars[&def_id] {
            VarData { kind: VarKind::Const { expr, .. }, .. } => Some((ConstExprLoc::Span(expr.span), &expr)),
            VarData { kind: VarKind::BuiltinConst { expr, .. }, .. } => Some((ConstExprLoc::Builtin, expr)),
            VarData { kind: VarKind::EnumConst { expr, .. }, .. } => Some((ConstExprLoc::Span(expr.span), &expr)),
            _ => None,
        }
    }
}

impl CompilerContext<'_> {
    pub fn init_special_defs(&mut self) {
        self.define_enum_const_dummy();
        self.add_builtin_consts();
    }

    fn add_builtin_consts(&mut self) {
        self.define_builtin_const_var(ident!("NAN"), f32::from_bits(CANONICAL_NAN_BITS).into());
        self.define_builtin_const_var(ident!("INF"), f32::INFINITY.into());
        self.define_builtin_const_var(ident!("PI"), core::f32::consts::PI.into());

        self.define_enum_const_fresh(ident!("true"), 1, ident!("bool"));
        self.define_enum_const_fresh(ident!("false"), 0, ident!("bool"));
    }

    fn define_enum_const_dummy(&mut self) {
        let ident = self.resolutions.attach_fresh_res(ident!("<ambiguous_enum>"));
        let def_id = self.resolutions.record_self_resolution(&ident);
        self.defs.vars.insert(def_id, VarData {
            ty: Some(ScalarType::Int.into()),
            kind: VarKind::EnumConstDummy,
        });

        self.defs.enum_const_dummy_def_id = Some(def_id);
    }

    /// Add info from a mapfile.
    ///
    /// Its path (if one is provided) is recorded in order to emit import directives into a decompiled script file.
    pub fn extend_from_mapfile(
        &mut self,
        path: Option<&std::path::Path>,
        mapfile: &Mapfile,
        // NOTE: this is only needed to check if it's < th08 or >= th08 for timeline arg0
        game: Game,
    ) -> Result<(), ErrorReported> {
        let emitter = self.emitter;

        if let Some(path) = path {
            self.mapfiles.push(path.to_owned());
        }

        for (names, signatures, language) in vec![
            (&mapfile.ins_names, &mapfile.ins_signatures, mapfile.language),
            (&mapfile.timeline_ins_names, &mapfile.timeline_ins_signatures, LanguageKey::Timeline),
        ] {
            for &(opcode, ref ident) in names {
                self.define_global_ins_alias(language, opcode as u16, ident.clone());
            }

            signatures.iter().map(|&(opcode, ref abi_str)| {
                // since there's no escape syntax in mapfile values, abi_str exactly matches the source text,
                // so we can construct a SourceStr
                let abi_source = SourceStr::from_span(abi_str.span, &abi_str);

                let abi = sp!(abi_str.span => InstrAbi::parse(abi_source, emitter)?);
                abi.validate_against_language(abi_str.span, game, language, emitter)?;

                let abi_loc = match mapfile.is_core_mapfile {
                    false => InstrAbiLoc::Span(abi_str.span),
                    true => InstrAbiLoc::CoreMapfile {
                        language, opcode: opcode as u16, abi_str: abi_str[..].into(),
                    },
                };
                self.set_ins_abi(language, opcode as u16, abi, abi_loc);
                Ok::<_, ErrorReported>(())
            }).collect_with_recovery::<()>()?;
        }

        for &(reg, ref ident) in &mapfile.gvar_names {
            self.define_global_reg_alias(mapfile.language, RegId(reg), ident.clone());
        }

        for &(reg, ref value) in &mapfile.gvar_types {
            let ty = match &value[..] {
                "%" => VarType::Typed(ScalarType::Float),
                "$" => VarType::Typed(ScalarType::Int),
                "?" => VarType::Untyped { explicit: true },
                _ => {
                    emitter.emit(warning!(
                        message("ignoring invalid variable type '{}' for gvar {}", value, reg),
                        primary(value, "invalid type"),
                    )).ignore();
                    continue;
                },
            };
            self.set_reg_ty(mapfile.language, RegId(reg), ty);
        }

        mapfile.ins_intrinsics.iter().map(|&(opcode, ref kind_str)| {
            // since there's no escape syntax in mapfile values, abi_str exactly matches the source text,
            // so we can construct a SourceStr
            let kind_source = SourceStr::from_span(kind_str.span, &kind_str);
            let kind = sp!(kind_str.span => IntrinsicInstrKind::parse(kind_source, emitter)?);
            self.defs.add_intrinsic_instr(mapfile.language, opcode as _, kind);
            Ok(())
        }).collect_with_recovery::<()>()?;

        mapfile.difficulty_flags.iter().map(|&(index, ref flag_str)| {
            let index = sp!(flag_str.span => index); // FIXME remind me why the indices don't have spans again?
            let flag_str = sp!(flag_str.span => &flag_str[..]);
            self.diff_flag_defs.define_flag_from_mapfile(index, flag_str)
                .map_err(|e| emitter.emit(e))
        }).collect_with_recovery::<()>()?;

        for (enum_name, enum_pairs) in &mapfile.enums {
            self.declare_enum(enum_name.clone());
            for &(value, ref const_name) in enum_pairs {
                let value = sp!(const_name.span => value.into()); // FIXME remind me why the indices don't have spans again?
                let res_ident = sp!(const_name.span => self.resolutions.attach_fresh_res(const_name.value.clone()));
                self.define_enum_const(res_ident, value, enum_name.clone());
            }
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
        let mut vec = vec![];
        vec.extend(self.global_ribs.ins_alias_ribs.values().cloned());
        vec.extend(self.global_ribs.reg_alias_ribs.values().cloned());
        vec.push(self.global_ribs.builtin_const_rib.clone());
        vec.push(self.global_ribs.enum_const_rib.clone());
        vec
    }

    pub fn enum_const_dummy_def_id(&self) -> DefId {
        self.enum_const_dummy_def_id.expect("Defs not initialized properly!")
    }
}

impl Defs {
    /// Add an intrinsic mapping from a mapfile.
    pub fn add_intrinsic_instr(
        &mut self,
        language: LanguageKey,
        opcode: raw::Opcode,
        intrinsic: Sp<IntrinsicInstrKind>,
    ) {
        self.intrinsic_instrs[language].push((opcode, intrinsic));
    }

    pub fn iter_intrinsic_instrs(&self, language: LanguageKey) -> impl Iterator<Item=(raw::Opcode, Sp<IntrinsicInstrKind>)> + '_ {
        self.intrinsic_instrs[language].iter().copied()
    }
}

// =============================================================================

/// Lookup table for decompiling constant values to enum consts.
#[derive(Debug, Clone)]
pub struct ConstNames {
    pub enums: IdMap<Ident, ScalarValueMap<Sp<Ident>>>,
}

/// A map with ScalarValue keys, which uses bitwise-identity for floats.
#[derive(Debug, Clone)]
pub struct ScalarValueMap<T> {
    ints: IdMap<i32, T>,
    strings: IdMap<String, T>,
    floats: IdMap<u32, T>,
}

impl<T> ScalarValueMap<T> {
    pub fn new() -> Self {
        ScalarValueMap {
            ints: Default::default(),
            strings: Default::default(),
            floats: Default::default(),
        }
    }

    pub fn insert(&mut self, key: ScalarValue, value: T) -> Option<T> {
        match key {
            ScalarValue::Int(x) => self.ints.insert(x, value),
            ScalarValue::Float(x) => self.floats.insert(x.to_bits(), value),
            ScalarValue::String(x) => self.strings.insert(x, value),
        }
    }

    pub fn get(&self, key: &ScalarValue) -> Option<&T> {
        match key {
            ScalarValue::Int(x) => self.ints.get(x),
            ScalarValue::Float(x) => self.floats.get(&x.to_bits()),
            ScalarValue::String(x) => self.strings.get(x),
        }
    }
}


impl CompilerContext<'_> {
    /// Get `value -> name` mappings for all enums and automatic consts, for decompilation or
    /// pretty-printing purposes.
    ///
    /// Requires [`crate::passes::evaluate_const_vars`] to have been run.
    pub fn get_const_names(&self, _const_proof: crate::passes::evaluate_const_vars::Proof) -> ConstNames {
        let CompilerContext { defs, consts, .. } = self;
        ConstNames {
            enums: defs.enums.iter().map(|(key, data)| (key.clone(), data.generate_lookup(consts))).collect(),
        }
    }
}

impl EnumData {
    fn generate_lookup(&self, consts: &context::Consts) -> ScalarValueMap<Sp<Ident>> {
        let mut out = ScalarValueMap::new();
        for (ident, &const_id) in &self.consts {
            let value = consts.get_cached_value(const_id).expect("evaluate_const_vars has not run! (bug!)");
            out.insert(value.clone(), ident.clone());
        }
        out
    }
}

// =============================================================================

/// Error indicating that raw syntax (`ins_`, `$REG`) was used in a place not associated with any
/// particular [`InstrLanguage`]. (e.g. a `const` definition)
pub struct UnexpectedRawSyntaxError;

impl CompilerContext<'_> {
    /// Get the effective type of a variable at a place where it is referenced.
    ///
    /// This can be different from the variable's innate type.  E.g. an integer global `I0` can be
    /// cast as a float using `%I0`.
    pub fn var_read_ty_from_ast(&self, var: &ast::Var) -> VarType {
        match var.ty_sigil {
            Some(sigil) => VarType::Typed(sigil.into()),
            None => self.var_inherent_ty_from_ast(var),
        }
    }

    /// Get the innate type of a variable at a place where it is referenced, ignoring its sigils.
    ///
    /// # Panics
    ///
    /// Panics if there is `REG` syntax and `language` is `None`; this should be caught in an earlier pass.
    pub fn var_inherent_ty_from_ast(&self, var: &ast::Var) -> VarType {
        match var.name {
            ast::VarName::Reg { reg, language } => self.defs.reg_inherent_ty(language.expect("must run assign_languages pass!"), reg),
            ast::VarName::Normal { ref ident, .. } => self.defs.var_inherent_ty(self.resolutions.expect_def(ident)),
        }
    }

    /// If the variable is a register or register alias, gets the associated register id.
    ///
    /// Otherwise, it must be something else (e.g. a local, a const...), whose unique
    /// name resolution id is returned.
    pub fn var_reg_from_ast(&self, var: &ast::VarName) -> Result<(LanguageKey, RegId), DefId> {
        match var {
            &ast::VarName::Reg { reg, language, .. } => {
                Ok((language.expect("must run assign_languages pass!"), reg)) // register
            },
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
    /// Otherwise, it must be something else (e.g. an exported or const function...), whose unique
    /// name resolution id is returned.
    pub fn func_opcode_from_ast(&self, name: &ast::CallableName) -> Result<(LanguageKey, u16), DefId> {
        match name {
            &ast::CallableName::Ins { opcode, language, .. } => {
                Ok((language.expect("must run assign_languages pass!"), opcode)) // instruction
            },
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
    ///
    /// # Panics
    ///
    /// Panics if there is `ins_` syntax and `language` is `None`; this should be caught in an earlier pass.
    pub fn func_signature_from_ast(&self, name: &ast::CallableName) -> Result<&Signature, InsMissingSigError> {
        match *name {
            ast::CallableName::Ins { opcode, language } => self.defs.ins_signature(language.expect("must run assign_languages pass!"), opcode),
            ast::CallableName::Normal { ref ident, .. } => self.defs.func_signature(self.resolutions.expect_def(ident)),
        }
    }

    /// Suppress the type sigil of a variable if it is unnecessary.
    pub fn var_simplify_ty_sigil(&self, var: &mut ast::Var) {
        let inherent_ty = self.var_inherent_ty_from_ast(var);
        Self::var_simplify_ty_sigil_(&mut var.ty_sigil, inherent_ty)
    }

    /// Look up the alias of a register.
    pub fn reg_alias(&self, language: LanguageKey, reg: RegId) -> Option<ResIdent> {
        self.defs.reg_aliases.get(&(language, reg))
            .map(|&def_id| self.defs.var_name(def_id).clone())
    }

    /// Generate an AST node with the ideal appearance for a register, automatically using
    /// an alias if one exists.
    pub fn reg_to_ast(&self, language: LanguageKey, reg: RegId) -> ast::VarName {
        Self::reg_to_ast_(language, reg, self.reg_alias(language, reg))
    }

    /// [`Self::reg_to_ast`] but where an alias has already been looked up. (perhaps one that is
    /// different from the one defined in mapfiles, e.g. a function parameter name...)
    ///
    /// FIXME: free-form function of `reg_to_ast`, feels awkwardly placed
    pub fn reg_to_ast_(language: LanguageKey, reg: RegId, alias: Option<ResIdent>) -> ast::VarName {
        match alias {
            None => ast::VarName::Reg { reg, language: Some(language) },
            Some(ident) => ast::VarName::Normal { ident, language_if_reg: Some(language) },
        }
    }

    /// Generate an AST node with the ideal appearance for an instruction call,
    /// automatically using an alias if one exists.
    pub fn ins_to_ast(&self, language: LanguageKey, opcode: raw::Opcode) -> ast::CallableName {
        match self.defs.ins_aliases.get(&(language, opcode)) {
            None => ast::CallableName::Ins { opcode, language: Some(language) },
            Some(&def_id) => {
                let ident = self.defs.func_name(def_id).clone();
                ast::CallableName::Normal { ident, language_if_ins: Some(language) }
            },
        }
    }

    /// Suppress the type sigil of a variable if it is unnecessary.
    ///
    /// FIXME: free-form function of `var_simplify_ty_sigil`, feels awkwardly placed
    pub fn var_simplify_ty_sigil_(ty_sigil: &mut Option<ast::VarSigil>, inherent_ty: VarType) {
        if let Some(sigil) = *ty_sigil {
            if inherent_ty == VarType::Typed(ScalarType::from(sigil)) {
                *ty_sigil = None;
            }
        }
    }

    /// Get the expression assigned to a const var.
    ///
    /// # Panics
    ///
    /// Panics if the ID does not correspond to a variable.
    pub fn var_aliasable_id(&self, name: &ast::VarName) -> AliasableId {
        match self.var_reg_from_ast(name) {
            Ok((_, reg)) => AliasableId::Reg(reg),
            Err(def_id) => AliasableId::Var(def_id),
        }
    }
}

impl Defs {
    /// Look up an enum const, if it exists.
    pub fn enum_const_def_id(&self, enum_name: &Ident, ident: &Ident) -> Option<DefId> {
        self.enums[enum_name].consts.get(ident).map(|&const_id| const_id.def_id)
    }

    /// Look up the unique enum that defines a const with a given name, or return `None`
    /// if there are multiple.
    ///
    /// # Panics
    /// Panics if the ident does not belong to any enums at all.
    pub fn enum_name_for_unqualified_enum_const(&self, ident: &Ident) -> Option<&Ident> {
        self.unique_enums.get(ident).map(|opt| opt.as_ref())
            .unwrap_or_else(|| panic!("not an enum const: {ident}"))
    }
}

// =============================================================================

impl CompilerContext<'_> {
    /// Implementation of [`crate::Truth::validate_defs`]. Call that instead.
    ///
    /// Responsible for additional validation after all mapfiles have been seen,
    /// which should occur during both compilation and decompilation (but which does not
    /// have any other obvious time to be performed).
    pub fn validate_defs(&self) -> Result<(), ErrorReported> {
        self.validate_mapfile_signatures()
    }

    fn all_signatures(&self) -> impl Iterator<Item=&'_ Signature> {
        let ins_sigs = self.defs.instrs.values().map(|data| &data.sig);
        let non_ins_sigs = self.defs.funcs.values().filter_map(|func| func.sig.as_ref());
        ins_sigs.chain(non_ins_sigs)
    }

    fn validate_mapfile_signatures(&self) -> Result<(), ErrorReported> {
        self.all_signatures().map(|siggy| {
            siggy.params.iter().map(|param| {
                if let Some(ty_color) = &param.ty_color {
                    self.validate_param_ty_color(ty_color)?;
                }
                Ok(())
            }).collect_with_recovery()
        }).collect_with_recovery()
    }

    fn validate_param_ty_color(&self, ty_color: &Sp<TypeColor>) -> Result<(), ErrorReported> {
        let TypeColor::Enum(used_name) = &ty_color.value;

        if self.defs.enums.get(used_name).is_none() {
            // Enum doesn't exist.
            let mut diag = error!(
                message("no such enum '{used_name}'"),
                primary(ty_color, "no such enum"),
            );
            if let Some(suggestion) = self.defs.find_similar_enum_name(used_name) {
                diag.secondary(ty_color, format!("did you mean `{suggestion}`?"));
            }
            return Err(self.emitter.emit(diag));
        }
        Ok(())
    }
}

impl Defs {
    fn find_similar_enum_name(&self, input: &Ident) -> Option<Ident> {
        let max_distance = input.as_str().len() / 3;

        self.enums.keys()
            .map(|candidate| (candidate, strsim::osa_distance(input.as_str(), candidate.as_str())))
            .min_by_key(|&(_, distance)| distance)
            .filter(|&(_, distance)| distance <= max_distance)
            .map(|(candidate, _)| candidate.clone())
    }
}

// =============================================================================

/// Indicates that a function name is an alias for an instruction, but this instruction
/// has no signature available.
///
/// (this error can't really be caught earlier, because we only want to flag instructions that
/// are actually used...)
#[derive(Debug, Clone)]
pub struct InsMissingSigError {
    pub language: LanguageKey,
    pub opcode: raw::Opcode,
}

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
    pub ty_color: Option<Sp<TypeColor>>,
    pub name: Option<Sp<ResIdent>>,
    pub default: Option<Sp<ast::Expr>>,
    pub qualifier: Option<Sp<ast::ParamQualifier>>,
    /// "Most useful" span for pointing to this parameter in a diagnostic.  Will point to the name if available,
    /// or something else if there is no name.
    pub useful_span: Span,
    /// This is `Some(_)` if for any reason, arguments in this position must be compile-time constants.
    ///
    /// (this is distinct from the question of "is the variable declared by this param a compile-time
    /// constant", which should be answered by instead checking [`Self::qualifier`].)
    ///
    /// Args will be checked for const-ness during one of the early compile passes.
    pub const_arg_reason: Option<ConstArgReason>,
}

/// A tag to "colorize" a parameter in a function.
///
/// This can cause it to prefer decompiling to consts of a specific enum, and/or help disambiguate
/// ambiguous enum const names.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeColor {
    Enum(Ident),
    // TODO: maybe bitflags, idk
}

impl TypeColor {
    pub fn descr(&self) -> impl fmt::Display + '_ {
        struct Impl<'a>(&'a TypeColor);

        impl fmt::Display for Impl<'_> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                match &self.0 {
                    TypeColor::Enum(name) => write!(f, "enum {name}"),
                }
            }
        }

        Impl(self)
    }

    pub fn enum_name(&self) -> Option<&Ident> {
        match self {
            TypeColor::Enum(name) => Some(name),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ConstArgReason {
    /// The encoding of this parameter does not permit registers.
    Encoding(crate::llir::ArgEncoding),

    // /// Exported functions in EoSD ECL can only take `const` values due to limitations of the `call` instruction.
    // EosdEcl,
}

impl Signature {
    pub fn from_func_params(ty_keyword: Sp<ast::TypeKeyword>, params: &[Sp<ast::FuncParam>]) -> Self {
        signature_from_func_ast(ty_keyword, params)
    }

    pub(crate) fn validate(&self, _ctx: &CompilerContext) -> Result<(), ErrorReported> {
        Ok(())
    }

    /// Minimum number of arguments accepted.
    pub fn min_args(&self) -> usize {
        self.params.iter().fold(0, |count, param| count + param.default.is_none() as usize)
    }

    /// Maximum number of arguments accepted.
    pub fn max_args(&self) -> usize {
        self.min_args()
    }

    /// Matches arguments at a call site to their corresponding parameters.
    /// (assuming that the argument count has already been checked)
    pub fn match_params_to_args<'a>(&'a self, args: &'a [Sp<ast::Expr>]) -> MatchedArgs<'_> {
        // TODO: variadics, keywords?
        let positional_pairs = Box::new(self.params.iter().zip(args));
        MatchedArgs { positional_pairs }
    }
}

pub struct MatchedArgs<'a> {
    // FIXME: Unbox once existential types are a thing.
    /// Individual (non-variadic), positional arguments.
    pub positional_pairs: Box<dyn Iterator<Item=(&'a SignatureParam, &'a Sp<ast::Expr>)> + 'a>,
}

fn signature_from_func_ast(return_ty_keyword: Sp<ast::TypeKeyword>, params: &[Sp<ast::FuncParam>]) -> Signature {
    Signature {
        params: params.iter().map(|sp_pat!(ast::FuncParam { ty_keyword, ident, qualifier })| SignatureParam {
            ty: ty_keyword.sp_map(ast::TypeKeyword::var_ty),
            ty_color: None,
            name: ident.clone(),
            qualifier: qualifier.clone(),
            default: None,
            useful_span: ident.as_ref().map(|ident| ident.span).unwrap_or_else(|| ty_keyword.span),
            // FIXME the match is to remind us to add a new ConstArgReason when inline funcs with 'const' params exist
            const_arg_reason: qualifier.as_ref().map(|q| match q.value { }),
        }).collect(),
        return_ty: return_ty_keyword.sp_map(ast::TypeKeyword::expr_ty),
    }
}
