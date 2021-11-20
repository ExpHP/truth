use core::ops::Range;
use std::collections::{BTreeSet};

use crate::raw;
use crate::ast;
use crate::ident::{Ident};
use crate::pos::{Sp};
use crate::diagnostic::{Emitter};
use crate::error::{ErrorReported};
use crate::llir::{RawInstr, LanguageHooks, IntrinsicInstrKind, IntrinsicInstrs};
use crate::resolve::{IdMap};
use crate::context::{self, CompilerContext};
use crate::game::LanguageKey;
use crate::passes::semantics::time_and_difficulty::{DEFAULT_DIFFICULTY_MASK_BYTE};

macro_rules! ensure {
    ($emitter:expr, $cond:expr, $($arg:tt)+) => {
        if !$cond { return Err($emitter.emit(error!($($arg)+))); }
    };
}
#[allow(unused)]
macro_rules! warn_unless {
    ($emitter:expr, $cond:expr, $($arg:tt)+) => {
        if !$cond { $emitter.emit(warning!($($arg)+)).ignore(); }
    };
}

use early::{Label};
mod early;
mod late;
mod recognize;

use IntrinsicInstrKind as IKind;
use crate::bitset::BitSet32;

#[derive(Debug, Clone)]
pub struct DecompileOptions {
    pub arguments: bool,
    pub intrinsics: bool,  // invariant: intrinsics implies arguments
    pub blocks: bool,
}

impl DecompileOptions {
    /// Construct with all features enabled.
    pub fn new() -> Self { Default::default() }
}

impl Default for DecompileOptions {
    fn default() -> Self {
        DecompileOptions { arguments: true, intrinsics: true, blocks: true }
    }
}

/// Intermediate form of an instruction only used during decompilation.
///
/// In this format:
///
/// * FIXME TODO TODO TODO TODO TODO
///
/// This is useful for an early pass at generating offset labels.
#[derive(Debug, Clone)]
struct RaiseInstr {
    fallback_expansion: Option<Vec<RaiseInstr>>,
    labels: Vec<Label>,
    /// Indices into the [`EarlyRaiseInstr`]s.
    instr_range: Range<usize>,
    time: raw::Time,
    difficulty_mask: raw::DifficultyMask,
    kind: RaiseIntrinsicKind,
    parts: RaisedIntrinsicParts,
}

/// Result of raising an intrinsic's arguments.
///
/// The fields correspond to those on [`IntrinsicInstrAbiParts`].
#[derive(Debug, Clone, Default)]
struct RaisedIntrinsicParts {
    pub jump: Option<ast::StmtGoto>,
    pub sub_id: Option<ast::CallableName>,
    pub outputs: Vec<ast::Var>,
    pub plain_args: Vec<ast::Expr>,
    // additional things used by e.g. the "instruction" intrinsic
    pub opcode: Option<raw::Opcode>,
    pub pseudo_arg0: Option<ast::Expr>,
    pub pseudo_mask: Option<raw::ParamMask>,
    pub pseudo_blob: Option<Vec<u8>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum RaiseIntrinsicKind {
    /// A raw instruction call.  Uses `opcode`, `plain_args`, and `pseudo_arg0`.
    Instruction,
    /// A raw instruction call of unknown signature.  Uses `opcode` and the `pseudo_*` fields.
    Blob,
    /// A single-instruction intrinsic.  (or the combination of multiple single-instruction
    /// intrinsics into one that behaves identical to another known intrinsic)
    Standard(IKind),
    /// A combined form of [`IntrinsicInstrKind::CallReg`] that includes `plain_arg`s for all
    /// of the argument registers assigned before the call, in their original order of assignment.
    ///
    /// (the actual registers of each argument must be inferred based on the argument's type)
    CallRegsGiven,
    /// A format-independent call intrinsic where `plain_args` contains the args in an
    /// order that matches the user-visible function signature.
    CallProper,
    /// End of script. Used to hold labels.
    End,
}

/// Type that provides methods to raise instructions to AST nodes.
///
/// It tracks some state related to diagnostics, so that some consolidated warnings
/// can be given at the end of decompilation.
pub struct Raiser<'a> {
    hooks: &'a dyn LanguageHooks,
    opcodes_without_abis: BTreeSet<u16>,
    // Root emitter because we don't want any additional context beyond the filename.
    emitter_for_abi_warnings: &'a context::RootEmitter,
    options: &'a DecompileOptions,
    intrinsic_instrs: IntrinsicInstrs,
    item_names: ItemNames,
    /// Caches information about PCB-style argument registers
    call_reg_info: Option<crate::ecl::CallRegInfo>,
}

#[derive(Default)]
struct ItemNames {
    anm_sprites: IdMap<i32, Ident>,
    anm_scripts: IdMap<i32, Ident>,
    ecl_subs: IdMap<i32, Ident>,
}

impl Drop for Raiser<'_> {
    fn drop(&mut self) {
        self.generate_warnings();
    }
}

impl<'a> Raiser<'a> {
    pub fn new(
        hooks: &'a dyn LanguageHooks,
        emitter: &'a context::RootEmitter,
        defs: &context::Defs,
        options: &'a DecompileOptions,
    ) -> Result<Self, ErrorReported> {
        Ok(Raiser {
            hooks,
            opcodes_without_abis: Default::default(),
            emitter_for_abi_warnings: emitter,
            // If intrinsic decompilation is disabled, simply pretend that there aren't any intrinsics.
            intrinsic_instrs: match options.intrinsics {
                true => IntrinsicInstrs::from_format_and_mapfiles(hooks, defs, emitter)?,
                false => Default::default(),
            },
            options,
            item_names: Default::default(),
            call_reg_info: None,
        })
    }

    /// Supply names for raising ANM sprite arguments.
    pub fn add_anm_sprite_names(&mut self, names: impl IntoIterator<Item=(raw::LangInt, Ident)>) {
        self.item_names.anm_sprites.extend(names)
    }

    /// Supply names for raising ANM script arguments.
    pub fn add_anm_script_names(&mut self, names: impl IntoIterator<Item=(raw::LangInt, Ident)>) {
        self.item_names.anm_scripts.extend(names)
    }

    /// Supply names for raising ECL sub calls.
    pub fn add_ecl_sub_names(&mut self, names: impl IntoIterator<Item=(raw::LangInt, Ident)>) {
        self.item_names.ecl_subs.extend(names)
    }

    /// Supply data for raising subs in this particular format.
    pub fn set_olde_sub_format(&mut self, sub_format: &dyn crate::ecl::OldeSubFormat) {
        self.call_reg_info = sub_format.call_reg_info();
    }

    pub fn raise_instrs_to_sub_ast(
        &mut self,
        emitter: &dyn Emitter,
        raw_script: &[RawInstr],
        ctx: &CompilerContext<'_>,
    ) -> Result<Vec<Sp<ast::Stmt>>, ErrorReported> {
        let mut stmts = _raise_instrs_to_sub_ast(self, &emitter, raw_script, ctx)?;
        crate::passes::resolution::fill_missing_node_ids(&mut stmts[..], &ctx.unused_node_ids)?;
        Ok(stmts)
    }

    pub fn generate_warnings(&mut self) {
        if !self.opcodes_without_abis.is_empty() {
            self.emitter_for_abi_warnings.emit(warning!(
                message("{} instructions with unknown signatures were decompiled to byte blobs.", self.hooks.language().descr()),
                note(
                    "The following opcodes were affected: {}",
                    self.opcodes_without_abis.iter()
                        .map(|opcode| opcode.to_string()).collect::<Vec<_>>().join(", ")
                ),
            )).ignore();
        }

        self.opcodes_without_abis.clear();
    }
}

fn _raise_instrs_to_sub_ast(
    raiser: &mut Raiser,
    emitter: &impl Emitter,
    raw_script: &[RawInstr],
    ctx: &CompilerContext,
) -> Result<Vec<Sp<ast::Stmt>>, ErrorReported> {
    let mut middle_instrs = early::early_raise_instrs(raiser, emitter, raw_script, ctx)?;

    let mut sub_raiser = SingleSubRaiser {
        hooks: raiser.hooks,
        intrinsic_instrs: &raiser.intrinsic_instrs,
        language: raiser.hooks.language(),
        ctx,
        item_names: &raiser.item_names,
        call_reg_data: raiser.call_reg_info.as_ref(),
    };

    middle_instrs = sub_raiser.perform_recognition(middle_instrs);

    sub_raiser.raise_instrs(emitter, &middle_instrs)
}

/// Type containing all sorts of info about the current sub so that functions involved in
/// raising instrs to statements don't need to take 50 arguments.
struct SingleSubRaiser<'a, 'ctx> {
    // context
    intrinsic_instrs: &'a IntrinsicInstrs,
    hooks: &'a dyn LanguageHooks,
    language: LanguageKey,
    ctx: &'a CompilerContext<'ctx>,
    item_names: &'a ItemNames,
    call_reg_data: Option<&'a crate::ecl::CallRegInfo>,
    // NOTE: No Emitter because the chain methods are used to add contextual info.
}

/// Methods where all of the fallback logic concerning diff switches and intrinsics is implemented.
impl SingleSubRaiser<'_, '_> {
    fn make_stmt(&self, difficulty_mask: raw::DifficultyMask, kind: ast::StmtKind) -> Sp<ast::Stmt> {
        sp!(ast::Stmt {
            node_id: None,
            diff_label: self.make_diff_label(difficulty_mask),
            kind,
        })
    }

    fn make_diff_label(&self, mask_byte: raw::DifficultyMask) -> Option<Sp<ast::DiffLabel>> {
        match mask_byte {
            // save some work by suppressing redundant labels now.
            // (this pass generates a flat list so the "outer"/natural difficulty is always 0xFF)
            DEFAULT_DIFFICULTY_MASK_BYTE => None,
            mask_byte => {
                let mask = BitSet32::from_mask(mask_byte as _);
                Some(sp!(ast::DiffLabel {
                    mask: Some(mask),
                    string: sp!(self.ctx.diff_flag_names.mask_to_diff_label(mask)),
                }))
            },
        }
    }
}

/// An error indicating that the data cannot be represented correctly as an intrinsic,
/// so a fallback to raw `ins_` should be tried.
struct CannotRaiseIntrinsic;

// =============================================================================
