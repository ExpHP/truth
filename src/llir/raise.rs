use std::collections::{BTreeSet};

use crate::raw;
use crate::ast;
use crate::ident::{Ident};
use crate::pos::{Sp};
use crate::diagnostic::{Emitter};
use crate::error::{ErrorReported};
use crate::llir::{RawInstr, LanguageHooks, IntrinsicInstrs, IntrinsicInstrKind};
use crate::resolve::{IdMap};
use crate::context::{self, CompilerContext};
use crate::game::LanguageKey;
use crate::passes::semantics::time_and_difficulty::{DEFAULT_DIFFICULTY_MASK_BYTE};
use crate::bitset::BitSet32;

use IntrinsicInstrKind as IKind;

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

/// FIXME yucko hack y dis public
pub use infer_pcb_signatures::CallRegSignatures;
mod infer_pcb_signatures;

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

/// A partially-raised form for an exported sub in a file.
///
/// This can be used to perform some global analyses, such as deducing PCB sub
/// parameters from callsites.
pub struct RaiseScript {
    instrs: Vec<RaiseInstr>,
}

/// Intermediate form of an instruction only used during decompilation.
///
/// In this format:
///
/// * Intrinsics are identified without needing to look up the opcode.
/// * An instruction in this format may represent a group of raw instructions.
///   (e.g. combining a compare and jump into a single conditional jump)
/// * Arguments have been raised to a variety of AST nodes, through [`RaisedIntrinsicParts`].
///   Notably, label offsets are decodes so that offset do not need to be known.
///
/// This is useful for low level transformations, particularly at the granularity of statements
/// (without blocks).
#[derive(Debug, Clone)]
struct RaiseInstr {
    labels: Vec<Label>,
    time: raw::Time,
    difficulty_mask: raw::DifficultyMask,
    kind: RaiseIntrinsicKind,
    parts: RaisedIntrinsicParts,
    /// If something prevents this [`RaiseInstr`] from being converted into AST statements,
    /// it needs a fallback to render instead.
    fallback_expansion: Option<Vec<RaiseInstr>>,
}

/// Result of raising an intrinsic's arguments.
///
/// The fields correspond to those on [`IntrinsicInstrAbiParts`].
#[derive(Debug, Clone, Default)]
struct RaisedIntrinsicParts {
    pub jump: Option<ast::StmtGoto>,
    pub sub_id: Option<Ident>,
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

    fn sub_raiser<'ctx>(&'a self, ctx: &'a CompilerContext<'ctx>) -> SingleSubRaiser<'a, 'ctx> {
        SingleSubRaiser {
            language: self.hooks.language(),
            ctx,
            call_reg_data: self.call_reg_info.as_ref(),
        }
    }

    pub fn raise_instrs_to_sub_ast(
        &mut self,
        emitter: &dyn Emitter,
        raw_script: &[RawInstr],
        ctx: &CompilerContext<'_>,
    ) -> Result<Vec<Sp<ast::Stmt>>, ErrorReported> {
        let middle = self.raise_instrs_to_middle(&emitter, raw_script, ctx)?;
        self.raise_middle_to_sub_ast(emitter, &middle, ctx)
    }

    pub fn raise_instrs_to_middle(
        &mut self,
        emitter: &dyn Emitter,
        raw_script: &[RawInstr],
        ctx: &CompilerContext<'_>,
    ) -> Result<RaiseScript, ErrorReported> {
        Ok(RaiseScript { instrs: _raise_instrs_to_middle(self, &emitter, raw_script, ctx)? })
    }

    pub fn raise_middle_to_sub_ast(
        &mut self,
        emitter: &dyn Emitter,
        middle: &RaiseScript,
        ctx: &CompilerContext<'_>,
    ) -> Result<Vec<Sp<ast::Stmt>>, ErrorReported> {
        let mut stmts = self.sub_raiser(ctx).raise_middle_to_ast(emitter.as_sized(), &middle.instrs)?;
        crate::passes::resolution::fill_missing_node_ids(&mut stmts[..], &ctx.unused_node_ids)?;
        Ok(stmts)
    }

    pub fn infer_pcb_signatures_and_certify_calls<'c>(&self, middles: impl IntoIterator<Item=&'c mut RaiseScript>, ctx: &CompilerContext<'_>) -> CallRegSignatures {
        CallRegSignatures::infer_from_calls(middles, ctx)
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

fn _raise_instrs_to_middle(
    raiser: &mut Raiser,
    emitter: &impl Emitter,
    raw_script: &[RawInstr],
    ctx: &CompilerContext,
) -> Result<Vec<RaiseInstr>, ErrorReported> {
    let mut middle_instrs = early::early_raise_instrs(raiser, emitter, raw_script, ctx)?;

    let sub_raiser = raiser.sub_raiser(ctx);
    middle_instrs = sub_raiser.perform_recognition(middle_instrs);

    Ok(middle_instrs)
}

// FIXME: This might not need to exist anymore, it was created to reduce the number of arguments
//        to all methods that potentially needed to raise expressions, which is now all done in
//        an earlier pass.
struct SingleSubRaiser<'a, 'ctx> {
    language: LanguageKey,
    ctx: &'a CompilerContext<'ctx>,
    call_reg_data: Option<&'a crate::ecl::CallRegInfo>,
}

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
                    string: sp!(self.ctx.diff_flag_defs.mask_to_diff_label(mask)),
                }))
            },
        }
    }
}

/// An error indicating that the data cannot be represented correctly as an intrinsic,
/// so a fallback to raw `ins_` should be tried.
struct CannotRaiseIntrinsic;
