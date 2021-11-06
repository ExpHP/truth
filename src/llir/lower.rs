use std::collections::{HashMap};

use crate::raw;
use super::{unsupported, SimpleArg};
use crate::llir::{RawInstr, LanguageHooks, IntrinsicInstrs, ArgEncoding, TimelineArgKind, ScalarType};
use crate::diagnostic::Emitter;
use crate::error::{GatherErrorIteratorExt, ErrorReported};
use crate::pos::{Sp};
use crate::ast;
use crate::resolve::DefId;
use crate::ident::{Ident};
use crate::context::{self, CompilerContext};
use crate::io::{Encoded, DEFAULT_ENCODING};
use crate::value::ScalarValue;
use crate::passes::semantics::time_and_difficulty::TimeAndDifficulty;

mod stackless;
mod intrinsic;

/// An intermediate representation that is only used during lowering.
///
/// In addition to instructions, it has a couple of extra things that are handled via
/// some post-processing steps.
#[derive(Debug, Clone, PartialEq)]
enum LowerStmt {
    /// Represents a single instruction in the compiled file.
    Instr(LowerInstr),
    /// An intrinsic that represents a label that can be jumped to.
    Label { time: raw::Time, label: Sp<Ident> },
    /// An intrinsic that begins the scope of a register-allocated local.
    RegAlloc { def_id: DefId },
    /// An intrinsic that ends the scope of a register-allocated local.
    RegFree { def_id: DefId },
}

/// An instruction that needs just a bit more postprocessing to convert it into a [`RawInstr`].
#[derive(Debug, Clone, PartialEq)]
struct LowerInstr {
    stmt_data: TimeAndDifficulty, // or should this be NodeId?
    opcode: raw::Opcode,
    /// Value provided by user via an explicit `@arg0=`.
    explicit_extra_arg: Option<raw::ExtraArg>,
    /// Value provided by user via `@mask=`, which will override the automatically-computed param mask.
    user_param_mask: Option<raw::ParamMask>,
    /// Mask of enabled difficulties.
    // difficulty_mask: u8,
    args: LowerArgs,
}

#[derive(Debug, Clone, PartialEq)]
enum LowerArgs {
    /// The user provided normal arguments, which at this point we have largely reduced down to immediate
    /// values and registers.
    Known(Vec<Sp<LowerArg>>),
    /// The user provided `@blob=`.  In this case, it is okay for the instruction's ABI to not be known.
    Unknown(Sp<Vec<u8>>),
}

#[derive(Debug, Clone, PartialEq)]
enum LowerArg {
    /// A fully encoded argument (an immediate or a register).
    ///
    /// All arguments are eventually lowered to this form.
    Raw(SimpleArg),
    /// A reference to a register-allocated local.
    Local {
        def_id: DefId,
        /// The type that the register ID should be written into the file as.
        /// May differ from the type of the variable.
        storage_ty: ScalarType
    },
    /// A label that has not yet been converted to an integer argument.
    Label(Ident),
    /// A `timeof(label)` that has not yet been converted to an integer argument.
    TimeOf(Ident),
}

impl LowerArg {
    /// Call this at a time when the arg is known to have a fully resolved value.
    ///
    /// Such times are:
    /// * Within [`InstrFormat::write_instr`].
    #[track_caller]
    pub fn expect_raw(&self) -> &SimpleArg {
        match self {
            LowerArg::Raw(x) => x,
            _ => panic!("unexpected unresolved argument (bug!): {:?}", self),
        }
    }

    /// Tweak this LowerArg to encode its register ID as an int even if it was conceptually read/written as a float.
    /// (for early ECL)
    pub fn with_float_reg_encoded_as_int(self) -> Self {
        match self {
            LowerArg::Raw(arg) => LowerArg::Raw(SimpleArg::from_reg(arg.get_reg_id().unwrap(), ScalarType::Int)),

            LowerArg::Local { def_id, .. } => LowerArg::Local { def_id, storage_ty: ScalarType::Int },

            LowerArg::Label { .. } |
            LowerArg::TimeOf { .. } => panic!("not a register: {:?}", self),
        }
    }
}

/// Type that provides methods to lower function bodies to instructions.
///
/// It tracks some state related to diagnostics, so that some consolidated errors/warnings
/// can be given at the end of compilation.
///
/// Each language should have a separate instance.
/// This is a panic-bomb, so `.finish()` must be called.
pub struct Lowerer<'a> {
    hooks: &'a dyn LanguageHooks,
    export_info: Option<&'a crate::ecl::EosdExportedSubs>,
    // NOTE: later this can become Box<dyn Trait> and just let the implementations downcast
    inner: stackless::PersistentState,
}

impl Drop for Lowerer<'_> {
    #[track_caller]
    fn drop(&mut self) {
        if !std::thread::panicking() {
            panic!("Lowerer::finish() was not called, this is a bug!");
        }
    }
}

impl<'a> Lowerer<'a> {
    pub fn new(hooks: &'a dyn LanguageHooks) -> Self {
        Lowerer { hooks, inner: Default::default(), export_info: None }
    }

    /// Add information about exported subroutines, in languages that support calls.
    pub fn with_export_info(mut self, export_info: &'a crate::ecl::EosdExportedSubs) -> Self {
        self.export_info = Some(export_info);
        self
    }

    /// Compile a single sub.
    ///
    /// `def_id` should be provided if and only if [`Self::with_export_info`] has been called;
    /// it is used to look up information about the current sub's parameter list.
    pub fn lower_sub(&mut self, code: &[Sp<ast::Stmt>], def_id: Option<DefId>, ctx: &mut CompilerContext<'_>) -> Result<Vec<RawInstr>, ErrorReported> {
        lower_sub_ast_to_instrs(self, code, def_id, ctx)
    }

    /// Report any errors that can only be reported once all functions have been compiled.
    pub fn finish(mut self, ctx: &CompilerContext<'_>) -> Result<(), ErrorReported> {
        let inner = std::mem::replace(&mut self.inner, Default::default());
        std::mem::forget(self);  // disable the panic bomb
        inner.finish(ctx)
    }
}

fn lower_sub_ast_to_instrs(
    lowerer: &mut Lowerer,
    code: &[Sp<ast::Stmt>],
    def_id: Option<DefId>,
    ctx: &mut CompilerContext<'_>,
) -> Result<Vec<RawInstr>, ErrorReported> {
    use stackless::{SingleSubLowerer, assign_registers};

    let hooks = lowerer.hooks;
    let mut sub_lowerer = SingleSubLowerer {
        out: vec![],
        intrinsic_instrs: IntrinsicInstrs::from_format_and_mapfiles(hooks, &ctx.defs, ctx.emitter)?,
        stmt_data: crate::passes::semantics::time_and_difficulty::run(code, &ctx.emitter)?,
        export_info: lowerer.export_info,
        ctx,
        hooks,
    };
    sub_lowerer.lower_sub_ast(code)?;
    let mut out = sub_lowerer.out;

    // And now postprocess
    assign_registers(&mut out, &mut lowerer.inner, hooks, lowerer.export_info, def_id, &ctx)?;

    let label_info = gather_label_info(hooks, 0, &out, &ctx.defs, &ctx.emitter)?;
    encode_labels(&mut out, hooks, &label_info, &ctx.emitter)?;

    let mut encoding_state = ArgEncodingState::new();
    Ok(out.into_iter().filter_map(|x| match x.value {
        LowerStmt::Instr(instr) => Some({
            // this is the second time we're using encode_args (first time was to get labels), so suppress warnings
            let null_emitter = ctx.emitter.with_writer(crate::diagnostic::dev_null());
            encode_args(&mut encoding_state, hooks, &instr, &ctx.defs, &null_emitter)
                .expect("we encoded this successfully before!")
        }),
        LowerStmt::Label { .. } => None,
        LowerStmt::RegAlloc { .. } => None,
        LowerStmt::RegFree { .. } => None,
    }).collect())
}

// =============================================================================

struct LabelInfoverse {
    stmt_offsets: Vec<raw::BytePos>,
    labels: HashMap<Sp<Ident>, RawLabelInfo>,
}
struct RawLabelInfo {
    time: raw::Time,
    offset: raw::BytePos,
}

/// A quick pass near the end of a subroutine's compilation that collects the offsets of all labels.
fn gather_label_info(
    hooks: &dyn LanguageHooks,
    initial_offset: raw::BytePos,
    code: &[Sp<LowerStmt>],
    defs: &context::Defs,
    emitter: &context::RootEmitter,
) -> Result<LabelInfoverse, ErrorReported> {
    use std::collections::hash_map::Entry;

    // Due to things like the TH12 MSG furigana bug, the size of an instruction can depend
    // on other instructions written before it.  Thus, there's no easy way to get the size
    // of an instruction without repeating all of the logic involved in encoding it.
    //
    // Basically, here we will perform a full encoding pass of all instructions, substituting
    // unknown labels and etc. with dummy values, just so we can determine the number of bytes
    // that each instruction will occupy.  These encoded instructions will then be thrown out,
    // and we'll do a second, TRUE encoding pass later once we have substituted everything
    // with their proper values.
    //
    // We could maybe get rid of the second encoding pass by tracking offsets to fix up, like
    // a linker?  But we'd have to do it per-instruction and it'd be awkward.  (it'd have to
    // be per-instruction because AnmFile/StdFile/etc. structs need to contain something that
    // is a vec of data per-instruction, else they're not suitable for READING binary files).
    //
    // I doubt that the extra encoding is a big issue in the grand scheme of things.  - Exp

    let instr_format = hooks.instr_format();

    let mut offset = initial_offset;
    let mut labels = HashMap::new();
    let mut stmt_offsets = vec![];

    let mut encoding_state = ArgEncodingState::new();

    code.iter().enumerate().map(|(index, thing)| {
        stmt_offsets.push(offset);
        match thing.value {
            LowerStmt::Instr(ref instr) => {
                emitter.chain_with(|f| write!(f, "in instruction {}", index), |emitter| {
                    // encode the instruction with dummy values
                    let same_size_instr = substitute_dummy_args(instr);
                    let raw_instr = encode_args(&mut encoding_state, hooks, &same_size_instr, defs, emitter)?;
                    offset += instr_format.instr_size(&raw_instr) as u64;
                    Ok(())
                })?;
            },
            LowerStmt::Label { time, ref label } => {
                match labels.entry(label.clone()) {
                    Entry::Vacant(e) => {
                        e.insert(RawLabelInfo { time, offset });
                    },
                    Entry::Occupied(e) => {
                        return Err(emitter.emit(error!{
                            message("duplicate label '{}'", label),
                            secondary(e.key(), "originally defined here"),
                            primary(label, "redefined here"),
                        }));
                    },
                }
            },
            _ => {},
        }
        Ok(())
    }).collect_with_recovery()?;

    Ok(LabelInfoverse { labels, stmt_offsets })
}

/// Eliminates all `LowerArg::Label`s by replacing them with their dword values.
fn encode_labels(
    code: &mut [Sp<LowerStmt>],
    hooks: &dyn LanguageHooks,
    label_info: &LabelInfoverse,
    emitter: &context::RootEmitter,
) -> Result<(), ErrorReported> {
    let LabelInfoverse { labels, stmt_offsets } = label_info;

    assert_eq!(code.len(), stmt_offsets.len());
    code.iter_mut().enumerate().map(|(stmt_index, stmt)| {
        let cur_offset = stmt_offsets[stmt_index];
        if let LowerStmt::Instr(LowerInstr { args: LowerArgs::Known(args), .. } ) = &mut stmt.value {
            for arg in args {
                match arg.value {
                    | LowerArg::Label(ref label)
                    | LowerArg::TimeOf(ref label)
                    => match labels.get(label) {
                        Some(info) => match arg.value {
                            LowerArg::Label(_) => arg.value = LowerArg::Raw((hooks.encode_label(cur_offset, info.offset) as i32).into()),
                            LowerArg::TimeOf(_) => arg.value = LowerArg::Raw(info.time.into()),
                            _ => unreachable!(),
                        },
                        None => return Err(emitter.emit(error!{
                            message("undefined label '{}'", label),
                            primary(arg, "there is no label by this name"),
                        })),
                    },

                    _ => {},
                } // match arg.value
            } // for arg in args
        } // if let LowerStmt::Instr { .. }
        Ok(())
    }).collect_with_recovery()
}

/// Replaces special args like Labels and TimeOf with dummy values.
///
/// This preserves the number of bytes in the written instruction.
fn substitute_dummy_args(instr: &LowerInstr) -> LowerInstr {
    let &LowerInstr { ref args, .. } = instr;
    let new_args = match args {
        LowerArgs::Unknown(blob) => LowerArgs::Unknown(blob.clone()),
        LowerArgs::Known(args) => LowerArgs::Known(args.iter().map(|arg| match arg.value {
            | LowerArg::Label(_)
            | LowerArg::TimeOf(_)
            => sp!(arg.span => LowerArg::Raw(SimpleArg { value: ScalarValue::Int(0), is_reg: false })),

            | LowerArg::Local { .. }
            => sp!(arg.span => LowerArg::Raw(SimpleArg { value: ScalarValue::Int(0), is_reg: true })),

            | LowerArg::Raw(_) => arg.clone(),
        }).collect())
    };
    LowerInstr { args: new_args, ..*instr }
}

// =============================================================================

/// Mutable state that must persist from one instruction to the next when encoding instruction args into bytes.
struct ArgEncodingState {
    /// Records additional bytes that should be appended to the next string before it is padded
    /// and masked, in order to simulate the TH12 MSG furigana bug.
    furibug_bytes: Option<Encoded>,
}

impl ArgEncodingState {
    pub fn new() -> Self { ArgEncodingState {
        furibug_bytes: None,
    }}
}

/// Implements the encoding of argument values into byte blobs according to an instruction's ABI.
fn encode_args(
    state: &mut ArgEncodingState,
    hooks: &dyn LanguageHooks,
    instr: &LowerInstr,
    defs: &context::Defs,
    emitter: &impl Emitter,
) -> Result<RawInstr, ErrorReported> {
    use crate::io::BinWrite;

    let args = match &instr.args {
        LowerArgs::Known(args) => args,
        LowerArgs::Unknown(blob) => {
            // Trivial case; a @blob was provided so there's nothing for this function to do.
            return Ok(RawInstr {
                time: instr.stmt_data.time,
                opcode: instr.opcode,
                param_mask: instr.user_param_mask.unwrap_or(0),
                args_blob: blob.value.clone(),
                extra_arg: instr.explicit_extra_arg,
                difficulty: instr.stmt_data.difficulty_mask,
                // TODO: ECL pseudo-args whose semantics are not yet implemented
                pop: 0,
            });
        },
    };

    // From this point onwards, we are working with a standard list of arguments and
    // now need to convert these into a blob of bytes.
    if !hooks.has_registers() {
        if let Some(arg_that_is_reg) = args.iter().find(|arg| arg.expect_raw().is_reg) {
            return Err(emitter.emit(error!(
                message("non-constant expression in language without registers"),
                primary(arg_that_is_reg, "non-const expression"),
            )));
        }
    }

    let (abi, _) = {
        defs.ins_abi(hooks.language(), instr.opcode)
            .expect("(bug!) we already checked sigs for known args")
    };

    let mut arg_encodings_iter = abi.arg_encodings().peekable();
    let mut args_iter = args.iter().peekable();

    // handle timeline first argument; this may come from @arg0 or the first standard argument
    let mut extra_arg = instr.explicit_extra_arg;
    match arg_encodings_iter.peek() {
        Some(&ArgEncoding::TimelineArg(TimelineArgKind::Unused)) => {
            arg_encodings_iter.next(); // consume it
            extra_arg.get_or_insert(0);
        }
        Some(&ArgEncoding::TimelineArg(_)) => {
            arg_encodings_iter.next(); // consume it
            let first_normal_arg = args_iter.next().expect("type checker already checked arity");

            if extra_arg.is_none() {
                assert!(!first_normal_arg.expect_raw().is_reg, "checked above");
                extra_arg = Some(first_normal_arg.expect_raw().expect_int() as _);
            } else {
                // Explicit @arg0, but also drawn from args.
                // To keep the type checker's job simpler, we took an argument from the argument list anyways,
                // but it was "overridden" by the explicit @arg0.
                emitter.emit(warning!(
                    message("explicit @arg0 overrides value supplied naturally"),
                    primary(first_normal_arg, "this value will be ignored"),
                )).ignore();
            }
        }
        _ => {},
    }

    // The remaining args go into the argument byte blob.
    let mut args_blob = std::io::Cursor::new(vec![]);

    // Important: we put the shortest iterator (args_iter) first in the zip list
    //            to ensure that this loop reads an equal number of items from all iters.
    assert!(args_iter.len() <= arg_encodings_iter.len());
    for (arg, enc) in zip!(args_iter, arg_encodings_iter.by_ref()) {
        match enc {
            | ArgEncoding::TimelineArg { .. }
            => unreachable!(),

            | ArgEncoding::Dword
            | ArgEncoding::Color
            | ArgEncoding::JumpOffset
            | ArgEncoding::JumpTime
            | ArgEncoding::Padding
            | ArgEncoding::Script
            | ArgEncoding::Sub
            | ArgEncoding::Sprite
            => args_blob.write_i32(arg.expect_raw().expect_int()).expect("Cursor<Vec> failed?!"),

            | ArgEncoding::Float
            => args_blob.write_f32(arg.expect_raw().expect_float()).expect("Cursor<Vec> failed?!"),

            | ArgEncoding::Word
            => args_blob.write_i16(arg.expect_raw().expect_int() as _).expect("Cursor<Vec> failed?!"),

            | ArgEncoding::String { block_size, mask, furibug }
            => {
                let string = arg.expect_raw().expect_string();

                // convert to Shift-JIS or whatever
                let mut encoded = Encoded::encode(&sp!(arg.span => string), DEFAULT_ENCODING).map_err(|e| emitter.emit(e))?;
                encoded.0.push(b'\0'); // have to do this eagerly to correctly reproduce TH17 Extra files

                // the furigana bug appends a copy of the masked bytes from a previous furigana string
                if furibug {
                    if let Some(furibug_bytes) = state.furibug_bytes.take() {
                        encoded.0.extend(furibug_bytes.0);
                    }
                }

                if encoded.len() % block_size != 0 {
                    encoded.null_pad(block_size);
                }
                encoded.apply_xor_mask(mask);

                if furibug && string.starts_with("|") {
                    state.furibug_bytes = Some(encoded.clone());
                }

                args_blob.write_all(&encoded.0).expect("Cursor<Vec> failed?!");
            },
        }
    }

    for enc in arg_encodings_iter {
        assert_eq!(enc, ArgEncoding::Padding);
        args_blob.write_u32(0).expect("Cursor<Vec> failed?!");
    }

    Ok(RawInstr {
        time: instr.stmt_data.time,
        opcode: instr.opcode,
        param_mask: match instr.user_param_mask {
            Some(user_provided_mask) => user_provided_mask,
            None => compute_param_mask(&args, emitter)?,
        },
        args_blob: args_blob.into_inner(),
        extra_arg,
        difficulty: instr.stmt_data.difficulty_mask,
        // TODO: ECL pseudo-args whose semantics are not yet implemented
        pop: 0,
    })
}

fn compute_param_mask(args: &[Sp<LowerArg>], emitter: &impl Emitter) -> Result<raw::ParamMask, ErrorReported> {
    if args.len() > raw::ParamMask::BITS as _ {
        return Err(emitter.emit(error!(
            message("too many arguments in instruction!"),
            primary(args[raw::ParamMask::BITS as usize], "too many arguments"),
        )));
    }
    let mut mask = 0;
    for arg in args.iter().rev(){
        let bit = match &arg.value {
            LowerArg::Raw(raw) => raw.is_reg as raw::ParamMask,
            LowerArg::TimeOf { .. } |
            LowerArg::Label { .. } => 0,
            LowerArg::Local { .. } => 1,
        };
        mask *= 2;
        mask += bit;
    }
    Ok(mask)
}

// =============================================================================
