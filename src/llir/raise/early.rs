//! Early decompilation passes.
//!
//! These passes are generally responsible for decompiling instruction arguments.

use std::collections::{BTreeMap, BTreeSet};

use super::{Raiser, RaiseInstr, RaiseIntrinsicKind};
use crate::raw;
use crate::ast::{self};
use crate::pos::Sp;
use crate::ident::{Ident, ResIdent};
use crate::diagnostic::{Emitter};
use crate::error::{ErrorReported, GatherErrorIteratorExt};
use crate::llir::{RawInstr, LanguageHooks, SimpleArg};
use crate::llir::intrinsic::{IntrinsicInstrAbiParts, abi_parts};
use crate::resolve::{RegId, IdMap};
use crate::context::{self, Defs, CompilerContext};
use crate::context::defs::{ConstNames, TypeColor, auto_enum_names};
use crate::game::LanguageKey;
use crate::llir::{ArgEncoding, StringArgSize, InstrAbi, RegisterEncodingStyle};
use crate::value::{ScalarValue};
use crate::io::{DEFAULT_ENCODING, Encoded};
use crate::llir::raise::{CannotRaiseIntrinsic, RaisedIntrinsicParts, RaisedIntrinsicPseudos};
use crate::passes::semantics::time_and_difficulty::DEFAULT_DIFFICULTY_MASK_BYTE;

/// Intermediate form of an instruction only used during decompilation.
///
/// In this format:
///
/// * Using each instruction's ABI, the argument blob and register mask have been decoded
///   into core language primitive types.
///
/// This is useful for an early pass at generating offset labels.
#[derive(Debug)]
struct EarlyRaiseInstr {
    offset: raw::BytePos,
    time: raw::Time,
    opcode: raw::Opcode,
    args: EarlyRaiseArgs,
    difficulty_mask: raw::DifficultyMask,
    /// Timeline arg0, only if it should be raised to `@arg0`. (if it should be raised as a standard
    /// argument, it will be in `args`)
    pseudo_arg0: Option<raw::ExtraArg>,
    pseudo_pop: raw::StackPop,
    pseudo_arg_count: raw::ArgCount,
}

#[derive(Debug)]
enum EarlyRaiseArgs {
    /// The ABI of the instruction was known, so we parsed the argument bytes into arguments.
    Decoded(Vec<SimpleArg>),
    /// The ABI was not known, so we will be emitting pseudo-args like `@blob=`.
    Unknown(UnknownArgsData),
}

pub(in crate::llir::raise) fn early_raise_instrs(
    raiser: &mut super::Raiser,
    emitter: &impl Emitter,
    raw_script: &[RawInstr],
    ctx: &CompilerContext,
) -> Result<Vec<RaiseInstr>, ErrorReported> {
    let hooks = raiser.hooks;
    let ref instr_offsets = gather_instr_offsets(raw_script, hooks);

    // Parse blobs into args
    let instrs: Vec<EarlyRaiseInstr> = {
        raw_script.iter().zip(instr_offsets)
            .enumerate()
            .map(|(index, (raw_instr, &offset))| {
                let ref emitter = add_instr_context(emitter, index, raw_instr.opcode, offset);
                raiser.decode_args(emitter, raw_instr, offset, &ctx.defs)
            })
            .collect::<Result<_, _>>()?
    };

    let ref jump_data = gather_jump_time_args(&instrs, &ctx.defs, hooks)?;
    let offset_labels = generate_offset_labels(emitter, &instrs, instr_offsets, jump_data)?;

    let &end_offset = instr_offsets.last().expect("n + 1 offsets so there's always at least one");

    early_raise_intrinsics(raiser, emitter, &offset_labels, instrs, end_offset, ctx)
}

#[derive(Debug, Clone)]
struct  UnknownArgsData {
    blob: Vec<u8>,
    param_mask: raw::ParamMask,
}

fn early_raise_intrinsics(
    raiser: &mut super::Raiser,
    emitter: &impl Emitter,
    offset_labels: &OffsetLabels,
    instrs: Vec<EarlyRaiseInstr>,
    end_offset: raw::BytePos,
    ctx: &CompilerContext,
) -> Result<Vec<RaiseInstr>, ErrorReported> {
    let atom_raiser = AtomRaiser {
        language: raiser.hooks.language(),
        const_names: &raiser.const_names,
        hooks: raiser.hooks,
        offset_labels,
        ctx,
    };

    let mut out = instrs.iter().enumerate().map(|(instr_index, instr)| {
        let ref emitter = add_instr_context(emitter, instr_index, instr.opcode, instr.offset);
        let make_instr = |kind, parts| RaiseInstr {
            fallback_expansion: None,
            labels: Vec::from_iter(offset_labels.get(&instr.offset).cloned()),
            time: instr.time,
            difficulty_mask: instr.difficulty_mask,
            kind, parts,
        };

        // blob?
        let raw_args = match &instr.args {
            &EarlyRaiseArgs::Decoded(ref args) => args,
            &EarlyRaiseArgs::Unknown(UnknownArgsData { param_mask, ref blob }) => return Ok(make_instr(
                RaiseIntrinsicKind::Blob,
                RaisedIntrinsicParts {
                    opcode: Some(instr.opcode),
                    pseudo_blob: Some(blob.clone()),
                    pseudos: Some(RaisedIntrinsicPseudos {
                        arg0: instr.pseudo_arg0.map(|x| (x as i32).into()),
                        param_mask: (param_mask != 0).then(|| raise_mask(param_mask)),
                        // FIXME: would rather have these display based on whether the language supports them.
                        pop: (instr.pseudo_pop != 0).then(|| raise_pop(instr.pseudo_pop)),
                        arg_count: (instr.pseudo_arg_count != 0).then(|| raise_nargs(instr.pseudo_arg_count)),
                    }),
                    ..Default::default()
                })),
        };

        // basic instruction call syntax
        // (create now so it can be a fallback for intrinsics)
        let ins_instr = make_instr(
            RaiseIntrinsicKind::Instruction,
            atom_raiser.raise_raw_ins_args(emitter, instr, raw_args)?,
        );

        // intrinsic?
        let abi = atom_raiser.expect_abi(instr.opcode);
        if let Some((intrinsic, abi_info)) = raiser.intrinsic_instrs.get_intrinsic_and_props(instr.opcode) {
            match atom_raiser.raise_intrinsic_parts(instr, raw_args, abi, abi_info) {
                Ok(parts) => {
                    let mut intrinsic_instr = make_instr(RaiseIntrinsicKind::Standard(intrinsic), parts);

                    // FIXME: this is for things like EoSD split jumps and PCB calls that are not single-instruction
                    //        intrinsics and have no syntax they can be raised into.  They require an ins_ fallback
                    //        in case we are unable to merge them together into their larger, full intrinsics.
                    intrinsic_instr.fallback_expansion = Some(vec![ins_instr]);
                    return Ok(intrinsic_instr);
                },
                Err(CannotRaiseIntrinsic) => {},  // fall through
            }
        };

        // not intrinsic
        Ok(ins_instr)
    }).collect_with_recovery::<Vec<_>>()?;

    let end_time = {
        offset_labels.get(&end_offset)
            .map(|label| label.time_label)
            .or_else(|| instrs.last().map(|instr| instr.time))
            .unwrap_or(0)  // beginning of script time
    };

    out.push(RaiseInstr {
        fallback_expansion: None,
        labels: Vec::from_iter(offset_labels.get(&end_offset).cloned()),
        time: end_time,
        difficulty_mask: DEFAULT_DIFFICULTY_MASK_BYTE,
        kind: RaiseIntrinsicKind::End,
        parts: Default::default(),
    });
    Ok(out)
}

fn raise_mask(value: raw::ParamMask) -> ast::Expr {
    ast::Expr::LitInt {
        value: value.into(),
        radix: ast::IntRadix::Bin,
    }
}

fn raise_nargs(value: raw::ArgCount) -> ast::Expr {
    i32::from(value).into()
}

fn raise_pop(value: raw::StackPop) -> ast::Expr {
    ast::Expr::LitInt {
        value: value.into(),
        radix: ast::IntRadix::Hex,
    }
}

// =============================================================================
// Blob-decoding pass.  (RawInstr -> EarlyInstr)

impl Raiser<'_> {
    fn decode_args(&mut self, emitter: &impl Emitter, instr: &RawInstr, instr_offset: raw::BytePos, defs: &Defs) -> Result<EarlyRaiseInstr, ErrorReported> {
        if self.options.arguments {
            if let Some((abi, _)) = defs.ins_abi(self.hooks.language(), instr.opcode) {
                return decode_args_with_abi(emitter, self.hooks, instr, instr_offset, abi);
            } else {
                self.opcodes_without_abis.insert(instr.opcode);
            }
        }

        // Fall back to decompiling as a blob.
        Ok(EarlyRaiseInstr {
            offset: instr_offset,
            time: instr.time,
            opcode: instr.opcode,
            difficulty_mask: instr.difficulty,
            pseudo_arg0: instr.extra_arg,
            pseudo_arg_count: instr.arg_count,
            pseudo_pop: instr.pop,
            args: EarlyRaiseArgs::Unknown(UnknownArgsData {
                param_mask: instr.param_mask,
                blob: instr.args_blob.to_vec(),
            }),
        })
    }
}

fn decode_args_with_abi(
    emitter: &impl Emitter,
    hooks: &dyn LanguageHooks,
    instr: &RawInstr,
    instr_offset: raw::BytePos,
    siggy: &InstrAbi,
) -> Result<EarlyRaiseInstr, ErrorReported> {
    use crate::io::BinRead;

    let mut param_mask = instr.param_mask;
    let mut args_blob = std::io::Cursor::new(&instr.args_blob);
    let mut args = vec![];
    let mut pseudo_arg0 = instr.extra_arg;
    let mut remaining_len = instr.args_blob.len();

    fn decrease_len(emitter: &impl Emitter, remaining_len: &mut usize, amount: usize) -> Result<(), ErrorReported> {
        if *remaining_len < amount {
            return Err(emitter.emit(error!("not enough bytes in instruction")));
        }
        *remaining_len -= amount;
        Ok(())
    }

    let reg_style = hooks.register_style();
    for (arg_index, enc) in siggy.arg_encodings().enumerate() {
        let ref emitter = add_argument_context(emitter, arg_index);

        let param_mask_bit = param_mask % 2 == 1;
        param_mask /= 2;

        let value = match *enc {
            | ArgEncoding::Integer { arg0: true, .. }
            => {
                // a check that non-timeline languages don't have timeline args in their signature
                // is done earlier so we can unwrap this
                let extra_arg = pseudo_arg0.take().expect("timeline arg in sig for non-timeline language");
                ScalarValue::Int(extra_arg as _)
            },

            | ArgEncoding::Integer { arg0: false, size: 4, ty_color: _ }
            | ArgEncoding::Color
            | ArgEncoding::JumpOffset
            | ArgEncoding::JumpTime
            | ArgEncoding::Padding
            => {
                decrease_len(emitter, &mut remaining_len, 4)?;
                ScalarValue::Int(args_blob.read_u32().expect("already checked len") as i32)
            },

            | ArgEncoding::Integer { arg0: false, size: 2, ty_color: _ }
            => {
                decrease_len(emitter, &mut remaining_len, 2)?;
                ScalarValue::Int(args_blob.read_i16().expect("already checked len") as i32)
            },

            | ArgEncoding::Integer { size, .. }
            => panic!("unexpected integer size: {size}"),

            | ArgEncoding::Float
            => {
                decrease_len(emitter, &mut remaining_len, 4)?;
                ScalarValue::Float(f32::from_bits(args_blob.read_u32().expect("already checked len")))
            },

            | ArgEncoding::String { size: size_spec, mask, furibug }
            => {
                let read_len = match size_spec {
                    StringArgSize::Block { .. } => remaining_len,  // read to end
                    StringArgSize::Fixed { len, nulless: _ } => len,
                };
                decrease_len(emitter, &mut remaining_len, read_len)?;

                let mut encoded = Encoded(args_blob.read_byte_vec(read_len).expect("already checked len"));
                encoded.apply_xor_mask(mask);

                if let StringArgSize::Fixed { nulless: true, .. } = size_spec {
                    // suppress the warning about missing nulls by adding one now if missing
                    if !encoded.0.contains(&b'\0') {
                        encoded.0.push(b'\0');
                    }
                };

                let warn_on_trimmed_data = !furibug;  // furibug DOES leave garbage after the null
                encoded.trim_first_nul(emitter, warn_on_trimmed_data);

                let string = encoded.decode(DEFAULT_ENCODING).map_err(|e| emitter.emit(e))?;
                ScalarValue::String(string)
            },
        };

        let is_reg = match reg_style {
            RegisterEncodingStyle::ByParamMask => param_mask_bit,
            RegisterEncodingStyle::EosdEcl { does_value_look_like_a_register } => {
                does_value_look_like_a_register(&value)
            },
        };

        args.push(SimpleArg { value, is_reg });
    }

    if args_blob.position() != args_blob.get_ref().len() as u64 {
        emitter.emit(warning!(
            // this could mean the signature is incomplete
            "unexpected leftover bytes in ins_{}! (read {} bytes out of {}!)",
            instr.opcode, args_blob.position(), args_blob.get_ref().len(),
        )).ignore();
    }

    // check that we did enough right-shifts to use every bit
    if param_mask != 0 && matches!(reg_style, RegisterEncodingStyle::ByParamMask) {
        emitter.emit(warning!(
            "unused mask bits in ins_{}! (arg {} is a register, but there are only {} args!)",
            instr.opcode, param_mask.trailing_zeros() + args.len() as u32 + 1, args.len(),
        )).ignore();
    }
    Ok(EarlyRaiseInstr {
        offset: instr_offset,
        time: instr.time,
        opcode: instr.opcode,
        difficulty_mask: instr.difficulty,
        pseudo_arg0,
        pseudo_pop: instr.pop,
        pseudo_arg_count: instr.arg_count,
        args: EarlyRaiseArgs::Decoded(args),
    })
}


// =============================================================================
// Various early passes related to offset labels.

#[derive(Debug, Clone, PartialEq)]
pub struct Label {
    pub time_label: raw::Time,
    pub label: Ident
}

struct JumpData {
    /// For each offset that has at least one jump to it, all of the time arguments for those jumps.
    all_offset_args: BTreeMap<raw::BytePos, BTreeSet<Option<raw::Time>>>,
}

fn gather_instr_offsets(
    script: &[RawInstr],
    hooks: &dyn LanguageHooks,
) -> Vec<u64> {
    let mut out = vec![0];
    let mut offset = 0;

    let instr_format = hooks.instr_format();
    for instr in script {
        offset += instr_format.instr_size(instr) as u64;
        out.push(offset);
    }
    out
}

fn gather_jump_time_args(
    script: &[EarlyRaiseInstr],
    defs: &context::Defs,
    hooks: &dyn LanguageHooks,
) -> Result<JumpData, ErrorReported> {
    let mut all_offset_args = BTreeMap::<u64, BTreeSet<Option<i32>>>::new();

    for instr in script {
        if let Some((jump_offset, jump_time)) = extract_jump_args_by_signature(hooks, instr, defs) {
            all_offset_args.entry(jump_offset).or_default().insert(jump_time);
        }
    }

    Ok(JumpData { all_offset_args })
}

/// Maps offsets to their labels.
type OffsetLabels = BTreeMap<raw::BytePos, Label>;

fn generate_offset_labels(
    emitter: &impl Emitter,
    script: &[EarlyRaiseInstr],
    instr_offsets: &[raw::BytePos],
    jump_data: &JumpData,
) -> Result<OffsetLabels, ErrorReported> {
    let mut offset_labels = BTreeMap::new();
    for (&offset, time_args) in &jump_data.all_offset_args {
        let dest_index = {
            instr_offsets.binary_search(&offset)
                .map_err(|_| emitter.emit(error!("an instruction has a bad jump offset!")))?
        };
        // Find out the time range between this instruction and the previous one
        // (the or_else triggers when dest_index == script.len() (label after last instruction))
        let dest_time = script.get(dest_index).unwrap_or_else(|| script.last().unwrap()).time;
        let next = (instr_offsets[dest_index], dest_time);
        let prev = match dest_index {
            0 => (0, 0), // scripts implicitly start at time 0.  (test 'time_loop_at_beginning_of_script')
            i => (instr_offsets[i - 1], script[i - 1].time),
        };
        offset_labels.insert(offset, generate_label_at_offset(prev, next, time_args));
    }
    Ok(offset_labels)
}

/// Given all of the different time args used when jumping to `next_offset`,
/// determine what to call the label at this offset (and what time label to give it).
fn generate_label_at_offset(
    (prev_offset, prev_time): (raw::BytePos, raw::Time),
    (next_offset, next_time): (raw::BytePos, raw::Time),
    time_args: &BTreeSet<Option<raw::Time>>,
) -> Label {
    let time_args = time_args.iter().map(|&x| x.unwrap_or(next_time)).collect::<BTreeSet<_>>();

    // If the only time used with this label is the time of the previous instruction
    // (which is less than this instruction), put the label before the relative time increase.
    if prev_time < next_time && time_args.len() == 1 && time_args.iter().next().unwrap() == &prev_time {
        return Label { label: ident!("label_{prev_offset}r"), time_label: prev_time };
    }
    Label { label: ident!("label_{next_offset}"), time_label: next_time }
}

#[test]
fn test_generate_label_at_offset() {
    let check = generate_label_at_offset;
    let set = |times: &[Option<i32>]| times.iter().copied().collect();
    let label = |str: &str, time_label: i32| Label { label: Ident::new_user(str).unwrap(), time_label };

    assert_eq!(check((0, 0), (0, 10), &set(&[Some(10)])), (label("label_0", 10)));
    assert_eq!(check((100, 10), (116, 20), &set(&[Some(20)])), (label("label_116", 20)));
    assert_eq!(check((100, 10), (116, 20), &set(&[None])), (label("label_116", 20)));
    // make sure label doesn't get 'r' label if two instructions have equal times
    assert_eq!(check((100, 10), (116, 10), &set(&[Some(10)])), (label("label_116", 10)));
    // time label decrease means no 'r' label
    assert_eq!(check((100, 20), (116, 10), &set(&[Some(20)])), (label("label_116", 10)));
    // multiple different time args means no 'r' label
    assert_eq!(check((100, 10), (116, 20), &set(&[Some(10), Some(20)])), (label("label_116", 20)));
    assert_eq!(check((100, 10), (116, 20), &set(&[Some(10), Some(16)])), (label("label_116", 20)));

    // the case where an r label is created
    assert_eq!(check((100, 10), (116, 20), &set(&[Some(10)])), (label("label_100r", 10)));
}

fn extract_jump_args_by_signature(
    hooks: &dyn LanguageHooks,
    instr: &EarlyRaiseInstr,
    defs: &context::Defs,
) -> Option<(raw::BytePos, Option<raw::Time>)> {
    let mut jump_offset = None;
    let mut jump_time = None;

    let args = match &instr.args {
        EarlyRaiseArgs::Decoded(args) => args,
        EarlyRaiseArgs::Unknown(_) => return None,
    };

    let (abi, _) = defs.ins_abi(hooks.language(), instr.opcode).expect("decoded, so abi is known");
    for (arg, encoding) in zip!(args, abi.arg_encodings()) {
        match encoding {
            ArgEncoding::JumpOffset
            => jump_offset = Some(hooks.decode_label(instr.offset, arg.expect_immediate_int() as u32)),
            ArgEncoding::JumpTime
            => jump_time = Some(arg.expect_immediate_int()),
            _ => {},
        }
    }

    jump_offset.map(|offset| (offset, jump_time))
}

// =============================================================================
// Argument-raising pass.  (EarlyInstr -> RaiseInstr)

struct AtomRaiser<'a, 'ctx> {
    language: LanguageKey,
    const_names: &'a ConstNames,
    offset_labels: &'a OffsetLabels,
    hooks: &'a dyn LanguageHooks,
    ctx: &'a CompilerContext<'ctx>,
}

/// Indicates that a jump offset did not point to an instruction.
#[derive(Debug, Clone, Copy)]
struct IllegalOffset;

impl AtomRaiser<'_, '_> {
    /// Raise an instr to raw `ins_` syntax.
    fn raise_raw_ins_args(
        &self,
        emitter: &impl Emitter,
        instr: &EarlyRaiseInstr,
        args: &[SimpleArg],  // args decoded from the blob
    ) -> Result<RaisedIntrinsicParts, ErrorReported> {
        let abi = self.expect_abi(instr.opcode);
        let encodings = abi.arg_encodings().collect::<Vec<_>>();

        if args.len() != encodings.len() {
            return Err(emitter.emit(error!(
                "provided arg count ({}) does not match mapfile ({})", args.len(), encodings.len(),
            )));
        }

        // in case this is a jump that didn't decompile to an intrinsic, scan ahead for an offset arg
        // so we can use this info when decompiling the time arg.
        let dest_label = {
            encodings.iter().zip(args)
                .find(|(&enc, _)| enc == &ArgEncoding::JumpOffset)
                .map(|(_, offset_arg)| {
                    let dest_offset = self.hooks.decode_label(instr.offset, offset_arg.expect_int() as u32);
                    self.offset_labels.get(&dest_offset)
                        .ok_or(IllegalOffset)  // if it was a valid offset, it would have a label
                })
        };

        let mut raised_args = encodings.iter().zip(args).enumerate().map(|(i, (&enc, arg))| {
            let ref emitter = add_argument_context(emitter, i);
            Ok(self.raise_arg(emitter, &arg, enc, dest_label)?)
        }).collect::<Result<Vec<_>, ErrorReported>>()?;

        // Show an explicit @arg0 if necessary
        let pseudo_arg0 = match instr.pseudo_arg0 {
            None | Some(0) => None,
            Some(arg0) => {
                let enc = ArgEncoding::Integer { size: 2, ty_color: None, arg0: true };
                let expr = self.raise_arg(emitter, &SimpleArg::from(arg0 as i32), &enc, dest_label)?;
                Some(expr)
            }
        };

        // drop early STD padding args from the end as long as they're zero.
        //
        // IMPORTANT: this is looking at the original arg list because the new lengths may differ due to arg0.
        for (enc, arg) in abi.arg_encodings().zip(args).rev() {
            match enc {
                ArgEncoding::Padding if arg.is_immediate_zero() => raised_args.pop(),
                _ => break,
            };
        }

        Ok(RaisedIntrinsicParts {
            opcode: Some(instr.opcode),
            plain_args: raised_args,
            pseudos: Some(RaisedIntrinsicPseudos {
                arg0: pseudo_arg0,
                // FIXME: these should display based on whether they match the values that would be computed for the instruction
                param_mask: None,
                pop: (instr.pseudo_pop != 0).then(|| raise_pop(instr.pseudo_pop)),
                arg_count: (instr.pseudo_arg_count != 0).then(|| raise_nargs(instr.pseudo_arg_count)),
            }),
            ..Default::default()
        })
    }

    fn raise_intrinsic_parts(
        &self,
        instr: &EarlyRaiseInstr,
        args: &[SimpleArg],
        abi: &InstrAbi,
        abi_parts: &IntrinsicInstrAbiParts,
    ) -> Result<RaisedIntrinsicParts, CannotRaiseIntrinsic> {
        // Any failure in this function must go to the fallback logic for decompiling to raw syntax,
        // so we'll suppress warnings and errors this time around
        let emitter = &crate::diagnostic::DummyEmitter;

        let encodings = abi.arg_encodings().collect::<Vec<_>>();
        let IntrinsicInstrAbiParts {
            num_instr_args: _, padding: ref padding_info, outputs: ref outputs_info,
            jump: ref jump_info, plain_args: ref plain_args_info, sub_id: ref sub_id_info,
        } = abi_parts;

        let padding_range = padding_info.index..padding_info.index + padding_info.count;
        if !args[padding_range].iter().all(|arg| arg.is_immediate_zero()) {
            return Err(CannotRaiseIntrinsic);  // data in padding
        }

        let mut jump = None;
        if let &Some((index, order)) = jump_info {
            let (offset_arg, time_arg) = match order {
                abi_parts::JumpArgOrder::TimeLoc => (&args[index + 1], Some(&args[index])),
                abi_parts::JumpArgOrder::LocTime => (&args[index], Some(&args[index + 1])),
                abi_parts::JumpArgOrder::Loc => (&args[index], None),
            };

            let label_offset = self.hooks.decode_label(instr.offset, offset_arg.expect_immediate_int() as u32);
            let label = &self.offset_labels[&label_offset];
            jump = Some(ast::StmtGoto {
                destination: sp!(label.label.clone()),
                time: match time_arg {
                    Some(arg) => Some(sp!(arg.expect_immediate_int())).filter(|&t| t != label.time_label),
                    None => None,
                },
            });
        }

        let mut sub_id = None;
        if let &Some(index) = sub_id_info {
            let sub_index = args[index].expect_immediate_int() as _;
            // FIXME: This is a bit questionable. We're looking up an enum name (conceptually in the
            //        value namespace) to get an ident for a callable function (conceptually in the
            //        function namespace).  It feels like there is potential for future bugs here...
            let lookup_table = &self.const_names.enums[&auto_enum_names::ecl_sub()];
            let name = lookup_table.get(&sub_index).ok_or(CannotRaiseIntrinsic)?;
            sub_id = Some(name.value.clone());
        }

        let mut outputs = vec![];
        for &(index, mode) in outputs_info {
            let var = self.raise_arg_to_reg(emitter, &args[index], &encodings[index], mode)
                .map_err(|ErrorReported| CannotRaiseIntrinsic)?;

            outputs.push(var);
        }

        let mut plain_args = vec![];
        for &index in plain_args_info {
            let dest_label = None;  // offset and time are not plain args so this is irrelevant
            let expr = self.raise_arg(emitter, &args[index], &encodings[index], dest_label)
                .map_err(|ErrorReported| CannotRaiseIntrinsic)?;

            plain_args.push(expr);
        }
        Ok(RaisedIntrinsicParts {
            jump, sub_id, outputs, plain_args,
            ..Default::default()
        })
    }

    /// General argument-raising routine that supports registers and uses the encoding in the ABI
    /// to possibly guide how to express the output. This is what is used for e.g. args in `ins_` syntax.
    fn raise_arg(
        &self,
        emitter: &impl Emitter,
        raw: &SimpleArg,
        enc: &ArgEncoding,
        dest_label: Option<Result<&Label, IllegalOffset>>,
    ) -> Result<ast::Expr, ErrorReported> {
        if raw.is_reg {
            Ok(ast::Expr::Var(sp!(self.raise_arg_to_reg(emitter, raw, enc, abi_parts::OutputArgMode::Natural)?)))
        } else {
            self.raise_arg_to_literal(emitter, raw, enc, dest_label)
        }
    }

    /// Raise an immediate arg, using the encoding to guide the formatting of the output.
    fn raise_arg_to_literal(
        &self,
        emitter: &impl Emitter,
        raw: &SimpleArg,
        enc: &ArgEncoding,
        dest_label: Option<Result<&Label, IllegalOffset>>,
    ) -> Result<ast::Expr, ErrorReported> {
        ensure!(emitter, !raw.is_reg, "expected an immediate, got a register");

        match enc {
            | ArgEncoding::Padding
            | ArgEncoding::Integer { ty_color: None, .. }
            => Ok(ast::Expr::from(raw.expect_int())),

            | ArgEncoding::Integer { ty_color: Some(ty_color), .. }
            => {
                let lookup_table = match ty_color {
                    TypeColor::Enum(ident) => &self.const_names.enums[ident],
                };
                Ok(raise_to_possibly_named_constant(
                    &lookup_table,
                    raw.expect_int(),
                    ty_color,
                ))
            }

            | ArgEncoding::Color
            => Ok(ast::Expr::LitInt { value: raw.expect_int(), radix: ast::IntRadix::Hex }),

            | ArgEncoding::Float
            => Ok(ast::Expr::from(raw.expect_float())),

            | ArgEncoding::String { .. }
            => Ok(ast::Expr::from(raw.expect_string().clone())),

            | ArgEncoding::JumpTime
            => match dest_label {
                | Some(Ok(Label { time_label, label })) if *time_label == raw.expect_int()
                => Ok(ast::Expr::LabelProperty { label: sp!(label.clone()), keyword: sp!(token![timeof]) }),

                _ => Ok(ast::Expr::from(raw.expect_int())),
            },

            | ArgEncoding::JumpOffset
            => match dest_label.unwrap() {
                | Ok(Label { label, .. })
                => Ok(ast::Expr::LabelProperty { label: sp!(label.clone()), keyword: sp!(token![offsetof]) }),

                | Err(IllegalOffset) => {
                    emitter.emit(warning!("invalid offset in a jump instruction")).ignore();
                    Ok(ast::Expr::LitInt { value: raw.expect_int(), radix: ast::IntRadix::SignedHex })
                },
            },
        }
    }

    fn raise_arg_to_reg(
        &self,
        emitter: &impl Emitter,
        raw: &SimpleArg,
        encoding: &ArgEncoding,
        // ty: ScalarType,
        // FIXME: feels out of place.  But basically, the only place where the type of the raised
        //        variable can have a different type from its storage is in some intrinsics, yet the logic
        //        for dealing with these is otherwise the same as regs in non-intrinsics.
        storage_mode: abi_parts::OutputArgMode,
    ) -> Result<ast::Var, ErrorReported> {
        ensure!(emitter, raw.is_reg, "expected a variable, got an immediate");

        let storage_ty_sigil = encoding.expr_type().sigil().ok_or_else(|| {
            emitter.emit(error!("unexpected register bit on {} value", encoding.expr_type().descr()))
        })?;
        let ast_ty_sigil = match storage_mode {
            abi_parts::OutputArgMode::FloatAsInt => ast::VarSigil::Float,
            abi_parts::OutputArgMode::Natural => storage_ty_sigil,
        };
        let reg = match storage_ty_sigil {
            ast::VarSigil::Int => RegId(raw.expect_int()),
            ast::VarSigil::Float => {
                let float_reg = raw.expect_float();
                if float_reg != f32::round(float_reg) {
                    return Err(emitter.emit(error!("non-integer float variable %REG[{}] in binary file!", float_reg)));
                }
                RegId(float_reg as i32)
            },
        };
        let name = ast::VarName::Reg { reg, language: Some(self.language) };
        Ok(ast::Var { ty_sigil: Some(ast_ty_sigil), name })
    }

    fn expect_abi(&self, opcode: raw::Opcode) -> &InstrAbi {
        // if we have RaiseInstr then we already used the signature earlier to decode the arg bytes
        self.ctx.defs.ins_abi(self.hooks.language(), opcode).unwrap_or_else(|| {
            unreachable!("(BUG!) signature not known for opcode {}, but this should have been caught earlier!", opcode)
        }).0
    }
}

fn raise_to_possibly_named_constant(names: &IdMap<i32, Sp<Ident>>, id: i32, ty_color: &TypeColor) -> ast::Expr {
    match names.get(&id) {
        Some(ident) => {
            match ty_color {
                TypeColor::Enum(_) => {
                    let const_ident = ResIdent::new_null(ident.value.clone());
                    let name = ast::VarName::new_non_reg(const_ident);
                    let var = ast::Var { ty_sigil: None, name };
                    ast::Expr::Var(sp!(var))
                },
            }
        },
        None => id.into(),
    }
}

// =============================================================================

fn add_instr_context(emitter: &impl Emitter, instr_index: usize, opcode: raw::Opcode, offset: raw::BytePos) -> impl Emitter + '_ {
    emitter.get_chained_with(move |f| write!(
        f, "instr {} (opcode {}, offset {:#X})",
        instr_index, opcode, offset,
    ))
}

fn add_argument_context(emitter: &impl Emitter, arg_index: usize) -> impl Emitter + '_{
    emitter.get_chained_with(move |f| write!(f, "argument {}", arg_index + 1))
}
