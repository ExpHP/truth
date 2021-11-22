use super::{RaiseInstr, RaiseIntrinsicKind, RaisedIntrinsicParts, SingleSubRaiser};

use crate::ast;
use crate::llir::{IntrinsicInstrKind};
use crate::context::{CompilerContext};
use crate::value::{ReadType};
use crate::passes::semantics::time_and_difficulty::{DEFAULT_DIFFICULTY_MASK_BYTE};
use crate::diff_switch_utils as ds_util;
use crate::bitset::BitSet32;

use RaiseIntrinsicKind as RIKind;
use IntrinsicInstrKind as IKind;

impl SingleSubRaiser<'_, '_> {
    pub fn perform_recognition(
        &self,
        instrs: Vec<RaiseInstr>,
    ) -> Vec<RaiseInstr> {
        let mut out = vec![];
        let mut remaining = &instrs[..];
        while !remaining.is_empty() {
            if let Some((new_instr, num_replaced)) = recognize_double_instr_intrinsic(remaining) {
                out.push(new_instr);
                remaining = &remaining[num_replaced..];
                continue;
            }

            if let Some((new_instr, num_replaced)) = recognize_diff_switch(remaining, &self.ctx.diff_flag_names) {
                out.push(new_instr);
                remaining = &remaining[num_replaced..];
                continue;
            }

            if let Some(call_reg_data) = self.call_reg_data {
                if let Some((new_instr, num_replaced)) = recognize_reg_call(remaining, call_reg_data, self.ctx) {
                    out.push(new_instr);
                    remaining = &remaining[num_replaced..];
                    continue;
                }
            }

            out.push(remaining[0].clone());
            remaining = &remaining[1..];
        }
        out
    }
}

/// Try to raise an intrinsic that is two instructions long.
fn recognize_double_instr_intrinsic(
    instrs: &[RaiseInstr],
) -> Option<(RaiseInstr, usize)> {
    if instrs.len() < 2 {
        return None;
    }

    let (instr_1, instr_2) = (&instrs[0], &instrs[1]);
    if (instr_1.time, instr_1.difficulty_mask) != (instr_2.time, instr_2.difficulty_mask) {
        return None;
    }
    if !instr_2.labels.is_empty() {
        return None;
    }

    let (combined_kind, combined_parts);
    match (&instr_1.kind, &instr_2.kind) {
        (
            &RIKind::Standard(IKind::CondJmp2A(ty)),
            &RIKind::Standard(IKind::CondJmp2B(op)),
        ) => {
            let (cmp_instr, jmp_instr) = (instr_1, instr_2);
            combined_kind = RIKind::Standard(IKind::CondJmp(op, ty));
            combined_parts = RaisedIntrinsicParts {
                plain_args: cmp_instr.parts.plain_args.clone(),
                jump: jmp_instr.parts.jump.clone(),
                ..Default::default()
            };
        },
        _ => return None,
    };

    let combined_instr = RaiseInstr {
        fallback_expansion: Some(vec![instr_1.clone(), instr_2.clone()]),
        labels: instr_1.labels.clone(),
        time: instr_1.time,
        difficulty_mask: instr_1.difficulty_mask,
        kind: combined_kind,
        parts: combined_parts,
    };
    Some((combined_instr, 2))
}

/// Recognize a PCB ECL sub call.
///
/// Return value includes number of instructions read.
fn recognize_reg_call(
    instrs: &[RaiseInstr],
    call_reg_data: &crate::ecl::CallRegInfo,
    ctx: &CompilerContext<'_>,
) -> Option<(RaiseInstr, usize)> {
    let arg_regs_by_ty = &call_reg_data.arg_regs_by_type;

    // we will expect args of any given type to use the registers of that type in order;
    // otherwise we can't really roundtrip it.
    let mut expected_regs_by_ty = enum_map::enum_map!{
        ty => arg_regs_by_ty[ty].iter().copied(),
    };

    let first_instr = &instrs[0];
    let mut arg_exprs = vec![];
    for instr_index in 0..instrs.len() {
        let instr = &instrs[instr_index];

        if (instr.time, instr.difficulty_mask) != (first_instr.time, first_instr.difficulty_mask) {
            return None;  // needs time/difficulty label
        }

        if instr_index > 0 && !instr.labels.is_empty() {
            return None;  // needs label
        }

        match instr.kind {
            RIKind::Standard(IKind::AssignOp(token![=], ty)) => {
                let ty = ReadType::from_ty(ty).unwrap();

                // We want to see if this instruction writes to the next ARG register of this type.
                //
                // To do this we need the reg id being assigned to.  To make sure we read the args correctly
                // by the signature, we defer to the "intrinsic parts" raiser.
                let out_var = instr.parts.outputs[0].clone();
                let (_, var_reg) = ctx.var_reg_from_ast(&out_var.name).unwrap();
                let expected_reg = expected_regs_by_ty[ty].next();
                if Some(var_reg) != expected_reg {
                    // either:
                    // - (expected_reg is Some): not an arg var, or vars of type assigned out of sequence
                    // - (expected_reg is None): too many vars of one type
                    return None;
                }
                // is the assignment using the right type?  (e.g. forbid `%ARG_A = 3.0`)
                if ctx.var_read_ty_from_ast(&out_var) != ctx.var_inherent_ty_from_ast(&out_var) {
                    return None;
                }

                // ok looks like an arg, save it
                arg_exprs.push(instr.parts.plain_args[0].clone());
                continue;
            },

            RIKind::Standard(IKind::CallReg) => {
                let num_instrs_used = instr_index + 1;
                let new_instr = RaiseInstr {
                    fallback_expansion: Some(instrs[..num_instrs_used].iter().cloned().collect()),
                    labels: first_instr.labels.clone(),
                    time: first_instr.time,
                    difficulty_mask: first_instr.difficulty_mask,
                    kind: RIKind::CallRegsGiven,
                    parts: RaisedIntrinsicParts {
                        sub_id: instr.parts.sub_id.clone(),
                        plain_args: arg_exprs,
                        ..Default::default()
                    },
                };
                return Some((new_instr, num_instrs_used));
            },

            _ => {
                // something other than assign or call
                return None;
            },
        }
    }
    None  // encountered end of script
}

fn recognize_diff_switch(
    instrs: &[RaiseInstr],
    diff_flag_names: &crate::ast::diff_str::DiffFlagNames,
) -> Option<(RaiseInstr, usize)> {
    if instrs.len() < 2 || instrs[0].kind != instrs[1].kind || instrs[0].time != instrs[1].time
        || instrs[0].difficulty_mask == DEFAULT_DIFFICULTY_MASK_BYTE
    {
        return None;
    }

    // collect instructions at the beginning of the slice that resemble the first instruction,
    // and have disjoint difficulty masks spanning a range of contiguous bits starting at 0
    let mut next_difficulty = 0;
    let mut explicit_parts = vec![];
    let mut explicit_difficulties = BitSet32::new();
    let mut first_aux_mask = None;
    for instr in instrs {
        // do a full destructure to remind us to update this when adding a new field
        let &RaiseInstr {
            fallback_expansion: _,
            labels: ref this_labels,
            time: this_time,
            difficulty_mask: this_full_mask,
            kind: ref this_kind,
            parts: ref this_parts,
        } = instr;
        let this_full_mask = BitSet32::from_mask(this_full_mask as _);
        // split into the default off part (difficulties) and default on part (aux flags)
        let this_aux_mask = this_full_mask & diff_flag_names.aux_bits();
        let this_diff_mask = this_full_mask ^ this_aux_mask;

        if &this_aux_mask != first_aux_mask.get_or_insert(this_aux_mask) {
            break;
        }

        // label after first instruction
        if explicit_parts.len() > 0 && !this_labels.is_empty() {
            break;
        }

        // check for any "combo breakers"
        if this_kind != &instrs[0].kind || this_time != instrs[0].time {
            break;
        }
        // don't allow any "holes" in the difficulties
        if !(this_diff_mask.first() == Some(next_difficulty) && bitmask_bits_are_contiguous(this_diff_mask)) {
            break;
        }

        explicit_parts.push(this_parts);
        explicit_difficulties.insert(next_difficulty);
        next_difficulty += this_diff_mask.len() as u32;
    }
    let diff_meta = ds_util::DiffSwitchMeta {
        explicit_difficulties,
        num_difficulties: next_difficulty as _,
    };

    let num_instrs_compressed = explicit_parts.len();
    if num_instrs_compressed < 2 {
        return None;  // one case does not a diff switch make!
    }
    // FIXME: maybe this is overzealous
    if diff_meta.num_difficulties < 4 {  // check we have values up to at least Lunatic
        return None;
    }

    // now make each individual arg into a diff switch if necessary
    let parts = diff_switchify_parts(&diff_meta, &explicit_parts)?;

    // The final instruction will have the same aux bits as the original instructions,
    // but with all difficulty bits filled.
    let new_mask = first_aux_mask.unwrap() | diff_flag_names.difficulty_bits();

    Some((RaiseInstr {
        fallback_expansion: Some(instrs[..num_instrs_compressed].iter().cloned().collect()),
        labels: instrs[0].labels.clone(),
        time: instrs[0].time,
        kind: instrs[0].kind.clone(),
        difficulty_mask: new_mask.mask() as _,
        parts,
    }, explicit_parts.len()))
}

fn diff_switchify_parts(
    diff_meta: &ds_util::DiffSwitchMeta,
    explicit_instrs: &[&RaisedIntrinsicParts],
) -> Option<RaisedIntrinsicParts> {
    let first_instr = &explicit_instrs[0];

    let mut explicit_plain_args_by_index = vec![vec![]; first_instr.plain_args.len()];  // [arg_index] -> [instr_index] -> arg
    for instr in explicit_instrs {
        let RaisedIntrinsicParts { jump, sub_id, outputs, plain_args, opcode, pseudo_blob, pseudo_mask, pseudo_arg0 } = instr;

        // things that can't be diff-switchified
        macro_rules! check_eq {
            ($a:expr, $b:expr) => { if $a != $b { return None; }};
        }
        check_eq!(outputs, &first_instr.outputs);
        check_eq!(jump, &first_instr.jump);
        check_eq!(sub_id, &first_instr.sub_id);
        check_eq!(opcode, &first_instr.opcode);
        check_eq!(pseudo_blob, &first_instr.pseudo_blob);
        check_eq!(pseudo_mask, &first_instr.pseudo_mask);
        // FIXME: technically arg0 could be decompiled to a diff switch, but I had trouble implementing
        //        this in a way that wasn't doomed to create bugs for `T(_)` args in the future
        check_eq!(pseudo_arg0, &first_instr.pseudo_arg0);

        check_eq!(plain_args.len(), first_instr.plain_args.len());
        for (arg_index, arg) in plain_args.iter().enumerate() {
            explicit_plain_args_by_index[arg_index].push(arg.clone());
        }
    }

    let mut has_leftover_diff_switch = false;
    let to_diff_switch_or_scalar = |explicit_cases: Vec<ast::Expr>| {
        let first_case = &explicit_cases[0];
        if explicit_cases.iter().all(|case| case == first_case) {
            // all values for this arg are identical, keep just one
            explicit_cases.into_iter().next().unwrap()
        } else {
            has_leftover_diff_switch = true;
            let cases = diff_meta.switch_from_explicit_cases(explicit_cases.into_iter().map(|x| sp!(x)));
            ast::Expr::DiffSwitch(cases)
        }
    };

    // now make each individual arg into a diff switch if necessary
    let compressed_plain_args = explicit_plain_args_by_index.into_iter().map(to_diff_switch_or_scalar).collect::<Vec<_>>();

    // this catches garbage like:
    //
    //   difficulty[1]:  ins_10(30);
    //   difficulty[2]:  ins_10(30);
    //   difficulty[4]:  ins_10(30);
    //   difficulty[8]:  ins_10(30);
    //
    // where the file contains variants for each difficulty but they're all identical
    if !compressed_plain_args.iter().any(|arg| matches!(arg, ast::Expr::DiffSwitch { .. })) {
        return None;
    }

    Some(RaisedIntrinsicParts {
        jump: first_instr.jump.clone(),
        sub_id: first_instr.sub_id.clone(),
        outputs: first_instr.outputs.clone(),
        opcode: first_instr.opcode.clone(),
        pseudo_mask: first_instr.pseudo_mask.clone(),
        pseudo_arg0: first_instr.pseudo_arg0.clone(),
        pseudo_blob: first_instr.pseudo_blob.clone(),
        plain_args: compressed_plain_args,
    })
}

fn bitmask_bits_are_contiguous(mask: BitSet32) -> bool {
    assert!(!mask.is_empty());
    mask.last().unwrap() + 1 - mask.first().unwrap() == mask.len() as u32
}
