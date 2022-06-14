use super::{LowerStmt, LowerInstr, LowerArgs, LowerArg};
use crate::ast;
use crate::raw;
use crate::llir::{IntrinsicInstrKind};
use crate::llir::intrinsic::{IntrinsicInstrAbiParts, abi_parts};
use crate::error::{ErrorReported};
use crate::pos::{Sp, Span};
use crate::passes::semantics::time_and_difficulty::TimeAndDifficulty;

// FIXME: Ideally this module wouldn't depend on this type (so the stackful
//        lowerer can also use it) but until the other lowerer exists,
//        doing anything else would be premature abstraction.
use super::stackless::SingleSubLowerer;

impl SingleSubLowerer<'_, '_> {
    /// Factored out common code for beginning to construct an intrinsic.
    pub(in crate::llir::lower) fn lower_intrinsic<'a>( // lifetime to prevent forall quantification
        &mut self,
        span: Span,
        stmt_data: TimeAndDifficulty,
        kind: IntrinsicInstrKind,
        descr_if_unsupported: &str,
        declare_args: impl FnOnce(&mut IntrinsicBuilder<'a>),
    ) -> Result<(), ErrorReported> {
        let opcode = self.intrinsic_instrs.get_opcode_opt(kind)
            .ok_or_else(|| self.ctx.emitter.emit(self.intrinsic_instrs.missing_intrinsic_error(span, descr_if_unsupported)))?;

        self.lower_intrinsic_by_opcode(span, stmt_data, opcode, declare_args)
    }

    pub(in crate::llir::lower) fn lower_intrinsic_by_opcode<'a>(
        &mut self,
        span: Span,
        stmt_data: TimeAndDifficulty,
        opcode: raw::Opcode,
        declare_args: impl FnOnce(&mut IntrinsicBuilder<'a>),
    ) -> Result<(), ErrorReported> {
        let (_, abi_parts) = self.intrinsic_instrs.get_intrinsic_and_props(opcode)
            .expect("(bug!) how did we get this opcode if it isn't an intrinsic?");

        // let the caller provide us with various data appropriate to this intrinsic
        let mut builder = IntrinsicBuilder::default();
        declare_args(&mut builder);

        // convert them into a vec using the validated abi info
        let args = LowerArgs::Known(builder.into_vec(abi_parts)?);

        self.out.push(sp!(span => LowerStmt::Instr(LowerInstr {
            stmt_data,
            opcode,
            explicit_extra_arg: None,
            user_param_mask: None,
            args,
        })));
        Ok(())
    }
}

/// Holds arguments to be lowered for an intrinsic.  The data should be placed in the same places
/// that [`AbiParts`] uses for this intrinsic.
#[derive(Default)]
pub(in crate::llir::lower) struct IntrinsicBuilder<'a> {
    pub(in crate::llir::lower) jump: Option<&'a ast::StmtGoto>,
    pub(in crate::llir::lower) sub_id: Option<Sp<LowerArg>>,
    pub(in crate::llir::lower) plain_args: Vec<Sp<LowerArg>>,
    pub(in crate::llir::lower) outputs: Vec<Sp<LowerArg>>,
}

impl IntrinsicBuilder<'_> {
    // use the data in self and the indices in abi_parts to populate all of the elements of out_args
    fn into_vec(
        self,
        abi_parts: &IntrinsicInstrAbiParts,
    ) -> Result<Vec<Sp<LowerArg>>, ErrorReported> {
        // full pattern match to fail when new fields are added
        let &IntrinsicInstrAbiParts {
            num_instr_args, padding: ref padding_info, plain_args: ref plain_args_info,
            outputs: ref outputs_info, jump: ref jump_info, sub_id: sub_id_info,
        } = abi_parts;
        // check that the caller's 'build' closure put all of the right things for this intrinsic
        assert_eq!(self.jump.is_some(), jump_info.is_some());
        assert_eq!(self.sub_id.is_some(), sub_id_info.is_some());
        assert_eq!(self.plain_args.len(), plain_args_info.len());
        assert_eq!(self.outputs.len(), outputs_info.len());

        // Start with empty options then fill them in.
        // NOTE: This work buffer could be saved between instructions as a minor optimization...
        let mut out_args = vec![None; num_instr_args];

        // padding gets added later during args -> bytes conversion so we don't need to fill it
        out_args.truncate(padding_info.index);

        // fill in all of the options
        if let (Some(goto_ast), &Some(jump_info)) = (self.jump, jump_info) {
            populate_time_args(goto_ast, jump_info, &mut out_args);
        }

        for (value, &index) in self.plain_args.into_iter().zip(plain_args_info) {
            assert!(out_args[index].is_none());
            out_args[index] = Some(value);
        }

        if let Some((value, index)) = self.sub_id.zip(sub_id_info) {
            assert!(out_args[index].is_none());
            out_args[index] = Some(value);
        }

        for (var, &(index, mode)) in self.outputs.into_iter().zip(outputs_info) {
            let var = match mode {
                abi_parts::OutputArgMode::FloatAsInt => sp!(var.span => var.value.with_float_reg_encoded_as_int()),
                abi_parts::OutputArgMode::Natural => var,
            };
            assert!(out_args[index].is_none());
            out_args[index] = Some(var);
        }

        // all options should be Some(_) now
        Ok(out_args.into_iter().map(|x| x.expect("arg was not filled in! (bug)")).collect::<Vec<_>>())
    }
}

fn populate_time_args(goto: &ast::StmtGoto, info: (usize, abi_parts::JumpArgOrder), out_args: &mut [Option<Sp<LowerArg>>]) {
    let (out_index, order) = info;
    let label_arg = goto.destination.clone().sp_map(LowerArg::Label);
    let time_arg = match goto.time {
        Some(time) => time.sp_map(|t| LowerArg::Raw(t.into())),
        None => goto.destination.clone().sp_map(LowerArg::TimeOf),
    };

    // NOTE: No point throwing an error for the case of an explicit time arg being given
    //       when one can't be output; even if we only allow implicit time args, we will
    //       still miscompile labels placed at the previous instruction's time.
    // TODO: we can fix this by outputting a 'checked' variant of LowerArg::TimeOf when
    //       a time arg can't be encoded.
    let my_args = match order {
        abi_parts::JumpArgOrder::LocTime => vec![label_arg, time_arg],
        abi_parts::JumpArgOrder::TimeLoc => vec![time_arg, label_arg],
        abi_parts::JumpArgOrder::Loc => vec![label_arg],
    };
    for (offset, arg) in my_args.into_iter().enumerate() {
        assert!(out_args[out_index + offset].is_none());
        out_args[out_index + offset] = Some(arg);
    }
}
