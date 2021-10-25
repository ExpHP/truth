use super::{LowerStmt, LowerInstr, LowerArgs, LowerArg};
use crate::raw;
use crate::ast;
use crate::llir::{IntrinsicInstrKind};
use crate::llir::intrinsic::{IntrinsicInstrAbiPropsKind, abi_props};
use crate::error::{ErrorReported};
use crate::pos::{Sp, Span};
use crate::passes::semantics::time_and_difficulty::TimeAndDifficulty;

// FIXME: Ideally this module wouldn't depend on this type (so the stackful
//        lowerer can also use it) but until the other lowerer exists,
//        doing anything else would be premature abstraction.
use super::stackless::Lowerer;

impl Lowerer<'_, '_> {
    /// Factored out common code for beginning to construct an intrinsic.
    pub(in crate::llir::lower) fn begin_intrinsic(
        &self,
        kind: IntrinsicInstrKind,
        span: Span,
        descr: &str,
    ) -> Result<(u16, &IntrinsicInstrAbiPropsKind, Vec<Option<Sp<LowerArg>>>), ErrorReported> {
        self.intrinsic_instrs.get_opcode_and_abi_props(kind, span, descr)
            .map(|(opcode, abi_props)| {
                let args = vec![None; abi_props.num_instr_args];
                (opcode, &abi_props.kind, args)
            })
            .map_err(|e| self.ctx.emitter.emit(e))
    }

    /// Factored out common code for emitting an intrinsic.
    pub(in crate::llir::lower) fn finish_intrinsic(
        &mut self,
        stmt_data: TimeAndDifficulty,
        opcode: raw::Opcode,
        args: Vec<Option<Sp<LowerArg>>>,
    ) {
        let args = args.into_iter().map(|x| x.expect("arg was not filled in! (bug)")).collect::<Vec<_>>();
        let args = LowerArgs::Known(args);
        self.out.push(LowerStmt::Instr(LowerInstr {
            stmt_data,
            opcode,
            explicit_extra_arg: None,
            user_param_mask: None,
            args,
        }));
    }
}

impl abi_props::UnrepresentablePadding {
    pub(in crate::llir::lower) fn fill_in(&self, out_args: &mut Vec<Option<Sp<LowerArg>>>) -> Result<(), ErrorReported> {
        out_args.truncate(self.index); // padding gets added later during args -> bytes conversion
        Ok(())
    }
}

impl abi_props::JumpArgOrder {
    pub(in crate::llir::lower) fn fill_in(&self, out_args: &mut [Option<Sp<LowerArg>>], goto: &ast::StmtGoto) -> Result<(), ErrorReported> {
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
        let my_args = match self.kind {
            abi_props::JumpArgOrderKind::LocTime => vec![label_arg, time_arg],
            abi_props::JumpArgOrderKind::TimeLoc => vec![time_arg, label_arg],
            abi_props::JumpArgOrderKind::Loc => vec![label_arg],
        };
        for (offset, arg) in my_args.into_iter().enumerate() {
            assert!(out_args[self.index + offset].is_none());
            out_args[self.index + offset] = Some(arg);
        }
        Ok(())
    }
}

impl abi_props::OutOperandType {
    pub(in crate::llir::lower) fn fill_in(&self, out_args: &mut [Option<Sp<LowerArg>>], var: Sp<LowerArg>) -> Result<(), ErrorReported> {
        let &abi_props::OutOperandType { index, kind } = self;

        assert!(out_args[index].is_none());
        // type should already be checked so just shove it in
        let result = match kind {
            abi_props::OutOperandTypeKind::FloatAsInt => sp!(var.span => var.value.with_float_reg_encoded_as_int()),
            abi_props::OutOperandTypeKind::Natural => var,
        };
        out_args[index] = Some(result);
        Ok(())
    }
}

impl abi_props::InputOperandType {
    pub(in crate::llir::lower) fn fill_in(&self, out_args: &mut [Option<Sp<LowerArg>>], value: Sp<LowerArg>) -> Result<(), ErrorReported> {
        let &abi_props::InputOperandType { index } = self;

        assert!(out_args[index].is_none());
        out_args[index] = Some(value);
        Ok(())
    }
}

impl abi_props::ImmediateInt {
    pub(in crate::llir::lower) fn fill_in(&self, out_args: &mut [Option<Sp<LowerArg>>], value: &Sp<i32>) -> Result<(), ErrorReported> {
        let &abi_props::ImmediateInt { index } = self;
        assert!(out_args[index].is_none());
        out_args[index] = Some(sp!(value.span => LowerArg::Raw(value.value.into())));
        Ok(())
    }
}
