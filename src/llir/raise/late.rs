use super::{
    RaiseInstr, RaiseIntrinsicKind, RaisedIntrinsicParts, IntrinsicInstrKind,
    SingleSubRaiser, CannotRaiseIntrinsic, Label,
};

use crate::raw;
use crate::ast::{self, pseudo};
use crate::ident::ResIdent;
use crate::pos::{Sp, Span};
use crate::diagnostic::{Emitter};
use crate::error::{ErrorReported};

use RaiseIntrinsicKind as RIKind;
use IntrinsicInstrKind as IKind;

impl SingleSubRaiser<'_, '_> {
    /// The final pass of raising a stmt, which converts our intermediate format into AST statements.
    pub fn raise_middle_to_ast(&self, emitter: &impl Emitter, script: &[RaiseInstr]) -> Result<Vec<Sp<ast::Stmt>>, ErrorReported> {
        let mut out = vec![];
        let mut label_gen = LabelEmitter::new();

        for instr in script {
            label_gen.emit_labels_for_instr(&mut out, instr);
            self.raise_instr(emitter, &instr, |stmt| {
                out.push(self.make_stmt(instr.difficulty_mask, stmt))
            });
        }

        Ok(out)
    }

    fn raise_instr(
        &self,
        emitter: &impl Emitter,
        instr: &RaiseInstr,
        mut emit_stmt: impl FnMut(ast::StmtKind),
    ) {
        // &mut dyn FnMut so it can be passed recursively
        self._raise_instr(emitter, instr, &mut emit_stmt)
    }

    fn _raise_instr(
        &self,
        emitter: &impl Emitter,
        instr: &RaiseInstr,
        emit_stmt: &mut dyn FnMut(ast::StmtKind),
    ) {
        match self.try_raise_intrinsic(instr, emit_stmt) {
            Ok(()) => {},
            Err(CannotRaiseIntrinsic) => match &instr.fallback_expansion {
                Some(fallback_instrs) => {
                    for child_instr in fallback_instrs {
                        self._raise_instr(emitter, child_instr, emit_stmt);
                    }
                },
                None => {
                    // (FIXME: should CannotRaiseIntrinsic have a minor payload to provide more context?)
                    panic!("cannot render instr of kind {:?} with no fallback", instr.kind);
                },
            },
        }
    }


    fn try_raise_intrinsic(
        &self,
        instr: &RaiseInstr,
        emit_stmt: &mut dyn FnMut(ast::StmtKind),
    ) -> Result<(), CannotRaiseIntrinsic> {
        let RaisedIntrinsicParts {
            mut sub_id, mut jump, outputs, plain_args,
            opcode, pseudo_arg0, pseudo_blob, pseudo_mask,
        } = instr.parts.clone();
        let mut outputs = outputs.into_iter();
        let mut plain_args = plain_args.into_iter();

        match instr.kind {
            RIKind::Instruction => {
                let mut pseudos = vec![];
                if let Some(extra_arg) = pseudo_arg0 {
                    pseudos.push(sp!(ast::PseudoArg {
                        at_sign: sp!(()), eq_sign: sp!(()),
                        kind: sp!(token![arg0]),
                        value: sp!(extra_arg),
                    }));
                }

                emit_stmt(ast::StmtKind::Expr(sp!(ast::Expr::Call(ast::ExprCall {
                    name: sp!(ast::CallableName::Ins { opcode: opcode.unwrap(), language: Some(self.language) }),
                    pseudos,
                    args: plain_args.map(|expr| sp!(expr)).collect(),
                }))));
            },


            RIKind::Blob => {
                let mut pseudos = vec![];

                let pseudo_mask = pseudo_mask.unwrap();
                if pseudo_mask != 0 {
                    pseudos.push(sp!(ast::PseudoArg {
                        at_sign: sp!(()), eq_sign: sp!(()),
                        kind: sp!(token![mask]),
                        value: sp!(ast::Expr::LitInt { value: pseudo_mask as i32, radix: ast::IntRadix::Bin }),
                    }));
                }

                if let Some(extra_arg) = pseudo_arg0 {
                    pseudos.push(sp!(ast::PseudoArg {
                        at_sign: sp!(()), eq_sign: sp!(()),
                        kind: sp!(token![arg0]),
                        value: sp!(extra_arg),
                    }));
                }

                pseudos.push(sp!(ast::PseudoArg {
                    at_sign: sp!(()), eq_sign: sp!(()),
                    kind: sp!(token![blob]),
                    value: sp!(pseudo::format_blob(pseudo_blob.as_ref().unwrap()).into()),
                }));

                emit_stmt(ast::StmtKind::Expr(sp!(ast::Expr::Call(ast::ExprCall {
                    name: sp!(ast::CallableName::Ins { opcode: opcode.unwrap(), language: Some(self.language) }),
                    pseudos,
                    args: vec![],
                }))));
            },


            RIKind::Standard(IKind::Jmp) => {
                let goto = jump.take().unwrap();
                emit_stmt(stmt_goto!(rec_sp!(Span::NULL => as kind, goto #(goto.destination) #(goto.time))));
            },


            RIKind::Standard(IKind::AssignOp(op, _ty)) => {
                let var = outputs.next().unwrap();
                let value = plain_args.next().unwrap();
                emit_stmt(stmt_assign!(rec_sp!(Span::NULL => as kind, #var #op #value)));
            },


            RIKind::Standard(IKind::BinOp(op, _ty)) => {
                let var = outputs.next().unwrap();
                let a = plain_args.next().unwrap();
                let b = plain_args.next().unwrap();
                emit_stmt(stmt_assign!(rec_sp!(Span::NULL => as kind, #var = expr_binop!(#a #op #b))));
            },


            RIKind::Standard(IKind::UnOp(op, _ty)) => {
                let var = outputs.next().unwrap();
                let b = plain_args.next().unwrap();
                emit_stmt(stmt_assign!(rec_sp!(Span::NULL => as kind, #var = expr_unop!(#op #b))));
            },


            RIKind::Standard(IKind::InterruptLabel) => {
                let interrupt = plain_args.next().unwrap();
                let interrupt = sp!(Span::NULL => match interrupt.as_const_int() {
                    Some(interrupt_id) => interrupt_id,
                    None => {
                        assert!(matches!(interrupt, ast::Expr::Var { .. }));
                        return Err(CannotRaiseIntrinsic);  // register in interrupt label
                    },
                });
                emit_stmt(stmt_interrupt!(rec_sp!(Span::NULL => as kind, #interrupt)));
            },


            RIKind::Standard(IKind::CountJmp) => {
                let goto = jump.take().unwrap();
                let var = outputs.next().unwrap();
                emit_stmt(stmt_cond_goto!(rec_sp!(Span::NULL =>
                    as kind, if expr_pre_xcrement!(-- #var) goto #(goto.destination) #(goto.time)
                )));
            },


            RIKind::Standard(IKind::CondJmp(op, _ty)) => {
                let goto = jump.take().unwrap();
                let a = plain_args.next().unwrap();
                let b = plain_args.next().unwrap();
                emit_stmt(stmt_cond_goto!(rec_sp!(Span::NULL =>
                    as kind, if expr_binop!(#a #op #b) goto #(goto.destination) #(goto.time)
                )));
            },


            RIKind::Standard(IKind::CallEosd) => {
                let ident = ResIdent::new_null(sub_id.take().unwrap());
                let name = ast::CallableName::Normal { ident, language_if_ins: None };

                let int = plain_args.next().unwrap();
                let float = plain_args.next().unwrap();

                emit_stmt(ast::StmtKind::Expr(sp!(ast::Expr::Call(ast::ExprCall {
                    name: sp!(name.into()),
                    pseudos: vec![],
                    // FIXME: If we decompile functions to have different signatures on a per-function
                    //        basis we'll need to adjust the argument order appropriately here
                    args: vec![sp!(int), sp!(float)],
                }))));
            },


            // Should be handled earlier.
            // We can't decompile it now, as we have already read past the other instructions
            // containing the values we'd want to put as function call arguments.
            | RIKind::Standard(IKind::CallReg) => return Err(CannotRaiseIntrinsic),


            // Individual pieces of multipart intrinsics, which can show up in this method when
            // they appear alone or with e.g. time labels in-between.
            | RIKind::Standard(IKind::CondJmp2A { .. })
            | RIKind::Standard(IKind::CondJmp2B { .. })
            => return Err(CannotRaiseIntrinsic),


            | RIKind::End
            => {},


            // if this hasn't been upgraded to CallProper yet then it may not match the sub definition;
            // we can't raise this.
            | RIKind::CallRegsGiven => return Err(CannotRaiseIntrinsic),


            // a call that matches the sub definition
            | RIKind::CallProper => {
                let ident = ResIdent::new_null(sub_id.take().unwrap());
                let name = ast::CallableName::Normal { ident, language_if_ins: None };

                emit_stmt(ast::StmtKind::Expr(sp!(ast::Expr::Call(ast::ExprCall {
                    name: sp!(name),
                    pseudos: vec![],
                    args: plain_args.map(|x| sp!(x)).collect(),
                }))));
            },
        }
        Ok(())
    }
}


// =============================================================================

/// Emits time and difficulty labels from an instruction stream.
#[derive(Debug, Clone)]
struct LabelEmitter {
    prev_time: raw::Time,
}

impl LabelEmitter {
    fn new() -> Self {
        LabelEmitter {
            prev_time: 0,
        }
    }

    fn emit_labels_for_instr(&mut self, out: &mut Vec<Sp<ast::Stmt>>, instr: &RaiseInstr) {
        self.emit_labels_for_instr_with(instr, &mut |stmt| out.push(stmt))
    }

    // -----------------
    // underlying implementation which uses a callback

    fn emit_labels_for_instr_with(&mut self, instr: &RaiseInstr, emit: &mut impl FnMut(Sp<ast::Stmt>)) {
        assert!(instr.labels.len() < 2, "multiple labels on instr not yet fully supported");
        self.emit_labels_with(instr.labels.get(0), instr.time, emit);
    }

    fn emit_labels_with(&mut self, label: Option<&Label>, time: raw::Time, emit: &mut impl FnMut(Sp<ast::Stmt>)) {
        self.emit_offset_and_time_labels_with(label, time, emit);

        // not statements anymore
        // self.emit_difficulty_labels_with(difficulty, emit);
    }

    // emit both labels like "label_354:" and "+24:"
    fn emit_offset_and_time_labels_with(
        &mut self,
        offset_label: Option<&Label>,
        time: raw::Time,
        emit: &mut impl FnMut(Sp<ast::Stmt>),
    ) {
        // labels don't need to worry about difficulty
        let make_stmt = |kind| sp!(ast::Stmt { node_id: None, diff_label: None, kind });

        // in the current implementation there is at most one regular label at this offset, which
        // may be before or after a relative time jump.
        let mut offset_label = offset_label;
        macro_rules! put_offset_label_here_if_it_has_time {
            ($time:expr) => {
                if let Some(label) = &offset_label {
                    if label.time_label == $time {
                        emit(make_stmt(ast::StmtKind::Label(sp!(label.label.clone()))));
                        offset_label = None;
                    }
                }
            };
        }

        put_offset_label_here_if_it_has_time!(self.prev_time);

        // add time labels
        let prev_time = self.prev_time;
        if time != prev_time {
            if prev_time < 0 && 0 <= time {
                // Include an intermediate 0: between negative and positive.
                // This is because ANM scripts can start with instrs at -1: that have special properties.
                emit(make_stmt(ast::StmtKind::AbsTimeLabel(sp!(0))));
                if time > 0 {
                    emit(make_stmt(ast::StmtKind::RelTimeLabel {
                        delta: sp!(time),
                        _absolute_time_comment: Some(time),
                    }));
                }
            } else if time < prev_time {
                emit(make_stmt(ast::StmtKind::AbsTimeLabel(sp!(time))));
            } else if prev_time < time {
                emit(make_stmt(ast::StmtKind::RelTimeLabel {
                    delta: sp!(time - prev_time),
                    _absolute_time_comment: Some(time),
                }));
            }
        }

        put_offset_label_here_if_it_has_time!(time);

        // do we have a label we never placed?
        if let Some(label) = &offset_label {
            panic!("impossible time for label: (times: {} -> {}) {:?}", self.prev_time, time, label);
        }

        self.prev_time = time;
    }
}
