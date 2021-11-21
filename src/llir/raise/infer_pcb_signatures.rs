use super::{RaiseIntrinsicKind, RaiseScript};

use crate::ast;
use crate::context::CompilerContext;
use crate::ident::Ident;
use crate::resolve::IdMap;
use crate::value::ReadType;

use RaiseIntrinsicKind as RIKind;

/// Signatures for [`IKind::CallReg`] deduced directly from callsites.
pub struct CallRegSignatures {
    pub signatures: IdMap<Ident, Vec<ReadType>>,
}

impl CallRegSignatures {
    /// Collect signatures from callsites, automatically setting [`RIKind::CallProper`] on those that
    /// match the returned signatures.
    pub fn infer_from_calls<'a>(
        scripts: impl IntoIterator<Item = &'a mut RaiseScript>,
        ctx: &CompilerContext<'_>,
    ) -> CallRegSignatures {
        let mut signatures = IdMap::default();
        for script in scripts {
            for instr in &mut script.instrs {
                if instr.kind == RIKind::CallRegsGiven {
                    if let Some(param_types) = param_types_from_args(&instr.parts.plain_args, ctx) {
                        let saved_param_types = {
                            &*signatures
                                .entry(instr.parts.sub_id.clone().unwrap())
                                .or_insert_with(|| param_types.clone())
                        };
                        if &param_types == saved_param_types {
                            instr.kind = RIKind::CallProper;
                        }
                    }
                }
            }
        }
        CallRegSignatures { signatures }
    }
}

// NOTE: I don't think it is possible for this to ever return None as that would suggest that
//       somehow something other than an int or float operand was decompiled from a register assignment.
//       But never say never...
fn param_types_from_args(args: &[ast::Expr], ctx: &CompilerContext<'_>) -> Option<Vec<ReadType>> {
    args.iter()
        .map(|arg| {
            arg.compute_ty(ctx)
                .as_value_ty()
                .and_then(ReadType::from_ty)
        })
        .collect()
}
