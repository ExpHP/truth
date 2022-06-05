use indexmap::IndexMap;

use crate::ast;
use crate::error::{ErrorReported};
use crate::diagnostic::{Diagnostic, RootEmitter};
use crate::pos::{Sp, Span};
use crate::resolve::{DefId, ConstId, Resolutions};
use crate::context::defs::{self, Defs};
use crate::value::ScalarValue;
use crate::debug_info;

/// Orchestrates the evaluation of all `const` variables, and caches their values.
///
/// Basically, because consts can freely refer to each other regardless of definition order,
/// dealing with const variables requires a two-stage process where they must first all be defined
/// (which *mostly* occurs during [name resolution][`crate::passes::resolution`]), and then
/// they must [all be evaluated][`crate::passes::evaluate_const_vars`].
#[derive(Debug, Clone, Default)]
pub struct Consts {
    deferred_ids: Vec<ConstId>,
    deferred_equality_checks: Vec<EqualityCheck>,
    values: IndexMap<ConstId, ScalarValue>,
}

#[derive(Debug, Clone)]
struct EqualityCheck {
    noun: &'static str,
    id_1: ConstId,
    id_2: ConstId,
}

impl Consts {
    /// Acknowledge that the given [`DefId`] is a `const` variable so that it can later be evaluated
    /// during [`crate::passes::evaluate_const_vars`].
    pub(in crate::context) fn defer_evaluation_of(&mut self, def_id: DefId) -> ConstId {
        let const_id = def_id.into();
        self.deferred_ids.push(const_id);
        const_id
    }

    /// Require that two consts have the same value.
    ///
    /// Later, during [`crate::passes::evaluate_const_vars`], these will be compared and will
    /// generate an `"ambiguous value"` error if they don't match.
    ///
    /// It is assumed that both consts have the same name; this mechanism is supposed to be like
    /// redefinition errors, but for enum consts.
    pub(in crate::context) fn defer_equality_check(&mut self, noun: &'static str, id_1: ConstId, id_2: ConstId) {
        self.deferred_equality_checks.push(EqualityCheck { noun, id_1, id_2 });
    }

    /// Implementation of [`crate::passes::evaluate_const_vars`].  Please call that instead.
    ///
    /// Evaluates and caches the expressions assigned to all `const` variables, and performs
    /// all deferred equality checks.
    #[doc(hidden)]
    pub fn evaluate_all_deferred(
        &mut self,
        defs: &Defs,
        resolutions: &Resolutions,
        emitter: &RootEmitter,
    ) -> Result<(), ErrorReported> {
        self.do_deferred_evaluations(defs, resolutions, emitter)?;
        self.do_deferred_equality(defs, emitter)
    }

    /// Get the value of a const.  In order for this to return `Some`, calls must have been made at
    /// some point to both [`Self::defer_evaluation_of`] and [`Self::evaluate_all_deferred`].
    pub fn get_cached_value(&self, id: ConstId) -> Option<&ScalarValue> {
        self.values.get(&id)
    }

    fn do_deferred_evaluations(
        &mut self,
        defs: &Defs,
        resolutions: &Resolutions,
        emitter: &RootEmitter,
    ) -> Result<(), ErrorReported> {
        let deferred_ids = std::mem::replace(&mut self.deferred_ids, vec![]);
        for id in deferred_ids {
            Evaluator::run_rooted(self, id, defs, resolutions, emitter)?;
        }
        Ok(())
    }

    fn do_deferred_equality(
        &mut self,
        defs: &Defs,
        emitter: &RootEmitter,
    ) -> Result<(), ErrorReported> {
        let deferred_equality_checks = std::mem::replace(&mut self.deferred_equality_checks, vec![]);

        for EqualityCheck { noun, id_1, id_2 } in deferred_equality_checks {
            let value_1 = self.get_cached_value(id_1).expect("missing value for def_1");
            let value_2 = self.get_cached_value(id_2).expect("missing value for def_2");
            if value_1 != value_2 {
                let ident = defs.var_name(id_2.def_id);
                let span_1 = defs.var_decl_span(id_1.def_id).expect("missing span for def_1");
                let span_2 = defs.var_decl_span(id_2.def_id).expect("missing span for def_2");
                return Err(emitter.emit(error!(
                    message("ambiguous value for {} '{}'", noun, ident),
                    primary(span_1, "definition with value {}", value_1),
                    primary(span_2, "definition with value {}", value_2),
                )));
            }
        }
        Ok(())
    }

    pub fn debug_info(&self, defs: &Defs) -> Vec<debug_info::Const> {
        self.values.iter().map(|(const_id, value)| {
            debug_info::Const {
                name: defs.var_name(const_id.def_id).to_string(),
                name_span: defs.var_decl_span(const_id.def_id).map(Into::into),
                value: value.clone().into(),
            }
        }).collect()
    }
}

/// State object for fully evaluating (not just simplifying) a `const` expression.
///
/// Automatically computes and caches the value of `const` items as their values are needed.
struct Evaluator<'a> {
    consts: &'a mut Consts,
    /// Stack of `const` items we're evaluating.  This is used to detect circular dependencies.
    eval_stack: Vec<ConstId>,
    defs: &'a Defs,
    resolutions: &'a Resolutions,
    emitter: &'a RootEmitter,
}

impl<'a> Evaluator<'a> {
    // Ensure that the given DefId (and anything else it depends on) is cached.
    fn run_rooted(consts: &mut Consts, id: ConstId, defs: &Defs, resolutions: &Resolutions, emitter: &RootEmitter) -> Result<(), ErrorReported> {
        Evaluator {
            consts, defs, resolutions, emitter,
            eval_stack: vec![]
        }._get_or_compute(None, id).map(|_| ())
    }

    // Get the cached value for a DefId, or compute one and store it.
    fn _get_or_compute(&mut self, use_span: Option<Span>, const_id: ConstId) -> Result<ScalarValue, ErrorReported> {
        let def_id = const_id.def_id;
        if let Some(value) = (*(&*self.consts)).values.get(&const_id) {
            return Ok(value.clone());
        }

        // use_span is None on the outermost call only. (for recursive calls, it holds the span
        // of the variable where it appeared inside another const's definition)
        assert_eq!(self.eval_stack.len() > 0, use_span.is_some());
        if self.eval_stack.contains(&const_id) {
            let root_def_span = self.defs.var_decl_span(def_id).expect("consts always have name spans");
            return Err(self.emitter.emit(error!(
                message("cycle in const definition"),
                primary(root_def_span, "cyclic const"),
                secondary(use_span.expect("len > 0"), "depends on its own value here"),
            )));
        }

        let (expr_loc, expr) = {
            self.defs.var_const_expr(def_id)
                .ok_or_else(|| {
                    // if we get here, we must have encountered a non-const variable inside a const's definition
                    self.non_const_error(use_span.expect("must be in another const's definition"))
                })?
        };
        let expr_span = match expr_loc {
            defs::ConstExprLoc::Span(span) => span,
            defs::ConstExprLoc::Builtin => Span::NULL,  // there's no way _const_eval will fail on a builtin const
        };
        // NOTE: this clone might seem unfortunate but there's some tricky borrowck issues without it.
        // Also we have to add a span now.
        let expr = sp!(expr_span => expr.clone());

        self.eval_stack.push(const_id);
        // FIXME: avoiding recursion here would be nice
        let value_result = self._const_eval(&expr);
        self.eval_stack.pop();  // cleanup before possibly diverging with '?'
        let value = value_result?;

        // NOTE: We can't avoid this second lookup because because computing the value can mutate the map.
        self.consts.values.insert(const_id, value.clone());
        Ok(value)
    }

    // !!! IMPORTANT !!!
    // This function must be updated in sync with the const simplification pass.
    // (it did not seem possible to factor the shared logic out...)
    fn _const_eval(&mut self, expr: &Sp<ast::Expr>) -> Result<ScalarValue, ErrorReported> {
        match &expr.value {
            &ast::Expr::LitInt { value, .. } => return Ok(ScalarValue::Int(value)),
            &ast::Expr::LitFloat { value, .. } => return Ok(ScalarValue::Float(value)),
            ast::Expr::LitString(ast::LitString { string, .. }) => return Ok(ScalarValue::String(string.clone())),

            ast::Expr::Var(var) => match var.name {
                ast::VarName::Normal { ref ident, .. } => {
                    let def_id = self.resolutions.expect_def(ident);
                    let const_id = def_id.into();
                    let inherent_value = self._get_or_compute(Some(expr.span), const_id)?;
                    let cast_value = inherent_value.clone().cast_by_ty_sigil(var.ty_sigil).expect("shoulda been type-checked");
                    return Ok(cast_value);
                },
                ast::VarName::Reg { .. } => {}, // fall to error path
            },

            ast::Expr::EnumConst { ident, .. } => {
                let def_id = self.resolutions.expect_def(ident);
                let const_id = def_id.into();
                return self._get_or_compute(Some(expr.span), const_id);
            },

            ast::Expr::UnOp(op, b) => {
                let b_value = self._const_eval(b)?;
                return op.const_eval(b_value).ok_or_else(|| self.non_const_error(expr.span));
            },

            ast::Expr::BinOp(a, op, b) => {
                let a_value = self._const_eval(a)?;
                let b_value = self._const_eval(b)?;
                return Ok(op.const_eval(a_value, b_value));
            },

            ast::Expr::Ternary { cond, left, right, .. } => {
                // NOTE: currently we evaluate both branches so that that we always error on non-const
                //       subexpressions.  Perhaps in the future we'd like to permit "circular" definitions
                //       where the cyclic branches are not actually followed, but then we'd need another way
                //       to continue generating errors on things like REG[1000] wherever they appear.
                let cond_value = self._const_eval(cond)?;
                let left_value = self._const_eval(left)?;
                let right_value = self._const_eval(right)?;
                match cond_value {
                    ScalarValue::Int(0) => return Ok(right_value),
                    ScalarValue::Int(_) => return Ok(left_value),
                    _ => panic!("uncaught type error"),
                }
            },
            _ => {}, // fall to error path
        }

        Err(self.non_const_error(expr.span))
    }

    fn non_const_error(&self, non_const_span: Span) -> ErrorReported {
        let mut diag = non_const_error(non_const_span);
        if let Some(&ConstId { def_id }) = self.eval_stack.last() {
            let cur_def_span = self.defs.var_decl_span(def_id).expect("consts always have name spans");
            diag.secondary(cur_def_span, format!("while evaluating this const"));
        }
        self.emitter.emit(diag)
    }
}

pub fn non_const_error(non_const_span: Span) -> Diagnostic {
    error!(
        message("const evaluation error"),
        primary(non_const_span, "non-const expression")
    )
}
