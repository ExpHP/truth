use std::collections::HashMap;

use crate::ast;
use crate::error::{CompileError, Diagnostic};
use crate::pos::{Sp, Span};
use crate::resolve::{DefId, Resolutions};
use crate::context::Defs;
use crate::value::ScalarValue;

/// Orchestrates the evaluation of all `const` variables, and caches their values.
///
/// Basically, because consts can freely refer to each other regardless of definition order,
/// dealing with const variables requires a two-stage process where they must first all be defined
/// (which *mostly* occurs during [name resolution][`crate::passes::resolve_names`]), and then
/// they must [all be evaluated][`crate::passes::evaluate_const_vars`].
#[derive(Debug, Clone, Default)]
pub struct Consts {
    deferred_def_ids: Vec<DefId>,
    values: HashMap<DefId, ScalarValue>,
}

impl Consts {
    /// Acknowledge that the given [`DefId`] is a `const` variable so that it can later be evaluated and cached.
    pub fn defer_evaluation_of(&mut self, def_id: DefId) {
        self.deferred_def_ids.push(def_id);
    }

    /// Implementation of [`crate::passes::evaluate_const_vars`].
    ///
    /// Evaluates and cache the expressions assigned to all `const` variables.
    pub fn evaluate_all_deferred(&mut self, defs: &Defs, resolutions: &Resolutions) -> Result<(), CompileError> {
        let deferred_def_ids = std::mem::replace(&mut self.deferred_def_ids, vec![]);
        for def_id in deferred_def_ids {
            Evaluator::run_rooted(self, def_id, defs, resolutions)?;
        }
        Ok(())
    }

    /// Get the value of a const.  In order for this to return `Some`, calls must have been made at
    /// some point to both [`Self::defer_evaluation_of`] and [`Self::evaluate_all_deferred`].
    pub fn get_cached_value(&self, def_id: DefId) -> Option<&ScalarValue> {
        self.values.get(&def_id)
    }
}

/// State object for fully evaluating (not just simplifying) a `const` expression.
///
/// Automatically computes and caches the value of `const` items as their values are needed.
struct Evaluator<'a> {
    consts: &'a mut Consts,
    /// Stack of `const` items we're evaluating.  This is used to detect circular dependencies.
    eval_stack: Vec<DefId>,
    defs: &'a Defs,
    resolutions: &'a Resolutions,
}

impl<'a> Evaluator<'a> {
    // Ensure that the given DefId (and anything else it depends on) is cached.
    fn run_rooted(consts: &'a mut Consts, def_id: DefId, defs: &Defs, resolutions: &Resolutions) -> Result<(), CompileError> {
        Evaluator {
            consts, defs, resolutions,
            eval_stack: vec![]
        }._get_or_compute(None, def_id).map(|_| ())
    }

    // Get the cached value for a DefId, or compute one and store it.
    fn _get_or_compute(&mut self, use_span: Option<Span>, def_id: DefId) -> Result<ScalarValue, CompileError> {
        if let Some(value) = (*(&*self.consts)).values.get(&def_id) {
            return Ok(value.clone());
        }

        // use_span is None on the outermost call only. (for recursive calls, it holds the span
        // of the variable where it appeared inside another const's definition)
        assert_eq!(self.eval_stack.len() > 0, use_span.is_some());
        if self.eval_stack.contains(&def_id) {
            let root_def_span = self.defs.var_decl_span(self.eval_stack[0]).expect("consts always have name spans");
            // FIXME: ADDTEST
            return Err(error!(
                message("cycle in const definition"),
                primary(root_def_span, "cyclic const"),
                secondary(use_span.expect("len > 0"), "depends on its own value here"),
            ));
        }

        let expr = {
            // NOTE: this clone might seem unfortunate but there's some tricky borrowck issues without it
            self.defs.var_const_expr(def_id).cloned()
                .ok_or_else(|| {
                    // if we get here, we must have encountered a non-const variable inside a const's definition
                    self.non_const_error(use_span.expect("must be in another const's definition"))
                })?
        };
        self.eval_stack.push(def_id);
        let value = self._const_eval(&expr)?;
        self.eval_stack.pop();

        // NOTE: We can't avoid this second lookup because because computing the value can mutate the map.
        self.consts.values.insert(def_id, value.clone());
        Ok(value)
    }

    // !!! IMPORTANT !!!
    // This function must be updated in sync with the const simplification pass.
    // (it did not seem possible to factor the shared logic out...)
    fn _const_eval(&mut self, expr: &Sp<ast::Expr>) -> Result<ScalarValue, CompileError> {
        match &expr.value {
            &ast::Expr::LitInt { value, .. } => return Ok(ScalarValue::Int(value)),
            &ast::Expr::LitFloat { value, .. } => return Ok(ScalarValue::Float(value)),
            ast::Expr::LitString(ast::LitString { string, .. }) => return Ok(ScalarValue::String(string.clone())),

            ast::Expr::Var(var) => match var.name {
                ast::VarName::Normal { ref ident } => {
                    let def_id = self.resolutions.expect_def(ident);
                    let inherent_value = self._get_or_compute(Some(expr.span), def_id)?;
                    let cast_value = inherent_value.clone().apply_sigil(var.ty_sigil).expect("shoulda been type-checked");
                    return Ok(cast_value)
                },
                ast::VarName::Reg { .. } => {}, // fall to error path
            },

            ast::Expr::Unop(op, b) => {
                let b_value = self._const_eval(b)?;
                return Ok(op.const_eval(b_value));
            },

            ast::Expr::Binop(a, op, b) => {
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

    fn non_const_error(&self, non_const_span: Span) -> CompileError {
        let mut diag = non_const_error(non_const_span);
        if let Some(&def_id) = self.eval_stack.last() {
            let cur_def_span = self.defs.var_decl_span(def_id).expect("consts always have name spans");
            diag.secondary(cur_def_span, format!("while evaluating this const"));
        }
        diag.into()
    }
}

pub fn non_const_error(non_const_span: Span) -> Diagnostic {
    let mut diag = Diagnostic::error();
    diag.message(format!("const evaluation error"));
    diag.primary(non_const_span, format!("non-const expression"));
    diag
}
