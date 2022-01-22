use std::collections::HashMap;

use crate::ast;
use crate::error::{ErrorReported};
use crate::diagnostic::{Diagnostic, RootEmitter};
use crate::pos::{Sp, Span};
use crate::resolve::{DefId, ConstId, Resolutions};
use crate::context::defs::{self, Defs, TypeColor};
use crate::value::ScalarValue;

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
    value_cache: HashMap<ConstId, ScalarValue>,
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
        self.value_cache.get(&id)
    }

    /// Evaluate a const expression on demand.
    /// Requires [`crate::passes::evaluate_const_vars`] to have been run.
    pub fn const_eval(&self, expr: &Sp<ast::Expr>, defs: &Defs, resolutions: &Resolutions, emitter: &RootEmitter) -> Result<ScalarValue, NonConstError> {
        let mut state = FrozenCache { consts: self };
        let context = Context { defs, resolutions, emitter };
        let x = _const_eval(&mut state, &context, expr);
        x
    }

    fn do_deferred_evaluations(
        &mut self,
        defs: &Defs,
        resolutions: &Resolutions,
        emitter: &RootEmitter,
    ) -> Result<(), ErrorReported> {
        let deferred_ids = std::mem::replace(&mut self.deferred_ids, vec![]);
        for id in deferred_ids {
            BuildingCache::run_rooted(self, id, defs, resolutions, emitter)?;
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
}

// =============================================================================

struct Context<'a> {
    defs: &'a Defs,
    resolutions: &'a Resolutions,
    emitter: &'a RootEmitter,
}

/// A throwaway trait used to abstract over the modes in which the const evaluator is run.
trait CacheState {
    type Err;

    /// Get the value of a defined `const`.  If we are currently building the cache, this may trigger
    /// the evaluation of said `const`'s definition. (giving an error on dependency cycles)
    ///
    /// `use_span` is the span where the variable was used.  While we are building the cache, this
    /// will be `None` for any starting nodes in our DFS traversals.
    fn get_const_var_value(
        &mut self,
        context: &Context<'_>,
        const_id: ConstId,
        use_span: Option<Span>,
    ) -> Result<ScalarValue, Self::Err>;

    fn non_const_error(&self, context: &Context, non_const_span: Span) -> Self::Err;
}

/// State during the const evaluation pass, which computes all const vars.
struct BuildingCache<'a> {
    consts: &'a mut Consts,
    /// Stack of `const` items we're evaluating.  This is used to detect circular dependencies.
    eval_stack: Vec<ConstId>,
}

/// State during on-demand expr evaluation, after the const evaluation pass.
struct FrozenCache<'a> {
    consts: &'a Consts,
}

pub struct NonConstError {
    pub non_const_span: Span,
}

impl BuildingCache<'_> {
    // Ensure that the given DefId (and anything else it depends on) is cached.
    fn run_rooted(consts: &mut Consts, id: ConstId, defs: &Defs, resolutions: &Resolutions, emitter: &RootEmitter) -> Result<(), ErrorReported> {
        let mut cache_state = BuildingCache { consts, eval_stack: vec![] };
        let context = Context { defs, resolutions, emitter };
        cache_state.get_const_var_value(&context, id, None).map(|_| ())
    }
}

impl CacheState for BuildingCache<'_> {
    type Err = ErrorReported;

    fn get_const_var_value(
        &mut self,
        context: &Context<'_>,
        const_id: ConstId,
        use_span: Option<Span>,
    ) -> Result<ScalarValue, ErrorReported> {
        let def_id = const_id.def_id;
        if let Some(value) = self.consts.value_cache.get(&const_id) {
            return Ok(value.clone());
        }

        // use_span is None on the outermost call only. (for recursive calls, it holds the span
        // of the variable where it appeared inside another const's definition)
        assert_eq!(self.eval_stack.len() > 0, use_span.is_some());
        if self.eval_stack.contains(&const_id) {
            let root_def_span = context.defs.var_decl_span(def_id).expect("consts always have name spans");
            return Err(context.emitter.emit(error!(
                message("cycle in const definition"),
                primary(root_def_span, "cyclic const"),
                secondary(use_span.expect("len > 0"), "depends on its own value here"),
            )));
        }

        let (expr_loc, expr) = {
            context.defs.var_const_expr(def_id)
                .ok_or_else(|| {
                    // if we get here, we must have encountered a non-const variable inside a const's definition
                    self.non_const_error(context, use_span.expect("must be in another const's definition"))
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
        let value = _const_eval(self, context, &expr)?;
        self.eval_stack.pop();

        // NOTE: We can't avoid this second lookup because because computing the value can mutate the map.
        self.consts.value_cache.insert(const_id, value.clone());
        Ok(value)
    }

    fn non_const_error(&self, context: &Context<'_>, non_const_span: Span) -> ErrorReported {
        context.emitter.emit(error!(
            message("const evaluation error"),
            primary(non_const_span, "non-const expression")
        ))
    }
}

impl CacheState for FrozenCache<'_> {
    type Err = NonConstError;

    fn get_const_var_value(
        &mut self,
        context: &Context<'_>,
        const_id: ConstId,
        use_span: Option<Span>,
    ) -> Result<ScalarValue, Self::Err> {
        if let Some(value) = self.consts.value_cache.get(&const_id) {
            return Ok(value.clone());
        }

        // all const vars should be in the cache, so this DefId must be for a runtime local
        Err(self.non_const_error(context, use_span.expect("must've been used")))
    }

    fn non_const_error(&self, _: &Context<'_>, non_const_span: Span) -> Self::Err {
        NonConstError { non_const_span }
    }
}

fn _const_eval<S: CacheState>(state: &mut S, context: &Context<'_>, expr: &Sp<ast::Expr>) -> Result<ScalarValue, S::Err> {
    match &expr.value {
        &ast::Expr::LitInt { value, .. } => return Ok(ScalarValue::Int(value)),
        &ast::Expr::LitFloat { value, .. } => return Ok(ScalarValue::Float(value)),
        ast::Expr::LitString(ast::LitString { string, .. }) => return Ok(ScalarValue::String(string.clone())),

        ast::Expr::Var(var) => match var.name {
            ast::VarName::Normal { ref ident, .. } => {
                let def_id = context.resolutions.expect_def(ident);
                let const_id = def_id.into();
                let inherent_value = state.get_const_var_value(context, const_id, Some(expr.span))?;
                let cast_value = inherent_value.clone().apply_sigil(var.ty_sigil).expect("shoulda been type-checked");
                return Ok(cast_value)
            },
            ast::VarName::Reg { .. } => {}, // fall to error path
        },

        ast::Expr::UnOp(op, b) => {
            let b_value = _const_eval(state, context, b)?;
            return Ok(op.const_eval(b_value));
        },

        ast::Expr::BinOp(a, op, b) => {
            let a_value = _const_eval(state, context, a)?;
            let b_value = _const_eval(state, context, b)?;
            return Ok(op.const_eval(a_value, b_value));
        },

        ast::Expr::Ternary { cond, left, right, .. } => {
            // NOTE: currently we evaluate both branches so that that we always error on non-const
            //       subexpressions.  Perhaps in the future we'd like to permit "circular" definitions
            //       where the cyclic branches are not actually followed, but then we'd need another way
            //       to continue generating errors on things like REG[1000] wherever they appear.
            let cond_value = _const_eval(state, context, cond)?;
            let left_value = _const_eval(state, context, left)?;
            let right_value = _const_eval(state, context, right)?;
            match cond_value {
                ScalarValue::Int(0) => return Ok(right_value),
                ScalarValue::Int(_) => return Ok(left_value),
                _ => panic!("uncaught type error"),
            }
        },
        _ => {}, // fall to error path
    }

    Err(state.non_const_error(context, expr.span))
}
