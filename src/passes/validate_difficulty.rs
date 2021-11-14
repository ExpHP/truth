//! See [`run`].

use crate::context::CompilerContext;
use crate::error::{ErrorFlag, ErrorReported};
use crate::ast::{self, Visit};
use crate::diagnostic::Emitter;
use crate::passes::semantics::time_and_difficulty::{TimeAndDifficultyHelper};
use crate::llir::LanguageHooks;
use crate::pos::Sp;

/// Scans the AST for improper usage of difficulty-related constructs.
///
/// To use this, you must call a method whose scope is at least as large as [`VisitMut::visit_root_block`].
pub fn run<V: ast::Visitable>(ast: &V, ctx: &CompilerContext<'_>, hooks: &dyn LanguageHooks) -> Result<(), ErrorReported> {
    let mut visitor = Visitor { ctx, hooks, errors: Default::default(), helper: Default::default() };
    ast.visit_with(&mut visitor);
    visitor.errors.into_result(())
}

/// Scans the AST for usage of difficulty-related constructs in languages that don't support them.
///
/// To use this, you must call a method whose scope is at least as large as [`VisitMut::visit_root_block`].
pub fn forbid_difficulty<V: ast::Visitable>(ast: &V, ctx: &CompilerContext<'_>) -> Result<(), ErrorReported> {
    let mut visitor = ForbidDifficultyVisitor { emitter: &ctx.emitter, errors: Default::default() };
    ast.visit_with(&mut visitor);
    visitor.errors.into_result(())
}

struct Visitor<'a, 'ctx> {
    helper: TimeAndDifficultyHelper,
    errors: ErrorFlag,
    ctx: &'a CompilerContext<'ctx>,
    hooks: &'a dyn LanguageHooks,
}

impl Visit for Visitor<'_, '_> {
    fn visit_stmt(&mut self, stmt: &Sp<ast::Stmt>) {
        self.helper.enter_stmt(stmt);

        // check diff labels
        if has_unintuitive_interaction_with_difficulty(&stmt.kind) {
            if let Some(diff_label_mask) = self.helper.difficulty_mask_if_nontrivial() {
                let mut diag = warning!(
                    message("{} inside difficulty label may have surprising behavior", stmt.kind.descr()),
                    primary(stmt, "{}", stmt.kind.descr()),
                    secondary(diff_label_mask, "in this difficulty label"),
                );

                if let Some(reg) = self.hooks.difficulty_register() {
                    let difficulty_reg_name = crate::fmt::stringify(&self.ctx.reg_to_ast(self.hooks.language(), reg));
                    diag.note(format!("\
                        This code may not behave as expected! \
                        Try using the difficulty register instead, e.g. `if ({} == 2)` instead of a difficulty label. \
                    ", difficulty_reg_name));
                }
                self.ctx.emitter.emit(diag).ignore();
            }
        }

        // fail on bad diff switches
        let mut switch_checker = SwitchLenChecker::default();
        switch_checker.visit_stmt(stmt);
        if let Err(e) = switch_checker.into_result(self.ctx.emitter) {
            self.errors.set(e)
        }

        // recurse
        ast::walk_stmt(self, stmt);

        self.helper.exit_stmt(stmt);
    }

    fn visit_root_block(&mut self, block: &ast::Block) {
        self.helper.enter_root_block();
        self.visit_block(block);
        self.helper.exit_root_block();
    }

    fn visit_block(&mut self, block: &ast::Block) {
        self.helper.enter_block();
        ast::walk_block(self, block);
        self.helper.exit_block();
    }
}

fn has_unintuitive_interaction_with_difficulty(stmt: &ast::StmtKind) -> bool {
    match stmt {
        | ast::StmtKind::Item { .. }
        | ast::StmtKind::Jump { .. }
        | ast::StmtKind::CondJump { .. }
        | ast::StmtKind::Return { .. }
        | ast::StmtKind::Expr { .. }
        | ast::StmtKind::Block { .. }
        | ast::StmtKind::Assignment { .. }
        | ast::StmtKind::Declaration { .. }
        | ast::StmtKind::CallSub { .. }
        | ast::StmtKind::InterruptLabel { .. }
        | ast::StmtKind::Label { .. }
        | ast::StmtKind::ScopeEnd { .. }
        | ast::StmtKind::NoInstruction { .. }
        => false,

        // time labels can induce waiting even if filtered out by difficulty.
        | ast::StmtKind::AbsTimeLabel { .. }
        | ast::StmtKind::RelTimeLabel { .. }
        => true,

        // control flow can enter even an `if (false)` block!
        // this is observable if an inner difficulty label re-enables a flag.
        | ast::StmtKind::CondChain { .. }
        => true,

        // more blocks that might be surprising to be entered
        // (e.g. `loop` and `times` would run exactly once instead of 0 times)
        | ast::StmtKind::Loop { .. }
        | ast::StmtKind::While { .. }
        | ast::StmtKind::Times { .. }
        => true,
    }
}

// =============================================================================

/// For checking that switches have equal length within a
#[derive(Default)]
struct SwitchLenChecker {
    first_len: Option<Sp<usize>>,
    second_len: Option<Sp<usize>>,
}

impl Visit for SwitchLenChecker {
    fn visit_expr(&mut self, expr: &Sp<ast::Expr>) {
        ast::walk_expr(self, expr);
        if let ast::Expr::DiffSwitch(cases) = &expr.value {
            self.first_len.get_or_insert(sp!(expr.span => cases.len()));

            if self.first_len.unwrap() != cases.len() {
                self.second_len.get_or_insert(sp!(expr.span => cases.len()));
            }
        }
    }

    fn visit_block(&mut self, _: &ast::Block) {}
}

impl SwitchLenChecker {
    fn into_result(self, emitter: &dyn Emitter) -> Result<(), ErrorReported> {
        if let Some(second_len) = self.second_len {
            let first_len = self.first_len.unwrap();
            return Err(emitter.as_sized().emit(error!(
                message("mismatched diff switch lengths in a single statement"),
                primary(first_len, "{} cases", first_len),
                primary(second_len, "{} cases", second_len),
            )));
        }

        if let Some(first_len) = self.first_len {
            if first_len > 8 {
                return Err(emitter.as_sized().emit(error!(
                    message("too many cases in diff switch"),
                    primary(first_len, "{} cases", first_len),
                    note("difficulty masks are only 8 bits wide"),
                )));
            }
        }

        Ok(())
    }
}

// =============================================================================

struct ForbidDifficultyVisitor<'a> {
    errors: ErrorFlag,
    emitter: &'a dyn Emitter,
}

impl Visit for ForbidDifficultyVisitor<'_> {
    fn visit_stmt(&mut self, stmt: &Sp<ast::Stmt>) {
        if let Some(diff_label) = &stmt.diff_label {
            self.errors.set(self.emitter.as_sized().emit(error!(
                message("difficulty is not supported in this format"),
                primary(diff_label, "difficulty label"),
            )));
        }
        ast::walk_stmt(self, stmt);
    }

    fn visit_expr(&mut self, expr: &Sp<ast::Expr>) {
        ast::walk_expr(self, expr);

        if let ast::Expr::DiffSwitch { .. } = expr.value {
            self.errors.set(self.emitter.as_sized().emit(error!(
                message("difficulty is not supported in this format"),
                primary(expr, "difficulty switch"),
            )));
        }
    }
}
