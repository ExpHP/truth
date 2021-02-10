use crate::ast;
use crate::pos::Sp;
use crate::type_system::TypeSystem;
use crate::error::CompileError;

/// Resolve names in a script parsed from text, replacing all variables with unique [`crate::var::VarId`]s.
///
/// After calling this, information containing the names and declared types of all variables
/// will be stored on the [`crate::var::Variables`] type.
pub fn run<A: ast::Visitable>(ast: &mut A, ty_ctx: &mut TypeSystem) -> Result<(), CompileError> {
    let mut v = crate::var::ResolveVarsVisitor::new(ty_ctx);
    ast.visit_mut_with(&mut v);
    v.finish()
}

/// Convert any register aliases and instruction aliases to `[10000]` and `ins_32` syntax.
///
/// Requires name resolution to have been performed.
pub fn aliases_to_raw<A: ast::Visitable>(ast: &mut A, ty_ctx: &TypeSystem) -> Result<(), CompileError> {
    let mut v = AliasesToRawVisitor { ty_ctx };
    ast.visit_mut_with(&mut v);
    Ok(())
}

/// Convert any raw register references (e.g. `[10000]`) and raw instructions (`ins_32`) to aliases
/// when they are available.
pub fn raw_to_aliases<A: ast::Visitable>(ast: &mut A, ty_ctx: &TypeSystem) -> Result<(), CompileError> {
    let mut v = RawToAliasesVisitor { ty_ctx };
    ast.visit_mut_with(&mut v);
    Ok(())
}

// =============================================================================

struct AliasesToRawVisitor<'a> {
    ty_ctx: &'a TypeSystem,
}

impl ast::VisitMut for AliasesToRawVisitor<'_> {
    fn visit_var(&mut self, var: &mut Sp<ast::Var>) {
        if let ast::Var::Named { .. } = &var.value {
            if let Ok(reg) = self.ty_ctx.var_reg_from_ast(var) {
                let read_ty = self.ty_ctx.var_read_ty_from_ast(var).expect("shoulda been typechecked!");
                let ty_sigil = read_ty.sigil().expect("regs have numeric types");
                var.value = ast::Var::Reg { reg, ty_sigil };
            }
        }
    }

    fn visit_expr(&mut self, expr: &mut Sp<ast::Expr>) {
        if let ast::Expr::Call { name, .. } = &mut expr.value {
            if let Ok(opcode) = self.ty_ctx.func_opcode_from_ast(name) {
                name.value = ast::CallableName::Ins { opcode };
            }
        }
        ast::walk_expr_mut(self, expr);
    }
}

struct RawToAliasesVisitor<'a> {
    ty_ctx: &'a TypeSystem,
}

impl ast::VisitMut for RawToAliasesVisitor<'_> {
    fn visit_var(&mut self, var: &mut Sp<ast::Var>) {
        if let ast::Var::Reg { ty_sigil, reg } = var.value {
            var.value = self.ty_ctx.reg_to_ast(reg, ty_sigil);
        }
    }

    fn visit_expr(&mut self, expr: &mut Sp<ast::Expr>) {
        if let ast::Expr::Call { name, .. } = &mut expr.value {
            if let ast::CallableName::Ins { opcode, .. } = name.value {
                name.value = self.ty_ctx.ins_to_ast(opcode);
            }
        }
        ast::walk_expr_mut(self, expr);
    }
}
