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

/// Convert any register aliases to raw register reference syntax.
///
/// Requires name resolution to have been performed.
pub fn aliases_to_regs<A: ast::Visitable>(ast: &mut A, ty_ctx: &TypeSystem) -> Result<(), CompileError> {
    let mut v = AliasesToRegsVisitor { ty_ctx };
    ast.visit_mut_with(&mut v);
    Ok(())
}

/// Convert raw register references to aliases when they are available.
pub fn regs_to_aliases<A: ast::Visitable>(ast: &mut A, ty_ctx: &TypeSystem) -> Result<(), CompileError> {
    let mut v = RegsToAliasesVisitor { ty_ctx };
    ast.visit_mut_with(&mut v);
    Ok(())
}

// =============================================================================

struct AliasesToRegsVisitor<'a> {
    ty_ctx: &'a TypeSystem,
}

impl ast::VisitMut for AliasesToRegsVisitor<'_> {
    fn visit_var(&mut self, var: &mut Sp<ast::Var>) {
        if let ast::Var::Named { .. } = &var.value {
            if let Ok(reg) = self.ty_ctx.var_reg_from_ast(var) {
                let read_ty = self.ty_ctx.var_read_ty_from_ast(var).expect("shoulda been typechecked!");
                let ty_sigil = read_ty.sigil().expect("regs have numeric types");
                var.value = ast::Var::Reg { reg, ty_sigil };
            }
        }
    }
}

struct RegsToAliasesVisitor<'a> {
    ty_ctx: &'a TypeSystem,
}

impl ast::VisitMut for RegsToAliasesVisitor<'_> {
    fn visit_var(&mut self, var: &mut Sp<ast::Var>) {
        if let ast::Var::Reg { ty_sigil, reg } = var.value {
            var.value = self.ty_ctx.reg_to_ast(reg, ty_sigil);
        }
    }
}
