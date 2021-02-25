use crate::ast;
use crate::pos::Sp;
use crate::type_system::TypeSystem;
use crate::error::CompileError;
use crate::ident::ResIdent;

/// Assign [`ResId`]s to names in a script parsed from text.
///
/// This is an extremely early preprocessing pass, preferably done immediately after parsing.
/// (it can't be done during parsing because parsing should not require access to [`TypeSystem`])
pub fn assign_res_ids<A: ast::Visitable>(ast: &mut A, ty_ctx: &mut TypeSystem) -> Result<(), CompileError> {
    let mut v = AssignResIdsVisitor { ty_ctx };
    ast.visit_mut_with(&mut v);
    Ok(())
}

/// Resolve names in a script parsed from text.
///
/// All [`ResId`]s will be mapped to a unique [`DefId`] during this pass.  These mappings are available
/// through the [`crate::resolve::Resolutions`] type.
///
/// While some definitions are recorded before this (notably eclmap stuff, and things from meta),
/// the majority of definitions are discovered during this pass; this includes user-defined functions,
/// consts, and locals.  All of these will receive [`DefId`]s, and their names and type information
/// will be recorded in [`TypeSystem`].
///
/// **Note:** It is worth noting that that this pass takes `&A`; i.e. it **does not** modify the AST.
/// This means that, if you clone an AST node and then run name resolution on the original, then the
/// names will also be resolved in the copy.  This property is important to helping make some parts
/// of `const` evaluation tractable.  (especially consts defined in meta, like sprite ids)
pub fn run<A: ast::Visitable>(ast: &A, ty_ctx: &mut TypeSystem) -> Result<(), CompileError> {
    let mut v = crate::resolve::ResolveVarsVisitor::new(ty_ctx);
    ast.visit_with(&mut v);
    v.finish()
}

/// Convert any register aliases and instruction aliases to `REG[10000]` and `ins_32` syntax.
///
/// Requires name resolution to have been performed.
pub fn aliases_to_raw<A: ast::Visitable>(ast: &mut A, ty_ctx: &TypeSystem) -> Result<(), CompileError> {
    let mut v = AliasesToRawVisitor { ty_ctx };
    ast.visit_mut_with(&mut v);
    Ok(())
}

/// Convert any raw register references (e.g. `REG[10000]`) and raw instructions (`ins_32`) to aliases
/// when they are available.
///
/// When it converts a register to an alias, it will strip the type sigil if it isn't needed.
/// (sigils are left on registers it doesn't convert
///
/// FIXME: Stripping the sigil seems like a surprising side-effect.
///  Or rather, while it's true that we DO want redundant sigils on REG and not on other things,
///  this particular function is an odd place to implement this behavior!
///  (it's only here for historical reasons, back when raw registers always had a `VarReadType`)
///  &nbsp;
///  I did try separating this into two passes (one that switches to aliases, another that strips sigils
///  from non-`REG`s) but ran into https://github.com/ExpHP/truth/issues/13 when the second pass
///  encountered things like `sprite24`.
pub fn raw_to_aliases<A: ast::Visitable>(ast: &mut A, ty_ctx: &TypeSystem) -> Result<(), CompileError> {
    let mut v = RawToAliasesVisitor { ty_ctx };
    ast.visit_mut_with(&mut v);
    Ok(())
}

// =============================================================================

struct AssignResIdsVisitor<'a> {
    ty_ctx: &'a mut TypeSystem,
}

impl ast::VisitMut for AssignResIdsVisitor<'_> {
    fn visit_res_ident(&mut self, ident: &mut ResIdent) {
        ident.res.get_or_insert_with(|| self.ty_ctx.resolutions.fresh_res());
    }
}

struct AliasesToRawVisitor<'a> {
    ty_ctx: &'a TypeSystem,
}

impl ast::VisitMut for AliasesToRawVisitor<'_> {
    fn visit_var(&mut self, var: &mut Sp<ast::Var>) {
        if let ast::VarName::Normal { .. } = &var.name {
            if let Ok(reg) = self.ty_ctx.var_reg_from_ast(&var.name) {
                var.name = reg.into();
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
        if let ast::VarName::Reg { reg } = var.name {
            var.name = self.ty_ctx.reg_to_ast(reg);

            // did it succeed?
            if var.name.is_named() {
                self.ty_ctx.var_simplify_ty_sigil(&mut var.value);
            }
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
