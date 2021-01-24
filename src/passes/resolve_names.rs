use crate::ast;
use crate::pos::Sp;
use crate::type_system::TypeSystem;
use crate::error::CompileError;

/// Resolve names in a script parsed from text, replacing all variables with unique [`crate::var::VarId`]s.
///
/// After calling this, information containing the names and declared types of all variables
/// will be stored on the [`crate::var::Variables`] type.
pub fn run<A: ast::Visitable>(ast: &mut A, ty_ctx: &mut TypeSystem) -> Result<(), CompileError> {
    let mut v = crate::var::ResolveVarsVisitor::new(&mut ty_ctx.variables);
    ast.visit_mut_with(&mut v);
    v.finish()
}

/// Convert [`crate::var::VarId`]s in the AST back into their original identifiers.
///
/// When used on decompiled code from a binary file, this will typically just replace raw register
/// access with their mapfile aliases (e.g. from `[10004]` to `I3`).
///
/// It can also be used on partially-compiled source code, though *this particular usage is only supported
/// strictly for testing and debugging purposes.*  In this case, setting `append_ids` to `true` will rename
/// local variables from `x` to e.g. `x_3` by appending their [`crate::var::LocalId`], enabling them to be
/// differentiated by scope.  Note that compiler-generated temporaries may render as something unusual.
pub fn unresolve<A: ast::Visitable>(ast: &mut A, append_ids: bool, ty_ctx: &TypeSystem) -> Result<(), CompileError> {
    let mut visitor = Unvisitor { ty_ctx, append_ids, errors: CompileError::new_empty() };
    ast.visit_mut_with(&mut visitor);
    visitor.errors.into_result(())
}

// =============================================================================

// Visitor for "unresolving" local variables and recovering their original names.
struct Unvisitor<'ts> {
    ty_ctx: &'ts TypeSystem,
    append_ids: bool,
    errors: CompileError,
}

impl ast::VisitMut for Unvisitor<'_> {
    fn visit_var(&mut self, var: &mut Sp<ast::Var>) {
        if let ast::Var::Resolved { ty_sigil: _, var_id } = var.value {
            // FIXME this seems weird because we ought to just be able to reuse ty_sigil in the output,
            //       but 'var_read_type_from_ast' seems to require a definite type.
            match self.ty_ctx.var_read_type_from_ast(var) {
                Ok(ty) => var.value = self.ty_ctx.var_to_ast(var_id, ty, self.append_ids),
                Err(e) => self.errors.append(e),
            }
        }
    }
}
