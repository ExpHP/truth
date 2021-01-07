use crate::ast::{self, Visit, VisitMut};
use crate::error::CompileError;
use crate::pos::Sp;
use crate::scope::{ScopeId, VarId, Variables, NameResolver, EMPTY_SCOPE};
use crate::type_system::{self, TypeSystem, ScalarType};

pub struct Visitor<'ts> {
    resolver: NameResolver,
    scope_stack: Vec<ScopeId>,
    ty_ctx: &'ts mut TypeSystem,
    variables: Variables,
    errors: CompileError,
}

impl<'ts> Visitor<'ts> {
    pub fn new(ty_ctx: &'ts mut TypeSystem) -> Self {
        assert!(ty_ctx.variables.is_none()); // not designed for multiple usages on the same TypeSystem

        let (variables, root_scope) = initial_variables(&ty_ctx.regs_and_instrs);
        let mut resolver = NameResolver::new();
        resolver.enter_descendant(root_scope, &variables);
        Visitor {
            resolver, variables, ty_ctx,
            scope_stack: vec![],
            errors: CompileError::new_empty(),
        }
    }

    pub fn finish(self) -> Result<(), CompileError> {
        let Visitor { errors, ty_ctx, variables, .. } = self;
        errors.into_result_with(|| {
            ty_ctx.variables = Some(variables);
        })
    }
}

impl VisitMut for Visitor<'_> {
    fn visit_block(&mut self, x: &mut ast::Block) {
        self.scope_stack.push(self.resolver.current_scope());

        ast::walk_mut_block(self, x);

        let original = self.scope_stack.pop().expect("(BUG!) unbalanced scope_stack usage!");
        self.resolver.return_to_ancestor(original, &self.variables);
    }

    fn visit_stmt_body(&mut self, x: &mut Sp<ast::StmtBody>) {
        match &mut x.value {
            ast::StmtBody::Declaration { keyword, vars } => {
                let ty = match keyword {
                    ast::VarDeclKeyword::Int => Some(ScalarType::Int),
                    ast::VarDeclKeyword::Float => Some(ScalarType::Float),
                    ast::VarDeclKeyword::Var => None,
                };

                for (var, init_value) in vars {
                    if let ast::Var::Named { ty_sigil, ident } = &var.value {
                        assert!(ty_sigil.is_none());

                        // a variable should not be allowed to appear in its own initializer, so walk the expression first.
                        if let Some(init_value) = init_value {
                            self.visit_expr(init_value);
                        }

                        // now declare the variable and enter its scope so that it can be used in future expressions
                        let var_id = self.variables.declare(self.resolver.current_scope(), ident.clone(), ty);
                        self.resolver.enter_descendant(self.variables.get_scope(var_id), &self.variables);

                        // swap out the AST node
                        var.value = ast::Var::Local { ty_sigil: None, var_id };
                    }
                }
            }
            _ => ast::walk_mut_stmt_body(self, x),
        }
    }

    fn visit_var(&mut self, var: &mut Sp<ast::Var>) {
        if let ast::Var::Named { ty_sigil, ref ident } = var.value {
            match self.resolver.resolve(ident) {
                Some(var_id) => {
                    var.value = ast::Var::Local { ty_sigil, var_id };
                },
                None => self.errors.append(error!(
                    message("no such variable {}", ident),
                    primary(var, "not found in this scope"),
                )),
            };
        }
    }
}

/// Given a [`TypeSystem`] that only contains register aliases from mapfiles, create a [`Variables`]
/// with these names and get the scope containing all of the variables.
fn initial_variables(initial_ty_ctx: &type_system::RegsAndInstrs) -> (Variables, ScopeId) {
    let mut variables = Variables::new();
    let mut scope = EMPTY_SCOPE;
    for (alias, &raw_id) in &initial_ty_ctx.reg_map {
        let ty = initial_ty_ctx.reg_default_types.get(&raw_id).copied();
        let new_var_id = variables.declare(scope, alias.clone(), ty);
        scope = variables.get_scope(new_var_id);
    }
    (variables, scope)
}

// --------------------------------------------

/// Visitor for "unresolving" local variables and recovering their original names.
pub struct Unvisitor<'ts> {
    variables: &'ts Variables,
    append_ids: bool,
}

impl<'ts> Unvisitor<'ts> {
    pub fn new(ty_ctx: &'ts TypeSystem, append_ids: bool) -> Self {
        let variables = ty_ctx.variables.as_ref().expect("unresolving vars without having resolved them?!");
        Unvisitor { variables, append_ids }
    }
}

impl VisitMut for Unvisitor<'_> {
    fn visit_var(&mut self, var: &mut Sp<ast::Var>) {
        if let ast::Var::Local { ty_sigil, var_id } = var.value {
            let ident = self.variables.get_name(var_id);
            let ident = match self.append_ids {
                true => format!("{}_{}", ident, var_id),
                false => format!("{}", ident),
            }.parse().unwrap();

            var.value = ast::Var::Named { ident, ty_sigil };
        }
    }
}

// --------------------------------------------

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::fmt::Formatter;
//
//     const SIMPLE_MAPFILE: &'static str = "\
//         !anmmap\n\
//         !gvar_names\n0 A\n1 B\n2 C\n3 D\n4 X\n5 Y\n6 Z\n7 W\n\
//         !gvar_types\n0 $\n1 $\n2 $\n3 $\n4 %\n5 %\n6 %\n7 %\n";
//
//     fn mess_with(text: &str) -> String {
//         let eclmap = crate::eclmap::Eclmap::parse(SIMPLE_MAPFILE).unwrap();
//         let mut ty_ctx = crate::type_system::TypeSystem::new();
//         ty_ctx.extend_from_eclmap("DUMMY.anmmap".as_ref(), &eclmap);
//
//         let mut f = Formatter::new(vec![]).with_max_columns(99999);
//         let mut files = crate::pos::Files::new();
//         let mut script = files.parse::<ast::Script>("<input>", text.as_bytes()).unwrap_or_else(|e| panic!("{}", e));
//
//         let mut visitor = Visitor::new(&mut ty_ctx);
//         ast::walk_mut_script(&mut visitor, &mut script);
//         visitor.finish().unwrap();
//
//         let mut visitor = Unvisitor::new(&ty_ctx, true);
//         ast::walk_mut_script(&mut visitor, &mut script);
//
//         f.fmt(&script).unwrap();
//         String::from_utf8(f.into_inner().unwrap()).unwrap()
//     }
//
//     #[test]
//     fn lol() {
//         assert_snapshot!("halp", mess_with(r#"
// void main() {
//     int x = 3 + 2;
//     int y = x;
//     int x = 3*A;
//     if (true) {
//         int x = 2;
//         x;
//     }
//     x;
// }
// "#).trim());
//     }
//
// }
