use std::fmt;
use std::num::NonZeroUsize;
use std::collections::HashMap;
use crate::ident::Ident;
use crate::type_system::ScalarType;

/// Uniquely identifies a variable (which may be a local or a register).
///
/// You can get information about the variable from [`TypeSystem`](crate::type_system::TypeSystem).
///
/// This is the preferred over [`Ident`]s as it accounts for scope. (i.e. two variables with the
/// same name can have different [`VarId`]s).   To obtain these from a parsed script, see
/// [`TypeSystem::resolve_names`](crate::type_system::TypeSystem::resolve_names)
/// which replaces all [`Ident`]-based variables with [`VarId`]s.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VarId {
    /// A global register.  Use [`crate::type_system::RegsAndInstrs`] to obtain more information about it.
    Reg(i32),
    /// A local variable, uniquely resolved by its scope.
    Local(LocalId),
}

impl From<LocalId> for VarId {
    fn from(x: LocalId) -> Self { VarId::Local(x) }
}

/// Uniquely identifies a scoped local variable.
///
/// Information about the variable like its name and type can be retrieved from [`Variables`].
///
/// Technically, all named variables have [`LocalId`]s; this includes global aliases of registers,
/// but those [`LocalId`]s will never be seen in the AST, as they will always be resolved to
/// [`VarId::Reg`] instead.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocalId(NonZeroUsize);

/// Identifies a scope in which a set of names are visible.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Default)]
struct ScopeId(
    // we define a new scope for every variable.  None is the empty scope.
    Option<LocalId>,
);

/// Scope containing no variables.
const EMPTY_SCOPE: ScopeId = ScopeId(None);

/// Provides data for all [`VarId`]s in the script being compiled.
#[derive(Debug, Clone)]
pub struct Variables {
    scopes: Vec<Scope>,
    /// Scope of toplevel code, containing all globals.
    root_scope: ScopeId,
    has_declared_locals: bool,
}

#[derive(Debug, Clone)]
struct Scope {
    /// Name of the variable defined in this scope.
    ident: Ident,
    /// Type of the variable defined in this scope, if fixed.
    ty: Option<ScalarType>,
    /// If the variable is a register alias (i.e. from a mapfile), the register it references.
    reg: Option<i32>,
    /// Scope where the rest of the visible variables are defined.
    parent: ScopeId,
}

impl Default for Variables {
    fn default() -> Self { Self::new() }
}

impl Variables {
    /// Create one with no variables defined.
    pub fn new() -> Self {
        // a dummy that is never used for anything because we number variables starting from 1.
        // (so that zero can refer to the scope with no variables)
        let dummy_scope = Scope {
            ident: "!!_DUMMY_IDENT_!!".parse().unwrap(),
            ty: None,
            reg: None,
            parent: EMPTY_SCOPE,
        };
        Variables {
            scopes: vec![dummy_scope],
            root_scope: EMPTY_SCOPE,
            has_declared_locals: false,
        }
    }

    pub fn get_name(&self, id: LocalId) -> &Ident { &self.scopes[id.0.get()].ident }
    pub fn get_type(&self, id: LocalId) -> Option<ScalarType> { self.scopes[id.0.get()].ty }

    fn get_parent_scope(&self, id: LocalId) -> ScopeId { self.scopes[id.0.get()].parent }
    fn get_scope(&self, id: LocalId) -> ScopeId { ScopeId(Some(id)) }

    /// Get the register mapped to this variable, if it is a register alias from a mapfile.
    ///
    /// IMPORTANT:  In some formats like ANM and old ECL, local variables are also ultimately
    /// allocated to registers, but that is unrelated to this and this function will return `None`
    /// for them.
    fn get_mapped_register(&self, id: LocalId) -> Option<i32> { self.scopes[id.0.get()].reg }

    /// Declare a new local variable with a unique [`LocalId`].
    pub fn declare_temporary(&mut self, ty: Option<ScalarType>) -> LocalId {
        self.has_declared_locals = true;

        // This function is only used by code outside this module, after name resolution has already been performed.
        // Hence, scope is no longer important for any purpose, and we can use anything.
        self.declare(EMPTY_SCOPE, "_tmp".parse().unwrap(), ty)
    }

    /// Declares a variable.  This will create a new scope, which will be a child of the given scope.
    fn declare(&mut self, parent: ScopeId, ident: Ident, ty: Option<ScalarType>) -> LocalId {

        let id = LocalId(NonZeroUsize::new(self.scopes.len()).unwrap());
        self.scopes.push(Scope { ident, ty, parent, reg: None });
        id
    }

    /// Declares a global variable as an alias for a register, adding it to the global scope for future name resolution.
    pub fn declare_global_register_alias(&mut self, ident: Ident, reg: i32) {
        // NOTE: This panic is here because, under the current design, declaring globals after declaring locals could
        //       have a weird effect that all of the previously declared locals will still be using the scope without
        //       the new globals.
        //       (more importantly, it means that those variables were resolved without these globals in scope!)
        //
        //       Generally speaking, the design of truth is supposed to be such that global things are declarative
        //       and allowed to be written in any order.  So if something triggers this error, it probably goes counter
        //       to this principle and should be reconsidered thoughtfully.
        assert!(!self.has_declared_locals, "called declare_register_alias after calling declare_temporary!");

        // NOTE: we *could* store types from mapfiles here, but we don't because anything using `Self::get_type` on
        //       the LocalId for a register is almost certainly bugged, and doing this would just mask that bug.
        let ty = None;
        let id = self.declare(self.root_scope, ident, ty);
        self.scopes[id.0.get()].reg = Some(reg);

        self.root_scope = self.get_scope(id);
    }
}

use name_resolver::NameResolver;
mod name_resolver {
    use super::*;

    /// A helper for resolving identifiers into [`VarId`s](VarId) based on scope.
    #[derive(Debug, Clone)]
    pub(super) struct NameResolver {
        current_scope: ScopeId,

        /// Variables that have each name. The last id in each vec is the active variable
        /// with that name; any earlier ones are shadowed.
        active_vars: HashMap<Ident, Vec<LocalId>>,
    }

    impl NameResolver {
        /// Create a new [`NameResolver`] sitting in the empty scope.
        pub fn new() -> Self {
            NameResolver { current_scope: EMPTY_SCOPE, active_vars: Default::default() }
        }

        /// Get the scope at which this [`NameResolver`] is currently resolving names.
        pub fn current_scope(&self) -> ScopeId { self.current_scope }

        /// Resolve an identifier at the current scope.
        pub fn resolve(&self, ident: &Ident, variables: &Variables) -> Option<VarId> {
            self.active_vars.get(ident)
                .and_then(|vec| vec.last().copied())  // the one that isn't shadowed
                .map(|var_id| match variables.get_mapped_register(var_id) {
                    Some(reg) => VarId::Reg(reg),  // always emit Reg for register aliases
                    None => VarId::Local(var_id),
                })
        }

        /// Travel from the current scope into one that is lower down the tree.
        ///
        /// (note: the case where `current_scope == descendant` will trivially succeed)
        pub fn enter_descendant(&mut self, descendant: ScopeId, variables: &Variables) {
            let mut vars_to_add = vec![];

            // travel from descendant back up to current position to gather tree edges in reverse
            let mut scope_iter = descendant;
            while self.current_scope != scope_iter {
                if let ScopeId(Some(var_id)) = scope_iter {
                    let name = variables.get_name(var_id);
                    vars_to_add.push((name, var_id));
                    scope_iter = variables.get_parent_scope(var_id);
                } else {
                    panic!("scope was not a descendant!");
                }
            }

            self.current_scope = descendant;

            for (name, var_id) in vars_to_add.into_iter().rev() {
                self.active_vars.entry(name.clone()).or_default().push(var_id);
            }
        }

        /// Travel from the current scope into one that is anywhere above it in the tree.
        ///
        /// (note: the case where `current_scope == ancestor` will trivially succeed)
        pub fn return_to_ancestor(&mut self, ancestor: ScopeId, variables: &Variables) {
            while self.current_scope != ancestor {
                // Travel up the tree, deleting one variable from `active_vars` at a time.
                if let ScopeId(Some(var_id)) = self.current_scope {
                    let name = variables.get_name(var_id);
                    let popped_var_id = self.active_vars.get_mut(name).unwrap().pop().unwrap();
                    assert_eq!(var_id, popped_var_id);

                    self.current_scope = variables.get_parent_scope(var_id);
                } else {
                    // we reached the root scope and never found our ancestor
                    panic!("scope was not an ancestor!");
                }
            }
        }
    }
}

pub use resolve_vars::Visitor as ResolveVarsVisitor;
mod resolve_vars {
    use super::*;
    use crate::ast::{self, VisitMut};
    use crate::pos::Sp;
    use crate::error::CompileError;

    /// Visitor for name resolution. Please don't use this directly, but instead call [`crate::type_system::TypeSystem::resolve_names`].
    pub struct Visitor<'ts> {
        resolver: NameResolver,
        stack: Vec<BlockState>,
        variables: &'ts mut Variables,
        errors: CompileError,
    }

    pub struct BlockState {
        outer_scope: ScopeId,
        locals_declared_at_this_level: Vec<LocalId>,
    }

    impl<'ts> Visitor<'ts> {
        pub fn new(variables: &'ts mut Variables) -> Self {
            let mut resolver = NameResolver::new();
            resolver.enter_descendant(variables.root_scope, variables);
            Visitor {
                resolver, variables,
                stack: vec![],
                errors: CompileError::new_empty(),
            }
        }

        pub fn finish(self) -> Result<(), CompileError> {
            self.errors.into_result(())
        }
    }

    impl VisitMut for Visitor<'_> {
        fn visit_block(&mut self, x: &mut ast::Block) {
            self.stack.push(BlockState {
                outer_scope: self.resolver.current_scope(),
                locals_declared_at_this_level: vec![],
            });

            ast::walk_mut_block(self, x);

            let popped = self.stack.pop().expect("(BUG!) unbalanced scope_stack usage!");

            for local_id in popped.locals_declared_at_this_level {
                let span = x.last_stmt().span.end_span();
                x.0.push(sp!(span => ast::Stmt {
                    time: x.end_time(), labels: vec![],
                    body: sp!(span => ast::StmtBody::ScopeEnd(local_id)),
                }))
            }

            self.resolver.return_to_ancestor(popped.outer_scope, &self.variables);
        }

        fn visit_stmt_body(&mut self, x: &mut Sp<ast::StmtBody>) {
            match &mut x.value {
                ast::StmtBody::Declaration { keyword, vars } => {
                    let ty = match keyword.value {
                        ast::VarDeclKeyword::Int => Some(ScalarType::Int),
                        ast::VarDeclKeyword::Float => Some(ScalarType::Float),
                        ast::VarDeclKeyword::Var => None,
                    };

                    for pair in vars {
                        let (var, init_value) = &mut pair.value;
                        if let ast::Var::Named { ty_sigil, ident } = &var.value {
                            assert!(ty_sigil.is_none());

                            // a variable should not be allowed to appear in its own initializer, so walk the expression first.
                            if let Some(init_value) = init_value {
                                self.visit_expr(init_value);
                            }

                            // now declare the variable and enter its scope so that it can be used in future expressions
                            let local_id = self.variables.declare(self.resolver.current_scope(), ident.clone(), ty);
                            self.resolver.enter_descendant(self.variables.get_scope(local_id), &self.variables);

                            self.stack.last_mut().expect("(bug?) empty stack?")
                                .locals_declared_at_this_level.push(local_id);

                            // swap out the AST node
                            let var_id = VarId::Local(local_id);
                            var.value = ast::Var::Resolved { ty_sigil: None, var_id };
                        }
                    }
                }
                _ => ast::walk_mut_stmt_body(self, x),
            }
        }

        fn visit_var(&mut self, var: &mut Sp<ast::Var>) {
            if let ast::Var::Named { ty_sigil, ref ident } = var.value {
                match self.resolver.resolve(ident, &self.variables) {
                    Some(var_id) => var.value = ast::Var::Resolved { ty_sigil, var_id },
                    None => self.errors.append(error!(
                        message("no such variable {}", ident),
                        primary(var, "not found in this scope"),
                    )),
                };
            }
        }
    }
}

impl fmt::Display for LocalId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl fmt::Display for ScopeId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0.map(|x| x.0.get()).unwrap_or(0), f)
    }
}

impl fmt::Debug for LocalId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Debug for ScopeId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pos::Files;
    use crate::error::CompileError;
    use crate::eclmap::Eclmap;
    use crate::type_system::TypeSystem;
    use crate::ast;

    const ECLMAP: &'static str = r#"!eclmap
!gvar_names
100 A
101 X
!gvar_types
100 $
101 %
"#;

    fn resolve(text: &str) -> Result<(TypeSystem, ast::Block), (Files, CompileError)> {
        let mut files = Files::new();
        let mut ty_ctx = TypeSystem::new();
        ty_ctx.extend_from_eclmap("<mapfile>".as_ref(), &Eclmap::parse(ECLMAP).unwrap());

        let mut parsed_block = files.parse::<ast::Block>("<input>", text.as_ref()).unwrap().value;
        match ty_ctx.resolve_names_block(&mut parsed_block) {
            Ok(()) => Ok((ty_ctx, parsed_block)),
            Err(e) => Err((files, e)),
        }
    }

    fn resolve_reformat(text: &str) -> String {
        let (mut ty_ctx, mut parsed_block) = resolve(text).unwrap();
        ty_ctx.unresolve_names_block(&mut parsed_block, true).unwrap();
        crate::fmt::stringify(&parsed_block)
    }

    fn resolve_expect_err(text: &str) -> String {
        let (files, err) = resolve(text).unwrap_err();
        err.to_string(&files).unwrap()
    }

    macro_rules! snapshot_test {
        ($name:ident = $source:literal) => {
            #[test]
            fn $name() { assert_snapshot!(resolve_reformat($source).trim()); }
        };
        ([expect_fail] $name:ident = $source:literal) => {
            #[test]
            fn $name() { assert_snapshot!(resolve_expect_err($source).trim()); }
        };
    }

    snapshot_test!(basic_local = r#"{
        int a = 3;
        int b = a + a;
    }"#);

    snapshot_test!(shadow_local = r#"{
        int a = 3;
        if (true) {
            int a = 4;
            int b = a * a;
        }
        int c = a * a;
        if (true) {
            int a = 4;
            int b = a * a;
        }
    }"#);

    snapshot_test!([expect_fail] err_adjacent_scope = r#"{
        if (true) {
            int a = 4;
            int b = a * 3;
        }
        if (true) {
            int b = a * 3;
        }
    }"#);

    snapshot_test!([expect_fail] err_after_scope_end = r#"{
        if (true) {
            int a = 4;
            int b = a * 3;
        }
        int b = a;
    }"#);

    snapshot_test!(basic_global = r#"{
        ins_21(A, X);
    }"#);

    snapshot_test!(shadow_global = r#"{
        ins_21(A, X);
        if (true) {
            float A = 4.0;
            float b = A;
        }
        ins_21(A, X);
    }"#);

    #[test]
    fn basic_global_was_really_resolved() {
        // since globals may not look different after resolving and unresolving,
        // we need to do a little extra sleuthing to make sure the visitor did its job.
        let (_ty_ctx, block) = resolve(r#"{
        ins_21(A, X);
    }"#).unwrap();
        let expr = block.0.iter().find_map(|stmt| match &stmt.body.value {
            ast::StmtBody::Expr(e) => Some(e),
            _ => None,
        }).unwrap();

        match &expr.value {
            ast::Expr::Call { args, .. } => {
                assert!(
                    matches!(args[0].value, ast::Expr::Var(sp_pat!(ast::Var::Resolved { var_id: VarId::Reg(100), .. }))),
                    "{:?}", args[0],
                );
            },
            _ => panic!(),
        }
    }
}
