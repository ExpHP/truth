use std::fmt;
use std::num::NonZeroUsize;
use std::collections::HashMap;
use crate::ident::{Ident, ResolveId};
use crate::type_system::{ScalarType, TypeSystem};

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
    Reg(RegId),
    /// A local variable.  The [`ResolveId`] always corresponds to a local. ([`TypeSystem::add_local`])
    Local(ResolveId),
}

impl From<RegId> for VarId {
    fn from(x: RegId) -> Self { VarId::Reg(x) }
}

/// The number used to access a register as an instruction argument.  This uniquely identifies a register.
///
/// For instance, in TH17 ECL, the `TIME` register has an id of `-9988`.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RegId(pub i32);

impl From<i32> for RegId {
    fn from(x: i32) -> Self { RegId(x) }
}

/// Uniquely identifies a scoped local variable.
///
/// Information about the variable like its name and type can be retrieved from [`TypeSystem`].
///
/// Technically, all named variables have [`LocalId`]s; this includes global aliases of registers,
/// but those [`LocalId`]s will never be seen in the AST, as they will always be resolved to
/// [`VarId::Reg`] instead.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct LocalId(NonZeroUsize);

/// Identifies a scope in which a set of names are visible.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Default)]
struct ScopeId(
    // we define a new scope for every variable.  None is the empty scope.
    Option<LocalId>,
);

/// Scope containing no variables.
const EMPTY_SCOPE: ScopeId = ScopeId(None);

use scope_tree::ScopeTree;
mod scope_tree {
    use super::*;

    // NOTE: Do we really need a tree structure, or would a simple stack suffice ()?
    //        I.e. could we get away with adding the following to NameResolver:
    //             names_in_scope: Vec<ResolveId>,
    //             block_scope_indices: Vec<usize>,
    //        As long as that will still work for other namespaces and globals, we should use that.
    //
    /// A treelike structure describing the relationships between all scopes during name resolution.
    ///
    /// The root node of the tree is the scope with no names.  Then, each new name definition creates a
    /// new child scope based off an existing scope.  During name resolution, [`NameResolver`] travels
    /// up and down this tree in order to learn which definitions are entering or leaving scope at any
    /// given time.
    ///
    /// # Note on necessity (FIXME: Remove once irrelevant)
    ///
    /// One might wonder, since the only operations we use seem to be descending to a brand new
    /// child or ascending to an arbitrary ancestor, why not just add the following fields to [`NameResolver`]?:
    ///
    /// ```text
    ///     names_in_scope: Vec<ResolveId>,
    ///     block_scope_indices: Vec<usize>,  // indices to truncate names_in_scope to on block exit
    /// ```
    ///
    /// Indeed, we probably could.  The reason we haven't YET is partly laziness (the tree is how it was
    /// originally implemented), and partly that I'm not yet convinced that we won't need the tree
    /// structure in the near future. (e.g. for inline functions maybe?)
    #[derive(Debug, Clone)]
    pub(super) struct ScopeTree {
        scopes: Vec<Scope>,
        /// Scope containing all global names.
        global_scope: ScopeId,
    }

    #[derive(Debug, Clone)]
    struct Scope {
        /// Id in [`TypeSystem`] of the name introduced by this scope.
        ///
        /// `None` for the empty scope.
        res: Option<ResolveId>,
        /// Scope where the rest of the visible variables are defined.
        parent: ScopeId,
    }

    impl ScopeTree {
        /// Create one with all names from the global scope.
        ///
        /// (the initial shape of the tree will be a string of nodes each with one child, ending at the
        ///  node containing all global names)
        pub(super) fn from_ty_ctx(ty_ctx: &TypeSystem) -> Self {
            // a dummy that is never used for anything because we number variables starting from 1.
            // (so that zero can refer to the scope with no variables)
            let dummy_scope = Scope {
                res: None,
                parent: EMPTY_SCOPE,
            };
            let mut scopes = vec![dummy_scope];
            let mut global_scope = EMPTY_SCOPE;
            for res in ty_ctx.globals() {
                scopes.push(Scope { res: Some(res), parent: global_scope });
                global_scope = ScopeId(NonZeroUsize::new(scopes.len() - 1).map(LocalId));
            }
            ScopeTree { scopes, global_scope }
        }

        pub(super) fn get_global_scope(&self) -> ScopeId { self.global_scope }

        pub(super) fn get_res(&self, local_id: LocalId) -> ResolveId {
            self.scopes[local_id.0.get()].res.expect("only None for dummy scope")
        }

        pub(super) fn get_parent_scope(&self, local_id: LocalId) -> ScopeId { self.scopes[local_id.0.get()].parent }
        pub(super) fn get_scope(&self, local_id: LocalId) -> ScopeId { ScopeId(Some(local_id)) }

        /// Declares a variable.  This will create a new scope, which will be a child of the given scope.
        pub(super) fn insert_child(&mut self, parent: ScopeId, res: ResolveId) -> LocalId {
            let local_id = LocalId(NonZeroUsize::new(self.scopes.len()).unwrap());
            self.scopes.push(Scope { res: Some(res), parent });
            local_id
        }
    }
}

use name_resolver::NameResolver;
mod name_resolver {
    use super::*;

    /// A helper for resolving identifiers into [`VarId`s][`VarId`] based on scope.
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

        // FIXME FIXME FIXME FIXME     I want to get rid of VarId, but there is a reason that this function
        // FIXME FIXME FIXME FIXME     always resolves aliases to RegIds. (stackless lowerer requires it)
        // FIXME FIXME FIXME FIXME
        // FIXME FIXME FIXME FIXME     However, we should be able to do that in the lowerer instead, and
        // FIXME FIXME FIXME FIXME     keep the ResolveId for the alias here.
        //
        /// Resolve an identifier at the current scope.
        pub fn resolve(&self, ident: &Ident, variables: &ScopeTree, ty_ctx: &TypeSystem) -> Option<VarId> {
            self.active_vars.get(ident)
                .and_then(|vec| vec.last().copied())  // the one that isn't shadowed
                .map(|local_id| {
                    let res = variables.get_res(local_id);
                    match ty_ctx.var_reg(res) {
                        Some(reg) => VarId::Reg(reg),  // always emit Reg for register aliases
                        None => VarId::Local(res),
                    }
                })
        }

        /// Travel from the current scope into one that is lower down the tree.
        ///
        /// (note: the case where `current_scope == descendant` will trivially succeed)
        pub fn enter_descendant(&mut self, descendant: ScopeId, variables: &ScopeTree, ty_ctx: &TypeSystem) {
            let mut vars_to_add = vec![];

            // travel from descendant back up to current position to gather tree edges in reverse
            let mut scope_iter = descendant;
            while self.current_scope != scope_iter {
                if let ScopeId(Some(local_id)) = scope_iter {
                    let res = variables.get_res(local_id);
                    if let Some(ident) = ty_ctx.var_resolvable_ident(res) {
                        vars_to_add.push((ident, local_id));
                        scope_iter = variables.get_parent_scope(local_id);
                    }
                } else {
                    panic!("scope was not a descendant!");
                }
            }

            self.current_scope = descendant;

            for (ident, local_id) in vars_to_add.into_iter().rev() {
                self.active_vars.entry(ident.clone()).or_default().push(local_id);
            }
        }

        /// Travel from the current scope into one that is anywhere above it in the tree.
        ///
        /// (note: the case where `current_scope == ancestor` will trivially succeed)
        pub fn return_to_ancestor(&mut self, ancestor: ScopeId, variables: &ScopeTree, ty_ctx: &TypeSystem) {
            while self.current_scope != ancestor {
                // Travel up the tree, deleting one variable from `active_vars` at a time.
                if let ScopeId(Some(local_id)) = self.current_scope {
                    let res = variables.get_res(local_id);
                    if let Some(ident) = ty_ctx.var_resolvable_ident(res) {
                        let popped_local_id = self.active_vars.get_mut(ident).unwrap().pop().unwrap();
                        assert_eq!(local_id, popped_local_id);
                    }

                    self.current_scope = variables.get_parent_scope(local_id);
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

    /// Visitor for name resolution. Please don't use this directly,
    /// but instead call [`crate::passes::resolve_names::run`].
    pub struct Visitor<'ts> {
        resolver: NameResolver,
        variables: ScopeTree,
        stack: Vec<BlockState>,
        errors: CompileError,
        ty_ctx: &'ts mut TypeSystem,
    }

    pub struct BlockState {
        outer_scope: ScopeId,
        locals_declared_at_this_level: Vec<LocalId>,
    }

    impl<'ts> Visitor<'ts> {
        pub fn new(ty_ctx: &'ts mut TypeSystem) -> Self {
            let mut resolver = NameResolver::new();
            let variables = ScopeTree::from_ty_ctx(ty_ctx);
            resolver.enter_descendant(variables.get_global_scope(), &variables, ty_ctx);
            Visitor {
                resolver,
                variables,
                stack: vec![],
                errors: CompileError::new_empty(),
                ty_ctx,
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

            ast::walk_block_mut(self, x);

            let popped = self.stack.pop().expect("(BUG!) unbalanced scope_stack usage!");

            for local_id in popped.locals_declared_at_this_level {
                let res = self.variables.get_res(local_id);
                let span = x.last_stmt().span.end_span();
                x.0.push(sp!(span => ast::Stmt {
                    time: x.end_time(),
                    body: ast::StmtBody::ScopeEnd(res),
                }));
            }

            self.resolver.return_to_ancestor(popped.outer_scope, &self.variables, self.ty_ctx);
        }

        fn visit_stmt(&mut self, x: &mut Sp<ast::Stmt>) {
            match &mut x.body {
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

                            let ident = self.ty_ctx.add_local(sp!(var.span => ident.clone()), ty);

                            // now declare the variable and enter its scope so that it can be used in future expressions
                            let local_id = self.variables.insert_child(self.resolver.current_scope(), ident.expect_res());
                            self.resolver.enter_descendant(self.variables.get_scope(local_id), &self.variables, self.ty_ctx);

                            self.stack.last_mut().expect("(bug?) empty stack?")
                                .locals_declared_at_this_level.push(local_id);

                            // swap out the AST node
                            let var_id = VarId::Local(ident.expect_res());  // FIXME XXX  redo VarId
                            var.value = ast::Var::Resolved { ty_sigil: None, var_id };
                        }
                    }
                }
                _ => ast::walk_stmt_mut(self, x),
            }
        }

        fn visit_var(&mut self, var: &mut Sp<ast::Var>) {
            if let ast::Var::Named { ty_sigil, ref ident } = var.value {
                match self.resolver.resolve(ident, &self.variables, self.ty_ctx) {
                    Some(var_id) => var.value = ast::Var::Resolved { ty_sigil, var_id },
                    None => self.errors.append(error!(
                        message("unknown variable '{}'", ident),
                        primary(var, "not found in this scope"),
                    )),
                };
            }
        }
    }
}

impl fmt::Display for RegId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
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

impl fmt::Debug for RegId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
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
        ty_ctx.extend_from_eclmap(None, &Eclmap::parse(ECLMAP).unwrap()).unwrap();

        let mut parsed_block = files.parse::<ast::Block>("<input>", text.as_ref()).unwrap().value;
        match crate::passes::resolve_names::run(&mut parsed_block, &mut ty_ctx) {
            Ok(()) => Ok((ty_ctx, parsed_block)),
            Err(e) => Err((files, e)),
        }
    }

    fn resolve_reformat(text: &str) -> String {
        let (ty_ctx, mut parsed_block) = resolve(text).unwrap();
        crate::passes::resolve_names::unresolve(&mut parsed_block, true, &ty_ctx).unwrap();
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
        let expr = block.0.iter().find_map(|stmt| match &stmt.body {
            ast::StmtBody::Expr(e) => Some(e),
            _ => None,
        }).unwrap();

        match &expr.value {
            ast::Expr::Call { args, .. } => {
                assert!(
                    matches!(args[0].value, ast::Expr::Var(sp_pat!(ast::Var::Resolved { var_id: VarId::Reg(RegId(100)), .. }))),
                    "{:?}", args[0],
                );
            },
            _ => panic!(),
        }
    }
}
