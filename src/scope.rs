use std::fmt;
use std::num::NonZeroUsize;
use std::collections::HashMap;
use crate::ident::Ident;
use crate::type_system::ScalarType;

/// Uniquely identifies a named variable (which may be a local or a register alias from a mapfile).
///
/// Information about the variable like its name and type can be retrieved from [`Variables`].
///
/// This is the preferred over [`Ident`]s as it accounts for scope. (i.e. two variables with the
/// same name can have different [`VarId`]s).   To obtain these from a parsed script, see
/// [`crate::passes::resolve_vars`] which replaces all [`Ident`]-based variables with [`VarId`]s.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct VarId(NonZeroUsize);

/// Identifies a scope in which a set of names are visible.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Default)]
pub struct ScopeId(
    // we define a new scope for every variable.  None is the empty scope.
    Option<VarId>,
);

/// Scope containing no variables.
pub const EMPTY_SCOPE: ScopeId = ScopeId(None);

/// Provides data for all [`VarId`]s in the script being compiled.
#[derive(Debug, Clone)]
pub struct Variables {
    scopes: Vec<Scope>,
}

#[derive(Debug, Clone)]
struct Scope {
    /// Name of the variable defined in this scope.
    ident: Ident,
    /// Type of the variable defined in this scope, if fixed.
    ty: Option<ScalarType>,
    /// Scope where the rest of the visible variables are defined.
    parent: ScopeId,
}

impl Variables {
    /// Create one with no variables defined.
    pub fn new() -> Self {
        // a dummy that is never used for anything because we number variables starting from 1.
        // (so that zero can refer to the scope with no variables)
        let dummy_scope = Scope {
            ident: "!!_DUMMY_IDENT_!!".parse().unwrap(),
            ty: None,
            parent: EMPTY_SCOPE,
        };
        Variables { scopes: vec![dummy_scope] }
    }
    pub fn get_name(&self, id: VarId) -> &Ident { &self.scopes[id.0.get()].ident }
    pub fn get_type(&self, id: VarId) -> Option<ScalarType> { self.scopes[id.0.get()].ty }
    pub fn get_parent_scope(&self, id: VarId) -> ScopeId { self.scopes[id.0.get()].parent }
    /// Get the scope containing this variable declaration.
    #[inline(always)]
    pub fn get_scope(&self, id: VarId) -> ScopeId { ScopeId(Some(id)) }

    /// Declares a variable.  This will create a new scope, which will be a child of the given scope.
    pub fn declare(&mut self, parent: ScopeId, ident: Ident, ty: Option<ScalarType>) -> VarId {
        let id = VarId(NonZeroUsize::new(self.scopes.len()).unwrap());
        self.scopes.push(Scope { ident, ty, parent });
        id
    }
}

/// A helper for resolving identifiers into [`VarId`s](VarId).
#[derive(Debug, Clone)]
pub(crate) struct NameResolver {
    current_scope: ScopeId,

    /// Variables that have each name. The last id in each vec is the active variable
    /// with that name; any earlier ones are shadowed.
    active_vars: HashMap<Ident, Vec<VarId>>,
}

impl NameResolver {
    /// Create a new [`NameResolver`] sitting in the empty scope.
    pub fn new() -> Self {
        NameResolver { current_scope: EMPTY_SCOPE, active_vars: Default::default() }
    }

    /// Get the scope at which this [`NameResolver`] is currently resolving names.
    pub fn current_scope(&self) -> ScopeId { self.current_scope }

    /// Resolve an identifier at the current scope.
    pub fn resolve(&self, ident: &Ident) -> Option<VarId> {
        self.active_vars.get(ident).and_then(|vec| vec.last().copied())
    }

    /// Travel from the current scope into one that is lower down the tree.
    ///
    /// (note: the case where `current_scope == descendant` will trivially succeed)
    pub fn enter_descendant(&mut self, descendant: ScopeId, variables: &Variables) {
        let mut vars_to_add = vec![];

        // travel from descendant back up to current position to gather tree edges in reverse
        let mut scope_iter = descendant;
        while self.current_scope != scope_iter {
            if let ScopeId(Some(var_id)) = self.current_scope {
                let name = variables.get_name(var_id);
                vars_to_add.push((name, var_id));
                scope_iter = variables.get_parent_scope(var_id);
            } else {
                panic!("scope was not a descendant!");
            }
        }

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

impl fmt::Display for VarId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl fmt::Display for ScopeId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0.map(|x| x.0.get()).unwrap_or(0), f)
    }
}

impl fmt::Debug for VarId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Debug for ScopeId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}
