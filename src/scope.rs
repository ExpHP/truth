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
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    /// If the variable is a register alias (i.e. from a mapfile), the register it references.
    reg: Option<i32>,
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
            reg: None,
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

    /// Indicate that a variable is an alias of a register that came from a mapfile.
    ///
    /// Name resolution will not produce this `VarId`, preferring to produce a direct register access instead.
    pub fn set_mapped_register(&mut self, id: VarId, reg: i32) { self.scopes[id.0.get()].reg = Some(reg); }

    /// Get the register mapped to this variable, if it is a register alias from a mapfile.
    ///
    /// IMPORTANT:  In some formats like ANM and old ECL, local variables are also stored in registers, but that
    /// is unrelated to this and this function will return `None` for them.
    pub fn get_mapped_register(&self, id: VarId) -> Option<i32> { self.scopes[id.0.get()].reg }

    /// Declare a new variable with a unique `VarId`.
    pub fn declare_temporary(&mut self, ty: Option<ScalarType>) -> VarId {
        // This function is only used by code outside this module, after name resolution has already been performed.
        // Hence, scope is no longer important for any purpose, and we can use anything.
        self.declare(EMPTY_SCOPE, "_tmp".parse().unwrap(), ty)
    }

    // TODO: We could move the contents of `passes::resolve_vars` into this module module and then mark as private
    //       everything involving ScopeId (including this method) since scopes only matter during name resolution.
    /// Declares a variable.  This will create a new scope, which will be a child of the given scope.
    ///
    /// NOTE: If name resolution has already been performed, then the `parent` and `ident` args are fairly
    /// meaningless, and you may consider calling [`Self::declare_temporary`] instead.
    pub fn declare(&mut self, parent: ScopeId, ident: Ident, ty: Option<ScalarType>) -> VarId {
        let id = VarId(NonZeroUsize::new(self.scopes.len()).unwrap());
        self.scopes.push(Scope { ident, ty, parent, reg: None });
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

pub enum Resolved {
    /// Local variable.
    Var(VarId),
    // FIXME I really feel like this shouldn't need the VarId field, but currently it's the
    //       only way to get the type without RegsAndInstrs
    /// Gloabal variable that maps to a register.
    Reg(VarId, i32),
}

impl NameResolver {
    /// Create a new [`NameResolver`] sitting in the empty scope.
    pub fn new() -> Self {
        NameResolver { current_scope: EMPTY_SCOPE, active_vars: Default::default() }
    }

    /// Get the scope at which this [`NameResolver`] is currently resolving names.
    pub fn current_scope(&self) -> ScopeId { self.current_scope }

    /// Resolve an identifier at the current scope.
    pub fn resolve(&self, ident: &Ident, variables: &Variables) -> Option<Resolved> {
        self.active_vars.get(ident)
            .and_then(|vec| vec.last().copied())  // the one that isn't shadowed
            .map(|var_id| match variables.get_mapped_register(var_id) {
                None => Resolved::Var(var_id),
                Some(reg) => Resolved::Reg(var_id, reg),
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
