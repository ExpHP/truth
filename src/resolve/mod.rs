use std::fmt;
use std::num::NonZeroU64;
use std::collections::HashMap;

use crate::ident::{Ident, ResIdent};
use crate::context::{CompilerContext, Defs};

#[cfg(test)]
mod tests;

/// A "resolvable ID."  Identifies a instance in the source code of an identifier that *can*
/// be resolved to something.
///
/// Name resolution is effectively the act of mapping [`ResId`]s to [`DefId`]s.
///
/// # Uniqueness
///
/// [`ResId`]s must be unique within any AST node that the [name resolution pass][`crate::passes::resolve_names::run`]
/// is called on.  This requirement is checked; otherwise, if a duplicate ID were to exist in the AST (due to e.g.
/// an ill-advised clone), then the resolution of that ID could end up depending on the order in which the two
/// duplicates are visited.
///
/// This does not mean that [`ResId`]s are always unique, however:
///
/// * Once the name resolution pass has finished, anything goes!  Clone nodes and move them around however
///   you like; they will continue referring to the same definitions.
/// * Clones of nodes may even be made before name resolution, so long as the clone isn't inserted anywhere
///   back into the AST.  For instance, in dealing with `const` variables, we may wish to record their expressions
///   upfront on some global evaluation context.  This is perfectly safe, and keeping the same [`ResId`]s in the
///   clones allows them to reap the benefits of performing name resolution on the original AST.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ResId(pub NonZeroU64);

/// Represents some sort of definition; a unique thing (an item, a local variable, a globally-defined
/// register alias, etc.) that a name can possibly be resolved to.
///
/// [`DefId`]s are created by the methods on [`CompilerContext`], and can be obtained after creation
/// from [`Resolutions`].
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefId(pub NonZeroU64);

/// The number used to access a register as an instruction argument.  This uniquely identifies a register.
///
/// For instance, in TH17 ECL, the `TIME` register has an id of `-9988`.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RegId(pub i32);

impl From<i32> for RegId {
    fn from(x: i32) -> Self { RegId(x) }
}

/// Identifies a scope in which a set of names are visible.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Default)]
struct ScopeId(
    // we define a new scope for every name.  None is the empty scope.
    Option<DefId>,
);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[derive(enum_map::Enum)]
pub enum Namespace {
    Vars,
    Funcs,
}

impl Namespace {
    pub fn noun_long(self) -> &'static str { match self {
        Namespace::Vars => "variable",
        Namespace::Funcs => "function",
    }}
}

use name_resolver::{NameResolver};
mod name_resolver {
    use super::*;

    use crate::pos::Span;
    use crate::error::CompileError;

    /// A helper whose purpose is to incrementally track which [`DefId`] each [`Ident`]
    /// currently maps to in each namespace as we travel up and down the scope tree.
    ///
    /// Basically, all of the names in the script can be thought of as forming a tree.
    /// The root node of the tree is the scope with no names.  Then, each new name definition creates a
    /// new child scope based off an existing scope.  During name resolution, [`NameResolver`] travels
    /// up and down this tree in order to learn which definitions are entering or leaving scope at any
    /// given time.
    ///
    /// Currently we do not explicitly construct this tree, as there is not currently ever any need for us to
    /// retain information about other branches than the one we are currently in.
    ///
    /// (see https://github.com/ExpHP/truth/blob/e7d5e303b6309ef6101faf87ae67c7ff67034535/src/var.rs#L61-L233
    /// for an older design, where an explicit tree was stored in `Variables`)
    #[derive(Debug, Clone)]
    pub(super) struct NameResolver {
        /// This contains the data we need from each node along our current path from the root of the scope tree;
        /// i.e. it has an entry for every name *currently in scope.*  (including ones that are shadowed)
        names_in_scope: Vec<(Namespace, Ident, DefId)>,

        /// An incrementally-maintained reverse mapping that lets us resolve variables in O(1).
        /// The last id in each vec is the one that the identifier currently resolves to;
        /// the ones before it are shadowed.
        names_by_ident: enum_map::EnumMap<Namespace, HashMap<Ident, Vec<DefId>>>,
    }

    /// A newtyped `usize` representing tree depth. (this uniquely identifies an ancestor node)
    pub struct Depth(usize);

    impl NameResolver {
        /// Create a new [`NameResolver`] sitting in the empty scope.
        pub fn new() -> Self {
            NameResolver { names_in_scope: vec![], names_by_ident: Default::default() }
        }

        /// Create a new [`NameResolver`] sitting in a scope that is pre-populated with all
        /// externally-defined names.
        pub fn init_from_defs(defs: &Defs) -> Self {
            let mut this = Self::new();
            for (ns, def_id) in defs.globals() {
                let ident = defs.name(ns, def_id);
                this.enter_child(ident.as_raw().clone(), ns, def_id);
            }
            this
        }

        pub fn current_depth(&self) -> Depth {
            Depth(self.names_in_scope.len())
        }

        pub fn resolve(&self, span: Span, ident: &ResIdent, ns: Namespace) -> Result<DefId, CompileError> {
            self._resolve(ident, ns).ok_or_else(|| error!(
                message("unknown {} '{}'", ns.noun_long(), ident),
                primary(span, "not found in this scope"),
            ))
        }

        fn _resolve(&self, ident: &Ident, ns: Namespace) -> Option<DefId> {
            self.names_by_ident[ns].get(ident)
                .and_then(|vec| vec.last().copied())  // the one that isn't shadowed
        }

        /// Travel from the current scope into a direct child by adding a single name
        /// into the current scope.
        pub fn enter_child(&mut self, ident: Ident, ns: Namespace, def_id: DefId) {
            self.names_in_scope.push((ns, ident.clone(), def_id));
            self.names_by_ident[ns].entry(ident.clone()).or_default().push(def_id);
        }

        /// Travel from the current scope into one that is (not necessarily strictly) above it in the tree.
        pub fn return_to_ancestor(&mut self, ancestor_depth: Depth) {
            while self.current_depth().0 > ancestor_depth.0 {
                let (ns, ident, def_id) = self.names_in_scope.pop().unwrap();
                let popped_def_id = self.names_by_ident[ns].get_mut(&ident).unwrap().pop().unwrap();
                assert_eq!(def_id, popped_def_id, "(bug!) internal inconsistency!");
            }
        }
    }
}

pub use resolve_vars::Visitor as ResolveVarsVisitor;
mod resolve_vars {
    use super::*;
    use crate::ast::{self, Visit};
    use crate::pos::{Sp, Span};
    use crate::error::CompileError;

    /// Visitor for name resolution. Please don't use this directly,
    /// but instead call [`crate::passes::resolve_names::run`].
    pub struct Visitor<'ts> {
        scope_traveler: NameResolver,
        errors: CompileError,
        ctx: &'ts mut CompilerContext,
    }

    impl<'ts> Visitor<'ts> {
        pub fn new(ctx: &'ts mut CompilerContext) -> Self {
            Visitor {
                scope_traveler: NameResolver::init_from_defs(&ctx.defs),
                errors: CompileError::new_empty(),
                ctx,
            }
        }

        pub fn finish(self) -> Result<(), CompileError> {
            self.errors.into_result(())
        }
    }

    impl Visit for Visitor<'_> {
        fn visit_script(&mut self, x: &ast::Script) {
            // scan ahead for all function definitions and consts
            self.add_items_to_scope(&x.items);

            ast::walk_script(self, x);
        }

        fn visit_item(&mut self, x: &Sp<ast::Item>) {
            match &x.value {
                | ast::Item::Func { params, code, .. }
                => {
                    if let Some(code) = code {
                        // we have to put the parameters in scope
                        let outer_scope_depth = self.scope_traveler.current_depth();
                        for (ty_keyword, ident) in params {
                            let def_id = self.ctx.define_local(ident.clone(), ty_keyword.var_ty());

                            self.scope_traveler.enter_child(ident.as_raw().clone(), Namespace::Vars, def_id);
                        }
                        ast::walk_block(self, code);

                        self.scope_traveler.return_to_ancestor(outer_scope_depth);
                    }
                },

                | ast::Item::ConstVar { vars, .. }
                => {
                    // we don't want to resolve the declaration idents, only the expressions
                    for sp_pat![(_, expr)] in vars {
                        self.visit_expr(expr);
                    }
                },

                | ast::Item::AnmScript { .. }
                | ast::Item::Meta { .. }
                => ast::walk_item(self, x),
            }
        }

        fn visit_block(&mut self, x: &ast::Block) {
            let outer_scope_depth = self.scope_traveler.current_depth();

            // "lift" items to the top of the block
            let items_in_block = x.0.iter().filter_map(|stmt| match &stmt.body {
                ast::StmtBody::Item(item) => Some(&**item),
                _ => None,
            });
            self.add_items_to_scope(items_in_block);

            ast::walk_block(self, x);

            // make names defined within the block no longer resolvable
            self.scope_traveler.return_to_ancestor(outer_scope_depth);
        }

        fn visit_stmt(&mut self, x: &Sp<ast::Stmt>) {
            match &x.body {
                ast::StmtBody::Declaration { keyword, vars } => {
                    let ty = keyword.var_ty();

                    for pair in vars {
                        let (var, init_value) = &pair.value;
                        if let ast::VarName::Normal { ident } = &var.value.name {
                            // a variable should not be allowed to appear in its own initializer, so walk the expression first.
                            if let Some(init_value) = init_value {
                                self.visit_expr(init_value);
                            }

                            let def_id = self.ctx.define_local(sp!(var.span => ident.clone()), ty);

                            // record the variable in our resolution tree and enter its scope
                            // so that it can be used in future expressions
                            self.scope_traveler.enter_child(ident.as_raw().clone(), Namespace::Vars, def_id);

                        } else {
                            unreachable!("impossible var name in declaration {:?}", var.value.name);
                        }
                    }
                },
                _ => ast::walk_stmt(self, x),
            }
        }

        fn visit_var(&mut self, var: &Sp<ast::Var>) {
            if let ast::VarName::Normal { ref ident, .. } = var.name {
                match self.scope_traveler.resolve(var.span, ident, Namespace::Vars) {
                    Err(e) => self.errors.append(e),
                    Ok(def_id) => self.ctx.resolutions.record_resolution(ident, def_id),
                }
            }
        }

        fn visit_expr(&mut self, expr: &Sp<ast::Expr>) {
            if let ast::Expr::Call { name, .. } = &expr.value {
                if let ast::CallableName::Normal { ident, .. } = &name.value {
                    match self.scope_traveler.resolve(name.span, ident, Namespace::Funcs) {
                        Err(e) => self.errors.append(e),
                        Ok(def_id) => self.ctx.resolutions.record_resolution(ident, def_id),
                    }
                }
            }
            ast::walk_expr(self, expr)
        }
    }

    impl Visitor<'_> {
        /// An early pass used on the script or on a block that adds all items to scope,
        /// without yet recursing into any of them.
        ///
        /// This is what allows items to be used prior to their definition.
        fn add_items_to_scope<'b>(&mut self, items: impl IntoIterator<Item=&'b Sp<ast::Item>>) {
            let mut funcs_seen = RedefinitionChecker::new("function");
            let mut consts_seen = RedefinitionChecker::new("const");
            for item in items {
                match item.value {
                    ast::Item::Func { ref ident, .. } => {
                        if let Err(e) = funcs_seen.check_for_redefinition(ident.as_raw(), ident.span) {
                            self.errors.append(e);
                            // keep going; this is relatively harmless
                        }

                        let def_id = self.ctx.define_user_func(ident.clone());

                        // add it to the current scope
                        self.scope_traveler.enter_child(ident.as_raw().clone(), Namespace::Funcs, def_id);
                    },

                    ast::Item::ConstVar { keyword, ref vars } => {
                        let ty = keyword.var_ty().expect("untyped consts don't parse");

                        for sp_pat![(var, expr)] in vars {
                            let ident = var.name.expect_ident();
                            if let Err(e) = consts_seen.check_for_redefinition(ident.as_raw(), var.span) {
                                self.errors.append(e);
                                // keep going; this is relatively harmless
                            }

                            let def_id = self.ctx.define_const_var(sp!(var.span => ident.clone()), ty, expr.clone());

                            // add it to the current scope
                            self.scope_traveler.enter_child(ident.as_raw().clone(), Namespace::Vars, def_id);
                        }
                    },

                    ast::Item::Meta { .. } => {},
                    ast::Item::AnmScript { .. } => {},
                }
            }
        }
    }

    struct RedefinitionChecker {
        map: HashMap<Ident, Span>,
        noun: &'static str,
    }

    impl RedefinitionChecker {
        fn new(noun: &'static str) -> Self { RedefinitionChecker {
            map: Default::default(),
            noun,
        }}
        /// Record an item,
        fn check_for_redefinition(&mut self, ident: &Ident, span: Span) -> Result<(), CompileError> {
            if let Some(old_span) = self.map.get(ident) {
                return Err(error!(
                    message("redefinition of {} '{}'", self.noun, ident),
                    primary(span, "redefinition of {}", self.noun),
                    secondary(old_span, "originally defined here"),
                ));
            }
            self.map.insert(ident.clone(), span);
            Ok(())
        }
    }
}


// =============================================================================

impl fmt::Display for RegId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl fmt::Debug for RegId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for ScopeId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0.map(|x| x.0.get()).unwrap_or(0), f)
    }
}

impl fmt::Debug for ScopeId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Debug for ResId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl fmt::Display for ResId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl fmt::Debug for DefId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl fmt::Display for DefId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

// =============================================================================

/// The place where successfully-determined name resolution information is stored in
/// the global compilation context.
#[derive(Debug, Clone)]
pub struct Resolutions {
    /// A dense map of [`ResId`] to [`DefId`].  The zeroth element is a dummy.
    map: Vec<Option<DefId>>,
}

impl Default for Resolutions {
    fn default() -> Self { Self::new() }
}

impl Resolutions {
    pub fn new() -> Self {
        Resolutions { map: vec![None] }  // the None is never used because ResId is nonzero
    }

    /// Get a new [`ResId`] for an unresolved name.
    pub fn fresh_res(&mut self) -> ResId {
        let res = self.map.len();
        self.map.push(None);
        ResId(NonZeroU64::new(res as u64).unwrap())
    }

    pub fn attach_fresh_res(&mut self, ident: Ident) -> ResIdent {
        ResIdent::new(ident, self.fresh_res())
    }

    pub fn record_resolution(&mut self, ident: &ResIdent, def: DefId) {
        let res = ident.expect_res();
        let dest = &mut self.map[res.0.get() as usize];

        // (This is to protect against bugs where an ident was cloned prior to name resolution,
        //  creating a situation where name resolution could have different results depending
        //  on AST traversal order.
        //
        //  The existence of this check is documented on `ResId`.  If you want to remove this check
        //  in order to e.g. make name resolution idempotent, please consider replacing it with some
        //  other form of check that all ResIds in the AST are unique prior to name resolution)
        assert!(dest.is_none(), "(bug!) ident resolved multiple times: {:?}", res);

        *dest = Some(def);
    }

    pub fn expect_def(&self, ident: &ResIdent) -> DefId {
        let res = ident.expect_res();
        self.map[res.0.get() as usize]
            .unwrap_or_else(|| panic!("(bug!) name '{}' has not yet been resolved!", ident))
    }
}
