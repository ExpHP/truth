use std::fmt;
use std::num::NonZeroU64;
use std::collections::HashMap;

use crate::ident::{Ident, ResIdent};
use crate::context::CompilerContext;

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

pub mod rib {
    use super::*;

    use crate::pos::{Sp, Span};
    use crate::diagnostic::Diagnostic;

    /// A helper used during name resolution to track stacks of [`Ribs`] representing the current scope
    ///
    #[derive(Debug, Clone)]
    pub(super) struct RibStacks {
        ribs: enum_map::EnumMap<Namespace, Vec<Rib>>,
    }

    /// A collection of names in a single namespace whose scopes all end simultaneously.
    ///
    /// The name and concept derives from [rustc's own ribs].  A stack of these is tracked for each
    /// namespace, and name resolution walks backwards through the stack trying to find a match.
    ///
    /// [rustc's own ribs]: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_resolve/late/struct.Rib.html
    #[derive(Debug, Clone)]
    pub struct Rib {
        pub ns: Namespace,
        pub kind: RibKind,
        defs: HashMap<Ident, RibEntry>,
    }

    #[derive(Debug, Clone)]
    pub struct RibEntry {
        pub def_id: DefId,
        pub def_ident_span: Span,
    }

    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    pub enum RibKind {
        /// Contains locals defined within a block. One is created for each block, and it will
        /// always be the top rib when visiting statements.
        ///
        /// (contrast with rustc where the idea of ribs is borrowed from; unlike rust, truth does
        ///  not allow locals to shadow other locals defined in the same block, because that
        ///  functionality is not useful in a language with such a primitive type system)
        Locals,

        /// Function parameters.  (really just locals, but we put "parameter" in error messages)
        Params,

        /// An empty, "marker" rib indicating the beginning of an item's definition, blocking access
        /// to all locals in outer ribs.  (and re-providing access to const items they've shadowed)
        LocalBarrier {
            /// `"function"`, `"const"`
            of_what: &'static str
        },

        /// Contains items within a block.  (`const`s or funcs)
        Items,

        /// A rib created from entries in a mapfile.
        Mapfile,

        /// A set of names generated from e.g. meta.
        Generated,

        /// An empty rib that's always first so that we don't need to justify
        DummyRoot,
    }

    impl Rib {
        pub fn new(ns: Namespace, kind: RibKind) -> Self {
            Rib { kind, ns, defs: Default::default() }
        }

        pub fn get(&mut self, ident: &Ident) -> Option<&RibEntry> {
            self.defs.get(ident)
        }

        /// Returns the old definition if this is a redefinition.
        pub fn insert(&mut self, ident: Sp<impl AsRef<Ident>>, def_id: DefId) -> Result<(), RibEntry> {
            let new_entry = RibEntry { def_id, def_ident_span: ident.span };
            match self.defs.insert(ident.value.as_ref().clone(), new_entry) {
                None => Ok(()),
                Some(old) => Err(old)
            }
        }

        /// Get a singular noun (with no article) describing the type of thing the rib contains,
        /// e.g. `"register alias"` or `"parameter"`.
        pub fn noun(&self) -> &'static str {
            match (&self.kind, self.ns) {
                (RibKind::Locals, _) => "local",
                (RibKind::Params, _) => "parameter",
                (RibKind::Items, Namespace::Vars) => "const",
                (RibKind::Items, Namespace::Funcs) => "function",
                (RibKind::Mapfile, Namespace::Vars) => "register alias",
                (RibKind::Mapfile, Namespace::Funcs) => "instruction alias",
                (RibKind::Generated, Namespace::Vars) => "automatic const",
                (RibKind::Generated, Namespace::Funcs) => "automatic func",

                (RibKind::LocalBarrier { .. }, ns) |
                (RibKind::DummyRoot, ns) => panic!("noun called on {:?} {:?} rib", self, ns),
            }
        }
    }

    impl RibKind {
        /// If this is a barrier that hides outer local variables, get a string describing it.
        /// (`"function"` or `"const"`)
        pub fn local_barrier_cause(&self) -> Option<&'static str> {
            match *self {
                RibKind::LocalBarrier { of_what } => Some(of_what),
                _ => None,
            }
        }

        /// Determine if this rib holds a kind of local.
        pub fn holds_locals(&self) -> bool {
            match *self {
                RibKind::Locals => true,
                RibKind::Params => true,
                _ => false,
            }
        }
    }

    impl RibStacks {
        /// Create a new [`NameResolver`] sitting in the empty scope.
        pub fn new() -> Self {
            RibStacks { ribs: enum_map::enum_map!{
                ns => vec![Rib { ns, kind: RibKind::DummyRoot, defs: Default::default() }],
            }}
        }

        /// Push a rib onto a namespace's rib stack.
        pub fn enter_rib(&mut self, rib: Rib) {
            self.ribs[rib.ns].push(rib)
        }

        /// Push an empty rib onto a namespace's rib stack.
        pub fn enter_new_rib(&mut self, ns: Namespace, kind: RibKind) {
            self.enter_rib(Rib::new(ns, kind))
        }

        /// Pop a rib from a namespace, double-checking its `kind` for our sanity.
        pub fn leave_rib(&mut self, ns: Namespace, expected_kind: RibKind) {
            let popped = self.ribs[ns].pop().expect("unbalanced rib usage!");
            assert_eq!(popped.kind, expected_kind);
        }

        /// Get the top rib for a namespace, checking that it is the given kind.
        pub fn top_rib(&mut self, ns: Namespace, expected_kind: RibKind) -> &mut Rib {
            let out = self.ribs[ns].last_mut().expect("no ribs?");
            assert_eq!(out.kind, expected_kind);
            out
        }

        /// Resolve an identifier by walking backwards through the stack of ribs.
        pub fn resolve(&self, ns: Namespace, cur_span: Span, cur_ident: &Ident) -> Result<DefId, Diagnostic> {
            // set to e.g. `Some("function")` when we first cross pass the threshold of a function or const.
            let mut crossed_local_border = None::<&str>;

            for rib in self.ribs[ns].iter().rev() {
                if let Some(cause) = rib.kind.local_barrier_cause() {
                    crossed_local_border.get_or_insert(cause);
                }

                if let Some(def) = rib.defs.get(cur_ident) {
                    if rib.kind.holds_locals() && crossed_local_border.is_some() {
                        let local_kind = rib.noun();
                        let local_span = def.def_ident_span;
                        let item_kind = crossed_local_border.unwrap();
                        return Err(error!(
                            message("cannot use {} from outside {}", local_kind, item_kind),
                            primary(cur_span, "used in a nested {}", item_kind),
                            secondary(local_span, "defined here"),
                        ));
                    } else {
                        return Ok(def.def_id);
                    }
                }
            } // for rib in ....

            Err(error!(
                message("unknown {} '{}'", ns.noun_long(), cur_ident),
                primary(cur_span, "not found in this scope"),
            ))
        }
    }

    impl std::iter::FromIterator<Rib> for RibStacks {
        fn from_iter<It: IntoIterator<Item=Rib>>(iter: It) -> Self {
            let mut out = Self::new();
            for rib in iter {
                out.ribs[rib.ns].push(rib);
            }
            out
        }
    }
}

pub use resolve_vars::Visitor as ResolveVarsVisitor;
mod resolve_vars {
    use super::*;
    use crate::ast::{self, Visit};
    use crate::pos::Sp;
    use crate::error::{ErrorReported, ErrorStore};
    use super::rib::{RibKind, RibStacks};

    /// Visitor that performs name resolution. Please don't use this directly,
    /// but instead call [`crate::passes::resolve_names::run`].
    ///
    /// The way it works is by visiting AST nodes in a particular order based on what ought to
    /// be in scope at any given point in the graph.
    pub struct Visitor<'a, 'ctx> {
        rib_stacks: RibStacks,
        errors: ErrorStore<ErrorReported>,
        ctx: &'a mut CompilerContext<'ctx>,
    }

    impl<'a, 'ctx> Visitor<'a, 'ctx> {
        pub fn new(ctx: &'a mut CompilerContext<'ctx>) -> Self {
            Visitor {
                rib_stacks: ctx.defs.initial_ribs().into_iter().collect(),
                errors: ErrorStore::new(),
                ctx,
            }
        }

        pub fn finish(self) -> Result<(), ErrorReported> {
            self.errors.into_result(())
        }
    }

    impl Visit for Visitor<'_, '_> {
        fn visit_script(&mut self, script: &ast::Script) {
            self.rib_stacks.enter_new_rib(Namespace::Vars, RibKind::Items);
            self.rib_stacks.enter_new_rib(Namespace::Funcs, RibKind::Items);

            // add all items to scope immediately so they're usable anywhere
            script.items.iter().for_each(|item| self.add_item_to_scope(item));

            // resolve exprs in the items' bodies before walking any statements, so that local
            // variables are not accidentally made visible inside those items.
            script.items.iter().for_each(|item| self.visit_item(item));

            self.rib_stacks.leave_rib(Namespace::Funcs, RibKind::Items);
            self.rib_stacks.leave_rib(Namespace::Vars, RibKind::Items);
        }

        fn visit_item(&mut self, item: &Sp<ast::Item>) {
            match &item.value {
                | ast::Item::Func { params, code, .. }
                => {
                    if let Some(code) = code {
                        // we have to put the parameters in scope
                        self.rib_stacks.enter_new_rib(Namespace::Vars, RibKind::LocalBarrier { of_what: "function" });
                        self.rib_stacks.enter_new_rib(Namespace::Vars, RibKind::Params);

                        for (ty_keyword, ident) in params {
                            let var_ty = ty_keyword.value.var_ty();
                            let def_id = self.ctx.define_local(ident.clone(), var_ty);
                            self.add_to_rib_with_redefinition_check(
                                Namespace::Vars, RibKind::Params, ident.clone(), def_id,
                            );
                        }

                        // now resolve the body
                        ast::walk_block(self, code);

                        self.rib_stacks.leave_rib(Namespace::Vars, RibKind::Params);
                        self.rib_stacks.leave_rib(Namespace::Vars, RibKind::LocalBarrier { of_what: "function" });
                    }
                },

                | ast::Item::ConstVar { vars, .. }
                => {
                    self.rib_stacks.enter_new_rib(Namespace::Vars, RibKind::LocalBarrier { of_what: "const" });
                    // we don't want to resolve the declaration idents, only the expressions
                    for sp_pat![(_, expr)] in vars {
                        self.visit_expr(expr);
                    }
                    self.rib_stacks.leave_rib(Namespace::Vars, RibKind::LocalBarrier { of_what: "const" });
                },

                | ast::Item::AnmScript { .. }
                | ast::Item::Meta { .. }
                => ast::walk_item(self, item),
            }
        }

        fn visit_block(&mut self, block: &ast::Block) {
            // add nested items to scope immediately so they're usable anywhere within the block
            self.rib_stacks.enter_new_rib(Namespace::Funcs, RibKind::Items);
            self.rib_stacks.enter_new_rib(Namespace::Vars, RibKind::Items);

            block_items(block).for_each(|item| self.add_item_to_scope(item));

            // now start resolving things inside the statements
            self.rib_stacks.enter_new_rib(Namespace::Vars, RibKind::Locals);
            block.0.iter().for_each(|stmt| self.visit_stmt(stmt));
            self.rib_stacks.leave_rib(Namespace::Vars, RibKind::Locals);

            self.rib_stacks.leave_rib(Namespace::Vars, RibKind::Items);
            self.rib_stacks.leave_rib(Namespace::Funcs, RibKind::Items);
        }

        fn visit_stmt(&mut self, x: &Sp<ast::Stmt>) {
            match x.body {
                ast::StmtBody::Declaration { ty_keyword, ref vars } => {
                    let var_ty = ty_keyword.value.var_ty();

                    for pair in vars {
                        let (var, init_value) = &pair.value;

                        // variable should not be allowed to appear in its own initializer, so walk the expression first.
                        if let ast::VarName::Normal { ident } = &var.value.name {
                            if let Some(init_value) = init_value {
                                self.visit_expr(init_value);
                            }

                            let sp_ident = sp!(var.span => ident.clone());
                            let def_id = self.ctx.define_local(sp_ident.clone(), var_ty);
                            self.add_to_rib_with_redefinition_check(
                                Namespace::Vars, RibKind::Locals, sp_ident.clone(), def_id,
                            );
                        } else {
                            unreachable!("impossible var name in declaration {:?}", var.value.name);
                        }
                    }
                },

                ast::StmtBody::Item(ref item) => self.visit_item(item),

                _ => ast::walk_stmt(self, x),
            }
        }

        fn visit_var(&mut self, var: &Sp<ast::Var>) {
            if let ast::VarName::Normal { ref ident, .. } = var.name {
                match self.rib_stacks.resolve(Namespace::Vars, var.span, ident) {
                    Err(e) => self.errors.append(self.ctx.diagnostics.emit(e)),
                    Ok(def_id) => self.ctx.resolutions.record_resolution(ident, def_id),
                }
            }
        }

        fn visit_expr(&mut self, expr: &Sp<ast::Expr>) {
            if let ast::Expr::Call { name, .. } = &expr.value {
                if let ast::CallableName::Normal { ident, .. } = &name.value {
                    match self.rib_stacks.resolve(Namespace::Funcs, name.span, ident) {
                        Err(e) => self.errors.append(self.ctx.diagnostics.emit(e)),
                        Ok(def_id) => self.ctx.resolutions.record_resolution(ident, def_id),
                    }
                }
            }
            ast::walk_expr(self, expr)
        }
    }

    // get the items defined inside a block (that aren't further nested inside another block)
    fn block_items(block: &ast::Block) -> impl Iterator<Item=&Sp<ast::Item>> {
        block.0.iter().filter_map(|stmt| match &stmt.body {
            ast::StmtBody::Item(item) => Some(&**item),
            _ => None,
        })
    }

    impl Visitor<'_, '_> {
        /// Add a name to the top rib in a namespace's stack, so that future names can resolve to it.
        ///
        /// If the name collides with another thing in the same rib, a redefinition error is generated.
        fn add_to_rib_with_redefinition_check(
            &mut self,
            ns: Namespace,
            expected_kind: RibKind, // as a sanity check
            ident: Sp<impl AsRef<Ident>>,  // Ident or ResIdent
            def_id: DefId,
        ) {
            let rib = self.rib_stacks.top_rib(ns, expected_kind);
            assert_eq!(rib.kind, expected_kind);

            let ident = sp!(ident.span => ident.as_ref().clone());

            if let Err(old_def) = rib.insert(ident.clone(), def_id) {
                let noun = rib.noun();
                self.errors.append(self.ctx.diagnostics.emit(error!(
                    message("redefinition of {} '{}'", noun, ident),
                    primary(ident.span, "redefinition of {}", noun),
                    secondary(old_def.def_ident_span, "originally defined here"),
                )));
            }
        }

        /// If this item defines something resolvable (a `const`, a function), add it to scope.
        ///
        /// This is called extremely early on items in a block, allowing items to be defined after they are used.
        fn add_item_to_scope<'b>(&mut self, item: &Sp<ast::Item>) {
            match item.value {
                ast::Item::Func { ref ident, ty_keyword, ref params, qualifier, code: _ } => {
                    let siggy = crate::context::defs::Signature::from_func_params(ty_keyword, params);
                    let def_id = self.ctx.define_user_func(ident.clone(), qualifier, siggy);
                    self.add_to_rib_with_redefinition_check(
                        Namespace::Funcs, RibKind::Items, ident.clone(), def_id,
                    );
                },

                ast::Item::ConstVar { ty_keyword, ref vars } => {
                    let ty = ty_keyword.value.var_ty().as_known_ty().expect("untyped consts don't parse");

                    for sp_pat![(var, expr)] in vars {
                        let ident = var.name.expect_ident();

                        let sp_ident = sp!(var.span => ident.clone());
                        let def_id = self.ctx.define_const_var(sp_ident.clone(), ty, expr.clone());
                        self.add_to_rib_with_redefinition_check(
                            Namespace::Vars, RibKind::Items, sp_ident.clone(), def_id,
                        );
                    }
                },

                ast::Item::Meta { .. } => {},
                ast::Item::AnmScript { .. } => {},
            } // match item.value
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
