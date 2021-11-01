use std::fmt;
use std::num::NonZeroU32;
use std::collections::HashMap;

use crate::raw;
use crate::game::InstrLanguage;
use crate::ident::{Ident, ResIdent};
use crate::context::CompilerContext;

#[cfg(test)]
mod tests;

pub type IdMap<K, V> = HashMap<K, V>; // probably want to get FxHashMap

newtype_id!{
    /// Identifies a node in the AST that may be interesting to semantic analysis.
    ///
    /// Semantic analysis passes typically return data indexed by [`NodeId`], bypassing the need
    /// to store this information inside the AST or a similarly-shaped structure.
    ///
    /// # Uniqueness and freshening
    ///
    /// [`NodeId`]s must generally be unique within any AST node that [any semantic analysis pass][`crate::passes::semantics`]
    /// is called on.  This requirement is typically checked; otherwise, if a duplicate ID were to exist in the AST
    /// (due to e.g. an ill-advised clone), then the stored analysis result on that ID could end up different
    /// depending on the order in which the two duplicates are visited.
    ///
    /// All [`NodeId`]s in the AST are [`Option`]s.  These can be set to `None` during the initial construction of
    /// an AST fragment (e.g. during parsing), but should be reassigned as soon as the fragment is complete by calling
    /// either [`crate::passes::resolution::fill_missing_node_ids`] or [`crate::passes::resolution::refresh_node_ids`].
    ///
    /// When duplicating an AST node (for instance, inlining a function body or unrolling a loop), the copy should be
    /// reassigned new [`NodeId`]s using [`CompilerContext::refresh_node_ids`].
    #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct NodeId(pub NonZeroU32);
}

newtype_id! {
    /// A "resolvable ID."  Identifies a instance in the source code of an identifier that *can*
    /// be resolved to something.
    ///
    /// Name resolution is effectively the act of mapping [`ResId`]s to [`DefId`]s.
    ///
    /// # Uniqueness
    ///
    /// [`ResId`]s must be unique within any AST node that the [name resolution pass][`crate::passes::resolution::resolve_names`]
    /// is called on, but after that, they can be freely copied around; all copies will continue referring to the
    /// same definition.
    ///
    /// There is not necessarily any association between the value of a [`ResId`] and a [`NodeId`].
    /// [`crate::passes::resolution::refresh_node_ids`] will reassign the latter, but not the former.
    #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct ResId(pub NonZeroU32);
}

newtype_id! {
    /// Represents some sort of definition; a unique thing (an item, a local variable, a globally-defined
    /// register alias, etc.) that an identifier can possibly be resolved to.
    ///
    /// [`DefId`]s are created by the methods on [`CompilerContext`], and can be obtained after creation
    /// from [`Resolutions`].
    #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct DefId(pub NonZeroU32);
}

newtype_id! {
    /// A stable ID for a loop.
    ///
    /// The purpose of this is because code transformations may move `continue`/`break` around in ways that
    /// cause a different loop to become their lexical parent.  Depending on the circumstance it may be
    /// desirable to detect this as a bug or decay into `goto label` syntax.
    ///
    /// These should be filled in ASAP, ideally at node construction or just after parsing.
    #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct LoopId(pub NonZeroU32);
}

newtype_id! {
    /// The number used to access a register as an instruction argument.  This uniquely identifies a register.
    ///
    /// For instance, in TH17 ECL, the `TIME` register has an id of `-9988`.
    #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct RegId(pub raw::Register);
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
    pub fn noun_long(self, alias_language: Option<InstrLanguage>) -> String {
        match (self, alias_language) {
            (Namespace::Vars, Some(language)) => format!("{} register or variable", language.descr()),
            (Namespace::Funcs, Some(language)) => format!("{} instruction or function", language.descr()),
            (Namespace::Vars, None) => format!("variable"),
            (Namespace::Funcs, None) => format!("function"),
        }
    }
}

/// Node ID allocator.
///
/// This can't be passed between threads, but uses internal mutability
/// as the single-threadedness eliminates most bugs related to misuse.
#[derive(Debug)]
pub struct UnusedIds<T> {
    next: std::cell::Cell<u32>,
    _covariant: std::marker::PhantomData<T>,
    _explicitly_single_threaded: std::marker::PhantomData<*mut ()>,
}

impl<T: From<NonZeroU32>> UnusedIds<T> {
    pub fn new() -> Self {
        UnusedIds {
            next: 1.into(),
            _covariant: Default::default(),
            _explicitly_single_threaded: Default::default(),
        }
    }

    pub fn next(&self) -> T {
        self.next.set(self.next.get().checked_add(1).expect("too many node ids!"));
        std::num::NonZeroU32::new(self.next.get() - 1).unwrap().into()
    }
}

pub mod node_id_helpers {
    //! Helper functions for use by semantic analysis passes to deal with [`NodeId`] bugs.
    use super::*;
    use crate::error::ErrorReported;
    use crate::diagnostic::Emitter;
    use crate::pos::{Sp, Span};

    /// Report a bug if an AST node doesn't have a [`NodeId`].
    pub fn expect_node_id<A>(emitter: &impl Emitter, node: &Sp<A>, node_id: Option<NodeId>) -> Result<NodeId, ErrorReported> {
        node_id.ok_or_else(|| bug_missing_node_id(emitter, node.span))
    }

    /// Insert into an [`IdMap`] and report a bug if the key is already present.
    pub fn id_map_insert<A, V>(emitter: &impl Emitter, id_map: &mut IdMap<NodeId, V>, node: &Sp<A>, node_id: Option<NodeId>, value: V) -> Result<(), ErrorReported> {
        let node_id = expect_node_id(emitter, node, node_id)?;
        if let Some(_prev_value) = id_map.insert(node_id, value) {
            return Err(bug_duplicate_node_id(emitter, node.span));
        }
        Ok(())
    }

    #[inline(never)]
    fn bug_missing_node_id(emitter: &dyn Emitter, span: Span) -> ErrorReported {
        emitter.as_sized().emit(bug!(
            message("AST node missing node ID!"),
            primary(span, "related to this code"),
        ))
    }

    #[inline(never)]
    fn bug_duplicate_node_id(emitter: &dyn Emitter, span: Span) -> ErrorReported {
        emitter.as_sized().emit(bug!(
            message("AST node has duplicate node ID!"),
            primary(span, "has a duplicate node id"),
            note("it was probably cloned without refreshing ids"),
        ))
    }
}

pub use resolve_vars::Visitor as ResolveVarsVisitor;
mod resolve_vars {
    use super::*;
    use crate::ast::{self, Visit};
    use crate::pos::Sp;
    use crate::error::{ErrorReported, ErrorFlag};
    use super::rib::{RibKind, RibStacks};

    /// Visitor that performs name resolution. Please don't use this directly,
    /// but instead call [`crate::passes::resolution::resolve_names`].
    ///
    /// The way it works is by visiting AST nodes in a particular order based on what ought to
    /// be in scope at any given point in the graph.
    pub struct Visitor<'a, 'ctx> {
        rib_stacks: RibStacks,
        errors: ErrorFlag,
        ctx: &'a mut CompilerContext<'ctx>,
    }

    impl<'a, 'ctx> Visitor<'a, 'ctx> {
        pub fn new(ctx: &'a mut CompilerContext<'ctx>) -> Self {
            Visitor {
                rib_stacks: ctx.defs.initial_ribs().into_iter().collect(),
                errors: ErrorFlag::new(),
                ctx,
            }
        }

        pub fn finish(self) -> Result<(), ErrorReported> {
            self.errors.into_result(())
        }
    }

    impl Visit for Visitor<'_, '_> {
        fn visit_file(&mut self, script: &ast::ScriptFile) {
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

                | ast::Item::Timeline { .. }
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
            match x.kind {
                ast::StmtKind::Declaration { ty_keyword, ref vars } => {
                    let var_ty = ty_keyword.value.var_ty();

                    for pair in vars {
                        let (var, init_value) = &pair.value;

                        // variable should not be allowed to appear in its own initializer, so walk the expression first.
                        if let ast::VarName::Normal { ident, .. } = &var.value.name {
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

                ast::StmtKind::Item(ref item) => self.visit_item(item),

                _ => ast::walk_stmt(self, x),
            }
        }

        fn visit_var(&mut self, var: &Sp<ast::Var>) {
            if let ast::VarName::Normal { ref ident, language_if_reg, .. } = var.name {
                match self.rib_stacks.resolve(Namespace::Vars, var.span, language_if_reg, ident) {
                    Err(e) => self.errors.set(self.ctx.emitter.emit(e)),
                    Ok(def_id) => self.ctx.resolutions.record_resolution(ident, def_id),
                }
            }
        }

        fn visit_expr(&mut self, expr: &Sp<ast::Expr>) {
            if let ast::Expr::Call { name, .. } = &expr.value {
                if let ast::CallableName::Normal { ref ident, language_if_ins, .. } = name.value {
                    match self.rib_stacks.resolve(Namespace::Funcs, name.span, language_if_ins, ident) {
                        Err(e) => self.errors.set(self.ctx.emitter.emit(e)),
                        Ok(def_id) => self.ctx.resolutions.record_resolution(ident, def_id),
                    }
                }
            }
            ast::walk_expr(self, expr)
        }
    }

    // get the items defined inside a block (that aren't further nested inside another block)
    fn block_items(block: &ast::Block) -> impl Iterator<Item=&Sp<ast::Item>> {
        block.0.iter().filter_map(|stmt| match &stmt.kind {
            ast::StmtKind::Item(item) => Some(&**item),
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
                self.errors.set(self.ctx.emitter.emit(error!(
                    message("redefinition of {} '{}'", noun, ident),
                    secondary(old_def.def_ident_span, "originally defined here"),
                    primary(ident.span, "redefinition of {}", noun),
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

                ast::Item::AnmScript { .. } => {}
                ast::Item::Timeline { .. } => {},
                ast::Item::Meta { .. } => {},
            } // match item.value
        }
    }
}

pub mod rib {
    use super::*;

    use crate::pos::{Sp, Span};
    use crate::diagnostic::Diagnostic;

    /// A helper used during name resolution to track stacks of [`Ribs`] representing the current scope.
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
        Mapfile { language: InstrLanguage },

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
                (RibKind::Mapfile { .. }, Namespace::Vars) => "register alias",
                (RibKind::Mapfile { .. }, Namespace::Funcs) => "instruction alias",
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
        pub fn resolve(&self, ns: Namespace, cur_span: Span, alias_language: Option<InstrLanguage>, cur_ident: &Ident) -> Result<DefId, Diagnostic> {
            // set to e.g. `Some("function")` when we first cross pass the threshold of a function or const.
            let mut crossed_local_border = None::<&str>;
            // set to Some(_) if we find a match for a reg/instr alias that isn't usable here
            let mut language_with_ident = None::<InstrLanguage>;

            'ribs: for rib in self.ribs[ns].iter().rev() {
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
                    }

                    if let RibKind::Mapfile { language: mapfile_language } = rib.kind {
                        if alias_language != Some(mapfile_language) {
                            language_with_ident = Some(mapfile_language);
                            continue 'ribs;
                        }
                    }
                    return Ok(def.def_id);
                }
            } // for rib in ....

            let mut diag = error!(
                message("unknown {} '{}'", ns.noun_long(alias_language), cur_ident),
                primary(cur_span, "not found in this scope"),
            );

            if let Some(other_language) = language_with_ident {
                let extra = match (alias_language, ns) {
                    (None, Namespace::Funcs) => ", which is not usable in a const context",
                    (None, Namespace::Vars) => ", which is not a const expression",
                    (Some(_), _) => "",  // the "_ instruction or" in the main message is enough
                };
                diag.note(format!("there is a '{}' defined in {}{}", cur_ident, other_language.descr(), extra));
            }
            Err(diag)
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

// =============================================================================

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
        ResId(NonZeroU32::new(res as u32).unwrap())
    }

    pub fn attach_fresh_res(&mut self, ident: Ident) -> ResIdent {
        ResIdent::new(ident, self.fresh_res())
    }

    /// Record that the given [`ResIdent`] resolves to itself and return its new [`DefId`].
    pub fn record_self_resolution(&mut self, ident: &ResIdent) -> DefId {
        let res = ident.expect_res();
        let def = Self::synthesize_def_id_from_res_id(res);
        self._record_resolution(ident, def, true);
        def
    }

    pub fn record_resolution(&mut self, ident: &ResIdent, def: DefId) {
        self._record_resolution(ident, def, false);
    }

    fn _record_resolution(&mut self, ident: &ResIdent, def: DefId, is_self_resolution: bool) {
        let res = ident.expect_res();
        let dest = &mut self.map[res.0.get() as usize];

        let already_has_matching_definition = *dest == Some(def);

        // (This is to protect against bugs where an ident was cloned prior to name resolution,
        //  creating a situation where name resolution could have different results depending
        //  on AST traversal order.
        //
        //  The existence of this check is documented on `ResId`.  If you want to remove this check
        //  in order to e.g. make name resolution idempotent, please consider replacing it with some
        //  other form of check that all ResIds in the AST are unique prior to name resolution)
        //
        // (because such bugs can be so subtle, we will fail even if the existing definition matches.
        //  BUT!  We make a small exception for self-resolutions (definitions) because we might get
        //  called multiple times when adding the same name to multiple namespaces)
        assert!(
            dest.is_none() || (already_has_matching_definition && is_self_resolution),
            "(bug!) ident resolved multiple times: {:?}", res,
        );

        *dest = Some(def);
    }

    pub fn expect_def(&self, ident: &ResIdent) -> DefId {
        let res = ident.expect_res();
        self.map[res.0.get() as usize]
            .unwrap_or_else(|| panic!("(bug!) name '{}' has not yet been resolved!", ident))
    }

    fn synthesize_def_id_from_res_id(res: ResId) -> DefId {
        // no need to invent new numbers
        DefId(res.0)
    }
}
