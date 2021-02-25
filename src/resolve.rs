use std::fmt;
use std::num::NonZeroU64;
use std::collections::HashMap;
use crate::ident::{Ident, ResIdent};
use crate::type_system::{TypeSystem};

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
/// [`DefId`]s are created by the methods on [`TypeSystem`], and can be obtained after creation
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

use name_resolver::{NameResolver, ResolutionError};
mod name_resolver {
    use super::*;

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

    /// Indicates that nothing with the given name is in scope.
    ///
    /// (the caller should decide how to turn this into a CompileError)
    pub struct ResolutionError;

    impl NameResolver {
        /// Create a new [`NameResolver`] sitting in the empty scope.
        pub fn new() -> Self {
            NameResolver { names_in_scope: vec![], names_by_ident: Default::default() }
        }

        /// Create a new [`NameResolver`] sitting in a scope that is pre-populated with all
        /// externally-defined names.
        pub fn init_from_ty_ctx(ty_ctx: &TypeSystem) -> Self {
            let mut this = Self::new();
            for (ns, def_id) in ty_ctx.globals() {
                let ident = ty_ctx.name(ns, def_id);
                this.enter_child(ident.as_raw().clone(), ns, def_id);
            }
            this
        }

        pub fn current_depth(&self) -> Depth {
            Depth(self.names_in_scope.len())
        }

        /// Resolve an identifier at the current scope.
        pub fn resolve(&self, ident: &Ident, ns: Namespace) -> Result<DefId, ResolutionError> {
            self.names_by_ident[ns].get(ident)
                .and_then(|vec| vec.last().copied())  // the one that isn't shadowed
                .ok_or(ResolutionError)
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
    use crate::pos::{Sp};
    use crate::error::CompileError;

    /// Visitor for name resolution. Please don't use this directly,
    /// but instead call [`crate::passes::resolve_names::run`].
    pub struct Visitor<'ts> {
        resolver: NameResolver,
        errors: CompileError,
        ty_ctx: &'ts mut TypeSystem,
    }

    impl<'ts> Visitor<'ts> {
        pub fn new(ty_ctx: &'ts mut TypeSystem) -> Self {
            Visitor {
                resolver: NameResolver::init_from_ty_ctx(ty_ctx),
                errors: CompileError::new_empty(),
                ty_ctx,
            }
        }

        pub fn finish(self) -> Result<(), CompileError> {
            self.errors.into_result(())
        }
    }

    impl Visit for Visitor<'_> {
        fn visit_script(&mut self, x: &ast::Script) {
            // scan ahead for all function definitions
            let mut funcs_at_this_level = HashMap::new();
            for item in &x.items {
                if let ast::Item::Func { ident, .. } = &item.value {
                    // check for redefinitions
                    if let Some(old_span) = funcs_at_this_level.get(ident.as_raw()) {
                        self.errors.append(error!(
                            message("redefinition of func '{}'", ident),
                            primary(ident.span, "redefinition of function"),
                            secondary(old_span, "originally defined here"),
                        ));
                        // keep going; this is relatively harmless
                    }
                    funcs_at_this_level.insert(ident.as_raw().clone(), ident.span);

                    let def_id = self.ty_ctx.add_user_func(ident.clone());

                    // add it to the current scope
                    self.resolver.enter_child(ident.as_raw().clone(), Namespace::Funcs, def_id);
                }
            }

            ast::walk_script(self, x);
        }

        fn visit_item(&mut self, x: &Sp<ast::Item>) {
            match &x.value {
                | ast::Item::Func { params, code, .. }
                => {
                    if let Some(code) = code {
                        // we have to put the parameters in scope
                        let outer_scope_depth = self.resolver.current_depth();
                        for (ty_keyword, ident) in params {
                            let def_id = self.ty_ctx.add_local(ident.clone(), ty_keyword.ty());

                            self.resolver.enter_child(ident.as_raw().clone(), Namespace::Vars, def_id);
                        }
                        ast::walk_block(self, code);

                        self.resolver.return_to_ancestor(outer_scope_depth);
                    }
                },

                | ast::Item::AnmScript { .. }
                | ast::Item::Meta { .. }
                | ast::Item::FileList { .. }
                => ast::walk_item(self, x),
            }
        }

        fn visit_block(&mut self, x: &ast::Block) {
            let outer_scope_depth = self.resolver.current_depth();

            ast::walk_block(self, x);

            // make names defined within the block no longer resolvable
            self.resolver.return_to_ancestor(outer_scope_depth);
        }

        fn visit_stmt(&mut self, x: &Sp<ast::Stmt>) {
            match &x.body {
                ast::StmtBody::Declaration { keyword, vars } => {
                    let ty = keyword.ty();

                    for pair in vars {
                        let (var, init_value) = &pair.value;
                        if let ast::VarName::Normal { ident } = &var.value.name {
                            // a variable should not be allowed to appear in its own initializer, so walk the expression first.
                            if let Some(init_value) = init_value {
                                self.visit_expr(init_value);
                            }

                            let def_id = self.ty_ctx.add_local(sp!(var.span => ident.clone()), ty);

                            // record the variable in our resolution tree and enter its scope
                            // so that it can be used in future expressions
                            self.resolver.enter_child(ident.as_raw().clone(), Namespace::Vars, def_id);

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
                match self.resolver.resolve(ident, Namespace::Vars) {
                    Err(ResolutionError) => self.errors.append(error!(
                        message("unknown variable '{}'", ident),
                        primary(var, "not found in this scope"),
                    )),
                    Ok(def_id) => self.ty_ctx.resolutions.record_resolution(ident, def_id),
                };
            }
        }

        fn visit_expr(&mut self, expr: &Sp<ast::Expr>) {
            if let ast::Expr::Call { name, .. } = &expr.value {
                if let ast::CallableName::Normal { ident, .. } = &name.value {
                    match self.resolver.resolve(ident, Namespace::Funcs) {
                        Err(ResolutionError) => self.errors.append(error!(
                            message("unknown function '{}'", name),
                            primary(name, "not found in this scope"),
                        )),
                        Ok(def_id) => self.ty_ctx.resolutions.record_resolution(ident, def_id),
                    }
                }
            }
            ast::walk_expr(self, expr)
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

// =============================================================================

#[cfg(test)]
mod tests {
    use crate::pos::Files;
    use crate::parse::Parse;
    use crate::fmt::Format;
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
!ins_names
21 func21
"#;

    fn resolve<A: ast::Visitable + Parse>(text: &str) -> Result<A, (Files, CompileError)> {
        let mut files = Files::new();
        let mut ty_ctx = TypeSystem::new();
        ty_ctx.extend_from_eclmap(None, &Eclmap::parse(ECLMAP).unwrap()).unwrap();

        let mut parsed = files.parse::<A>("<input>", text.as_ref()).unwrap().value;
        crate::passes::resolve_names::assign_res_ids(&mut parsed, &mut ty_ctx).unwrap();
        match crate::passes::resolve_names::run(&parsed, &mut ty_ctx) {
            Ok(()) => Ok(parsed),
            Err(e) => Err((files, e)),
        }
    }

    fn resolve_reformat<A: ast::Visitable + Format + Parse>(text: &str) -> String {
        let parsed = resolve::<A>(text).unwrap_or_else(|(files, e)| panic!("{}", e.to_string(&files).unwrap()));

        crate::fmt::stringify_with(&parsed, crate::fmt::Config::new().show_res(true))
    }

    fn resolve_expect_err<A: ast::Visitable + Parse>(text: &str, expected: &str) -> String {
        let (files, err) = resolve::<A>(text).err().unwrap();
        let err_msg = err.to_string(&files).unwrap();
        assert!(err_msg.contains(expected), "{}", err_msg);
        err_msg
    }

    macro_rules! snapshot_test {
        ($name:ident = <$ty:ty> $source:literal) => {
            #[test]
            fn $name() { assert_snapshot!(resolve_reformat::<$ty>($source).trim()); }
        };
        ([expect_fail($expected:expr)] $name:ident = <$ty:ty> $source:literal) => {
            #[test]
            fn $name() { assert_snapshot!(resolve_expect_err::<$ty>($source, $expected).trim()); }
        };
    }

    snapshot_test!(basic_local = <ast::Block> r#"{
        int a = 3;
        int b = a + a;  // should use same `a`
    }"#);

    snapshot_test!(shadow_local = <ast::Block> r#"{
        int a = 3;
        if (true) {
            int a = 4;
            int b = a * a;  // should use inner `a`
        }
        int c = a * a;  // should use outer `a`
        if (true) {
            int a = 4;  // should be different from other inner `a`
            int b = a * a;  // should use new inner `a`
        }
    }"#);

    snapshot_test!([expect_fail("in this scope")] err_adjacent_scope = <ast::Block> r#"{
        if (true) {
            int a = 4;
            int b = a * 3;
        }
        if (true) {
            int b = a * 3;  // should fail at `a`
        }
    }"#);

    snapshot_test!([expect_fail("in this scope")] err_after_scope_end = <ast::Block> r#"{
        if (true) {
            int a = 4;
            int b = a * 3;
        }
        int b = a;  // should fail at `a`
    }"#);

    snapshot_test!(basic_reg_alias = <ast::Block> r#"{
        ins_21(A, X);
    }"#);

    snapshot_test!(shadow_reg_alias = <ast::Block> r#"{
        ins_21(A, X);
        if (true) {
            float A = 4.0;  // should be different `A`
            float b = A;
        }
        ins_21(A, X);  // should be original `A`
    }"#);

    snapshot_test!(basic_func = <ast::Script> r#"
    int foo(int x) {
        return x;
    }

    script script0 {
        foo(x);  // should match `foo` definition
    }"#);

    snapshot_test!(basic_func_out_of_order = <ast::Script> r#"
    script script0 {
        int x = 3;
        foo(x);  // should match `foo` definition
    }

    int foo(int x) {
        return x;
    }
    "#);

    snapshot_test!([expect_fail("redefinition")] err_func_redefinition = <ast::Script> r#"
    int foo(int x) {
        return x;
    }

    int foo(float y) {
        return y;
    }
    "#);

    #[should_panic(expected = "resolved multiple times")]
    #[test]
    fn panics_on_cloned_res() {
        let mut files = Files::new();
        let mut ty_ctx = TypeSystem::new();
        ty_ctx.extend_from_eclmap(None, &Eclmap::parse(ECLMAP).unwrap()).unwrap();

        let mut def = files.parse::<ast::Stmt>("<input>", b"  int x = 2;  ").unwrap();
        let mut cloned = files.parse::<ast::Stmt>("<input>", b"  x = 3;  ").unwrap();
        crate::passes::resolve_names::assign_res_ids(&mut def, &mut ty_ctx).unwrap();
        crate::passes::resolve_names::assign_res_ids(&mut cloned, &mut ty_ctx).unwrap();

        let block = ast::Block(vec![def, cloned.clone(), cloned]);

        crate::passes::resolve_names::run(&block, &mut ty_ctx).unwrap();
    }
}
