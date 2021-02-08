use std::fmt;
use std::num::NonZeroU64;
use std::collections::HashMap;
use crate::ident::{Ident, ResIdent};
use crate::type_system::{ScalarType, TypeSystem};

// FIXME rename to crate::resolve

/// Represents an identifier that has been uniquely resolved according to its scope.
///
/// These are the disambiguating id numbers that get stored in [`ResIdent`] to make them
/// unique. So long as they are resolved using the same [`TypeSystem`], no two identifiers
/// referring to different things will ever have the same [`ResolveId`]. This is true even if
/// the identifiers are different or live in different namespaces (i.e. no additional information
/// beyond the [`ResolveId`] is necessary to uniquely refer to a named entity).
///
/// FIXME: Currently `ResolveId` is also used for some things that don't have resolvable idents
///        (such as raw register references) because it is more generally used as an key for
///        `TypeSystem`.  Maybe we can stop doing this now that the whole VarId mess has been
///        cleaned up?  Not sure.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ResolveId(pub NonZeroU64);

// FIXME move to crate::llir or crate::type_system
/// The number used to access a register as an instruction argument.  This uniquely identifies a register.
///
/// For instance, in TH17 ECL, the `TIME` register has an id of `-9988`.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RegId(pub i32);

impl From<i32> for RegId {
    fn from(x: i32) -> Self { RegId(x) }
}

/// Identifies a scope in which a set of names are visible.
///
/// Effectively, this is the index into the list of nodes for the "scope tree."
#[derive(Copy, Clone, PartialEq, Eq, Hash, Default)]
struct ScopeId(
    // we define a new scope for every name.  None is the empty scope.
    Option<ResolveId>,
);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[derive(enum_map::Enum)]
pub enum Namespace { Vars }

use name_resolver::{NameResolver, ResolutionError, Depth};
mod name_resolver {
    use super::*;

    /// A helper whose purpose is to incrementally track which [`ResolveId`] each [`Ident`]
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
    /// (if we did construct this tree then basically `Option<ResolveId>` could double as a "scope index" into the
    /// flattened list of tree nodes; see https://github.com/ExpHP/truth/blob/e7d5e303b6309ef6101faf87ae67c7ff67034535/src/var.rs#L61-L233
    /// for an older design, where an explicit tree was stored in `Variables`.  This design would not be convenient
    /// right now because not all things with ResolveIds have resolvable idents)
    #[derive(Debug, Clone)]
    pub(super) struct NameResolver {
        /// This contains the data we need from each node along our current path from the root of the scope tree;
        /// i.e. it has an entry for every name *currently in scope.*  (including ones that are shadowed)
        names_in_scope: Vec<(Namespace, Ident, ResolveId)>,

        /// An incrementally-maintained reverse mapping that lets us resolve variables in O(1).
        /// The last id in each vec is the one that the identifier currently resolves to;
        /// the ones before it are shadowed.
        names_by_ident: enum_map::EnumMap<Namespace, HashMap<Ident, Vec<ResolveId>>>,
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
            for (ns, res) in ty_ctx.globals() {
                if let Some(ident) = ty_ctx.resolvable_ident(ns, res) {
                    this.enter_child(ident.clone(), ns, res);
                }
            }
            this
        }

        pub fn current_depth(&self) -> Depth {
            Depth(self.names_in_scope.len())
        }

        /// Resolve an identifier at the current scope.
        pub fn resolve(&self, ident: &mut ResIdent, ns: Namespace) -> Result<(), ResolutionError> {
            if ident.res().is_some() {
                // already resolved for some reason (multiple calls to resolution pass?).
                // we'll panic for now just to be safe, but if we want to allow this in the future
                //   we can easily just return Ok here.
                panic!("{} was already resolved?!", ident);
            }
            let res  = {
                self.names_by_ident[ns].get(ident.as_raw())
                    .and_then(|vec| vec.last().copied())  // the one that isn't shadowed
                    .ok_or(ResolutionError)?
            };
            ident.set_res(res);
            Ok(())
        }

        /// Travel from the current scope into a direct child by adding a single variable
        /// into the current scope.
        pub fn enter_child(&mut self, ident: Ident, ns: Namespace, res: ResolveId) {
            self.names_in_scope.push((ns, ident.clone(), res));
            self.names_by_ident[ns].entry(ident.clone()).or_default().push(res);
        }

        /// Travel from the current scope into one that is (not necessarily strictly) above it in the tree.
        pub fn return_to_ancestor(&mut self, ancestor_depth: Depth) {
            while self.current_depth().0 > ancestor_depth.0 {
                let (ns, ident, res) = self.names_in_scope.pop().unwrap();
                let popped_res = self.names_by_ident[ns].get_mut(&ident).unwrap().pop().unwrap();
                assert_eq!(res, popped_res, "(bug!) internal inconsistency!");
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
        stack: Vec<BlockState>,
        errors: CompileError,
        ty_ctx: &'ts mut TypeSystem,
    }

    pub struct BlockState {
        /// Depth in the scope tree that we will ascend back to upon leaving the block.
        outer_scope_depth: Depth,

        /// List of local variables whose scope end at the end of this block.
        ///
        /// We track this actually not for name resolution purposes, but so that "ScopeEnd"
        /// statements can be inserted (which are used during lowering to free resources
        /// like registers that are held by the locals)
        locals_declared_at_this_level: Vec<ResolveId>,
    }

    impl<'ts> Visitor<'ts> {
        pub fn new(ty_ctx: &'ts mut TypeSystem) -> Self {
            Visitor {
                resolver: NameResolver::init_from_ty_ctx(ty_ctx),
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
                outer_scope_depth: self.resolver.current_depth(),
                locals_declared_at_this_level: vec![],
            });

            ast::walk_block_mut(self, x);

            let popped = self.stack.pop().expect("(BUG!) unbalanced scope_stack usage!");

            // emit statements that will free resources during lowering
            for res in popped.locals_declared_at_this_level {
                let span = x.last_stmt().span.end_span();
                x.0.push(sp!(span => ast::Stmt {
                    time: x.end_time(),
                    body: ast::StmtBody::ScopeEnd(res),
                }));
            }

            // make names defined within the block no longer resolvable
            self.resolver.return_to_ancestor(popped.outer_scope_depth);
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
                        if let ast::Var::Named { ty_sigil, ident } = &mut var.value {
                            assert!(ty_sigil.is_none());

                            // a variable should not be allowed to appear in its own initializer, so walk the expression first.
                            if let Some(init_value) = init_value {
                                self.visit_expr(init_value);
                            }

                            // assign the ident a new resolution id
                            *ident = self.ty_ctx.add_local(sp!(var.span => ident.clone()), ty).value;

                            // record the variable in our resolution tree and enter its scope
                            // so that it can be used in future expressions
                            self.resolver.enter_child(ident.as_raw().clone(), Namespace::Vars, ident.expect_res());

                            self.stack.last_mut().expect("(bug?) empty stack?")
                                .locals_declared_at_this_level.push(ident.expect_res());
                        }
                    }
                }
                _ => ast::walk_stmt_mut(self, x),
            }
        }

        fn visit_var(&mut self, var: &mut Sp<ast::Var>) {
            if let ast::Var::Named { ref mut ident, .. } = var.value {
                match self.resolver.resolve(ident, Namespace::Vars) {
                    Err(ResolutionError) => self.errors.append(error!(
                        message("unknown variable '{}'", ident),
                        primary(var, "not found in this scope"),
                    )),
                    Ok(()) => {},
                };
            }
        }

        fn visit_expr(&mut self, expr: &mut Sp<ast::Expr>) {
            // FIXME XXX  this is just a hack to get tests working,
            //            name resolution will be getting an update very soon
            if let ast::Expr::Call { ident, .. } = &expr.value {
                // currently ins_XXX names never get added, so add the ones that get called
                if let Some(opcode) = ident.as_ins() {
                    self.ty_ctx.add_global_ins_alias(opcode, crate::ident::ResIdent::from(ident.value.clone()));
                }
            }
            ast::walk_expr_mut(self, expr)
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

impl fmt::Debug for ResolveId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl fmt::Display for ResolveId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

// =============================================================================

#[cfg(test)]
mod tests {
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

    fn resolve(text: &str) -> Result<ast::Block, (Files, CompileError)> {
        let mut files = Files::new();
        let mut ty_ctx = TypeSystem::new();
        ty_ctx.extend_from_eclmap(None, &Eclmap::parse(ECLMAP).unwrap()).unwrap();

        let mut parsed_block = files.parse::<ast::Block>("<input>", text.as_ref()).unwrap().value;
        match crate::passes::resolve_names::run(&mut parsed_block, &mut ty_ctx) {
            Ok(()) => Ok(parsed_block),
            Err(e) => Err((files, e)),
        }
    }

    fn resolve_reformat(text: &str) -> String {
        let parsed_block = resolve(text).unwrap();
        crate::fmt::stringify_with(&parsed_block, crate::fmt::Config::new().show_res(true))
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

    // FIXME rename to basic_reg_alias
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
}
