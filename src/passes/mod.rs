use crate::ast;
use crate::error::CompileError;
use crate::context::CompilerContext;

pub mod const_simplify;
pub mod unused_labels;
pub mod desugar_blocks;
pub mod decompile_loop;
pub mod resolve_names;
pub mod type_check;
pub mod debug {
    //! Passes that exist for **debugging/testing purposes only.**
    pub mod make_idents_unique;
}
pub mod evaluate_const_vars {
    //! Pass for checking and computing all const vars.

    use super::*;

    /// This evaluates and caches the value of all `const` vars that have been defined on the global context.
    /// It is required for const simplification, which only looks at the cache.
    pub fn run(ctx: &mut CompilerContext) -> Result<(), CompileError> {
        ctx.consts.evaluate_all_deferred(&ctx.defs, &ctx.resolutions)
    }
}

pub enum DecompileKind { Simple, Fancy }

pub fn postprocess_decompiled<V: ast::Visitable+ std::fmt::Debug>(script: &mut V, ctx: &CompilerContext, decompile_kind: DecompileKind) -> Result<(), CompileError> {
    match decompile_kind {
        DecompileKind::Simple => postprocess_decompiled_simple(script, ctx),
        DecompileKind::Fancy => postprocess_decompiled_fancy(script, ctx),
    }
}

pub fn postprocess_decompiled_fancy<V: ast::Visitable + std::fmt::Debug>(script: &mut V, ctx: &CompilerContext) -> Result<(), CompileError> {
    if std::env::var("_TRUTH_DEBUG__MINIMAL").ok().as_deref() == Some("1") {
        return postprocess_decompiled_simple(script, ctx);
    }

    resolve_names::raw_to_aliases(script, ctx)?;
    decompile_loop::decompile_if_else(script)?;
    decompile_loop::decompile_loop(script)?;
    unused_labels::run(script)?;

    Ok(())
}

pub fn postprocess_decompiled_simple<V: ast::Visitable>(script: &mut V, ctx: &CompilerContext) -> Result<(), CompileError> {
    resolve_names::raw_to_aliases(script, ctx)?;
    Ok(())
}
