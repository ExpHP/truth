use crate::ast;
use crate::error::ErrorReported;
use crate::context::CompilerContext;
use crate::llir::DecompileOptions;

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
pub mod semantics {
    //! Passes that run over the AST to produce a map of information about each node.
    pub mod time_and_difficulty;
}
pub mod evaluate_const_vars {
    //! Pass for checking and computing all const vars.

    use super::*;

    /// This evaluates and caches the value of all `const` vars that have been defined on the global context.
    /// It is required for const simplification, which only looks at the cache.
    pub fn run(ctx: &mut CompilerContext) -> Result<(), ErrorReported> {
        ctx.consts.evaluate_all_deferred(&ctx.defs, &ctx.resolutions, &ctx.emitter)
    }
}

/// Run decompilation passes common to all languages.
pub fn postprocess_decompiled<V: ast::Visitable + std::fmt::Debug>(
    script: &mut V,
    ctx: &CompilerContext,
    decompile_options: &DecompileOptions,
) -> Result<(), ErrorReported> {
    resolve_names::raw_to_aliases(script, ctx)?;

    if decompile_options.blocks {
        decompile_loop::decompile_if_else(script)?;
        decompile_loop::decompile_loop(script)?;
        unused_labels::run(script)?;
    }

    Ok(())
}
