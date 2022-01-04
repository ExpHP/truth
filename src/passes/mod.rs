use crate::ast;
use crate::error::ErrorReported;
use crate::context::CompilerContext;
use crate::llir::DecompileOptions;

pub mod const_simplify;
pub mod unused_labels;
pub mod desugar_blocks;
pub mod decompile_loop;
pub mod resolution;
pub mod type_check;
pub mod validate_difficulty;
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

    /// A value returned by this compiler pass, as a sort of "proof" that it has been run.
    ///
    /// If a function requires the const var evaluation pass to have already been run, it may
    /// take this object as an argument to encode this requirement within the type system.
    #[derive(Debug, Copy, Clone)]
    pub struct Proof { _priv: () }

    /// This evaluates and caches the value of all `const` vars that have been defined on the global context.
    /// It is required for const simplification, which only looks at the cache.
    pub fn run(ctx: &mut CompilerContext) -> Result<Proof, ErrorReported> {
        ctx.consts.evaluate_all_deferred(&ctx.defs, &ctx.resolutions, &ctx.emitter)?;

        Ok(Proof { _priv: () })
    }
}

/// Run decompilation passes common to all languages.
pub fn postprocess_decompiled<V: ast::Visitable + std::fmt::Debug>(
    script: &mut V,
    ctx: &mut CompilerContext,
    decompile_options: &DecompileOptions,
) -> Result<(), ErrorReported> {
    resolution::raw_to_aliases(script, ctx)?;

    if decompile_options.blocks {
        // decompile loops before if/else for better detection of continue/break
        decompile_loop::decompile_loop(script, ctx)?;
        decompile_loop::decompile_if_else(script, ctx)?;
        decompile_loop::decompile_break(script, ctx)?;
        unused_labels::run(script)?;
    }

    resolution::check_loop_id_integrity(script, ctx)?;

    Ok(())
}
