use crate::ast;
use crate::error::CompileError;
use crate::type_system::TypeSystem;

pub mod const_simplify;
pub mod unused_labels;
pub mod desugar_blocks;
pub mod decompile_loop;
pub mod resolve_names;

pub enum DecompileKind { Simple, Fancy }

pub fn postprocess_decompiled<V: ast::Visitable+ std::fmt::Debug>(script: &mut V, ty_ctx: &TypeSystem, decompile_kind: DecompileKind) -> Result<(), CompileError> {
    match decompile_kind {
        DecompileKind::Simple => postprocess_decompiled_simple(script, ty_ctx),
        DecompileKind::Fancy => postprocess_decompiled_fancy(script, ty_ctx),
    }
}

pub fn postprocess_decompiled_fancy<V: ast::Visitable + std::fmt::Debug>(script: &mut V, ty_ctx: &TypeSystem) -> Result<(), CompileError> {
    if std::env::var("_TRUTH_DEBUG__MINIMAL").ok().as_deref() == Some("1") {
        return postprocess_decompiled_simple(script, ty_ctx);
    }

    resolve_names::unresolve(script, false, ty_ctx)?;
    decompile_loop::decompile_if_else(script)?;
    decompile_loop::decompile_loop(script)?;
    unused_labels::run(script)?;

    Ok(())
}

pub fn postprocess_decompiled_simple<V: ast::Visitable>(script: &mut V, ty_ctx: &TypeSystem) -> Result<(), CompileError> {
    resolve_names::unresolve(script, false, ty_ctx)?;

    Ok(())
}
