use crate::ast::{self, VisitMut};
use crate::error::CompileError;
use crate::type_system::TypeSystem;

pub mod const_simplify;
pub mod unused_labels;
pub mod compile_loop;
pub mod decompile_loop;

pub enum DecompileKind { Simple, Fancy }

pub fn postprocess_decompiled(script: &mut ast::Script, ty_ctx: &TypeSystem, decompile_kind: DecompileKind) -> Result<(), CompileError> {
    match decompile_kind {
        DecompileKind::Simple => postprocess_decompiled_simple(script, ty_ctx),
        DecompileKind::Fancy => postprocess_decompiled_fancy(script, ty_ctx),
    }
}

pub fn postprocess_decompiled_fancy(script: &mut ast::Script, ty_ctx: &TypeSystem) -> Result<(), CompileError> {
    if std::env::var("_TRUTH_DEBUG__MINIMAL").ok().as_deref() == Some("1") {
        return postprocess_decompiled_simple(script, ty_ctx);
    }

    ty_ctx.unresolve_names(script, false)?;

    let mut v = decompile_loop::Visitor::new();
    v.visit_script(script);
    v.finish()?;

    let mut v = unused_labels::Visitor::new();
    v.visit_script(script);
    v.finish()?;

    Ok(())
}

pub fn postprocess_decompiled_simple(script: &mut ast::Script, ty_ctx: &TypeSystem) -> Result<(), CompileError> {
    ty_ctx.unresolve_names(script, false)?;

    let mut v = unused_labels::Visitor::new();
    v.visit_script(script);
    v.finish()?;

    Ok(())
}
