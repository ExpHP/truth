use crate::ast::{self, VisitMut};
use crate::error::CompileError;

pub mod const_simplify;
pub mod unused_labels;
pub mod compile_loop;
pub mod decompile_loop;
pub mod resolve_vars;

pub enum DecompileKind { Simple, Fancy }

pub fn postprocess_decompiled(script: &mut ast::Script, decompile_kind: DecompileKind) -> Result<(), CompileError> {
    match decompile_kind {
        DecompileKind::Simple => postprocess_decompiled_simple(script),
        DecompileKind::Fancy => postprocess_decompiled_fancy(script),
    }
}

pub fn postprocess_decompiled_fancy(script: &mut ast::Script) -> Result<(), CompileError> {
    if std::env::var("_TRUTH_DEBUG__MINIMAL").ok().as_deref() != Some("1") {
        return postprocess_decompiled_simple(script);
    }

    let mut v = decompile_loop::Visitor::new();
    v.visit_script(script);
    v.finish()?;

    let mut v = unused_labels::Visitor::new();
    v.visit_script(script);
    v.finish()?;

    Ok(())
}

pub fn postprocess_decompiled_simple(script: &mut ast::Script) -> Result<(), CompileError> {
    let mut v = unused_labels::Visitor::new();
    v.visit_script(script);
    v.finish()?;

    Ok(())
}
