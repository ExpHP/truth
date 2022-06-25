use std::collections::HashSet;

use crate::ast;
use crate::pos::Sp;
use crate::ident::Ident;
use crate::diagnostic::Emitter;
use crate::error::{ErrorReported, ErrorFlag};

/// A structure representing the union of the text file layouts for all scripting languages.
///
/// After script is parsed into a `Vec<`[`ast::Item`]`>`, it is quickly converted into one of these.
/// This process consolidates a lot of code that e.g. looks for duplicate `script` names or errors
/// on unsupported syntax in a file.  By fully destructuring it in code, you can get "unused" warnings
/// which will help reduce bugs where a format silently ignores a certain type of item.
///
/// When [printed][`crate::fmt`] or [traversed][`crate::ast::Visit`], the items may print in a different
/// order from the original AST.
#[derive(Debug, Clone, Default)]
pub struct ScriptFile {
    pub meta: Option<ast::ItemMeta>,
    pub toplevel_consts: Vec<ast::ItemConstVar>,
    /// `script`s not underneath an `entry`.
    pub toplevel_scripts: Vec<ast::ItemScript>,
    /// Functions not defined inside a block of code.
    pub toplevel_funcs: Vec<ast::ItemFunc>,
    pub mapfiles: Vec<ast::ItemPragma>,
    pub image_sources: Vec<ast::ItemPragma>,
    pub entries: Vec<Entry>,
}

#[derive(Debug, Clone)]
pub struct Entry {
    pub meta: ast::ItemMeta,
    pub scripts: Vec<ast::ItemScript>,
}

impl ScriptFile {
    pub fn from_ast(items: Vec<Sp<ast::Item>>, emitter: &impl Emitter) -> Result<ScriptFile, ErrorReported> {
        let mut errors = ErrorFlag::new();
        let mut output = ScriptFile::default();
        let mut current_entry = None;

        let mut script_checker = RedefinitionChecker::new(emitter, "script");
        let mut function_checker = RedefinitionChecker::new(emitter, "function");

        for item in items {
            match item.value {
                ast::Item::Pragma(pragma@ast::ItemPragma { kind: sp_pat!(ast::PragmaKindKeyword::Mapfile), .. }) => {
                    output.mapfiles.push(pragma);
                },
                ast::Item::Pragma(pragma@ast::ItemPragma { kind: sp_pat!(ast::PragmaKindKeyword::ImageSource), .. }) => {
                    output.image_sources.push(pragma);
                },
                ast::Item::Meta(meta@ast::ItemMeta { keyword: sp_pat![kw_span => token![meta]], .. }) => {
                    if let Some(prev_meta) = output.meta.replace(meta) {
                        errors.set(emitter.emit(error!(
                            message("'meta' supplied multiple times"),
                            secondary(prev_meta.keyword, "previously supplied here"),
                            primary(kw_span, "duplicate 'meta'"),
                        )));
                    }
                },
                ast::Item::Meta(meta@ast::ItemMeta { keyword: sp_pat![kw_span => token![entry]], .. }) => {
                    // Begin a new entry
                    if let Some(prev_entry) = current_entry.take() {
                        output.entries.push(prev_entry);
                    }
                    current_entry = Some(Entry { meta, scripts: vec![] });
                },
                ast::Item::Script(script) => {
                    if let Err(e) = script_checker.check_for_redefinition(&script.ident) {
                        errors.set(e);
                    }
                    match current_entry.as_mut() {
                        Some(entry) => entry.scripts.push(script),
                        None => output.toplevel_scripts.push(script),
                    }
                },
                ast::Item::ConstVar(item) => {
                    output.toplevel_consts.push(item);
                },
                ast::Item::Func(item) => {
                    if let Err(e) = function_checker.check_for_redefinition(&sp!(item.ident.span => item.ident.as_raw().clone())) {
                        errors.set(e);
                    }
                    output.toplevel_funcs.push(item);
                },
            }
        }

        errors.into_result(output)
    }
}

struct RedefinitionChecker<'a> {
    emitter: &'a dyn Emitter,
    noun: &'a str,
    seen: HashSet<Sp<Ident>>,
}

impl<'a> RedefinitionChecker<'a> {
    fn new(emitter: &'a dyn Emitter, noun: &'a str) -> Self {
        RedefinitionChecker { emitter, noun, seen: Default::default() }
    }

    fn check_for_redefinition(&mut self, ident: &Sp<Ident>) -> Result<(), ErrorReported> {
        if let Some(prev) = self.seen.replace(ident.clone()) {
            return Err(self.emitter.as_sized().emit(error!(
                message("redefinition of {} '{ident}'", self.noun),
                primary(ident, ""),
                secondary(prev, "previously defined here"),
            )));
        }
        Ok(())
    }
}

pub fn meta_not_supported(emitter: &impl Emitter, meta: &Option<ast::ItemMeta>) -> Result<(), ErrorReported> {
    if let Some(ast::ItemMeta { keyword, .. }) = meta {
        return Err(emitter.emit(error!(
            message("unexpected '{keyword}'"),
            primary(keyword, "not valid in this format"),
        )))
    }
    Ok(())
}

pub fn scripts_not_supported(emitter: &impl Emitter, scripts: &[ast::ItemScript], note: Option<String>) -> Result<(), ErrorReported> {
    if let Some(ast::ItemScript { keyword, .. }) = scripts.iter().next() {
        let mut diag = error!(
            message("unexpected 'script'"),
            primary(keyword, "not valid in this format"),
        );
        if let Some(note) = note {
            diag.note(note);
        }
        return Err(emitter.emit(diag));
    }
    Ok(())
}

pub fn functions_not_supported(emitter: &impl Emitter, funcs: &[ast::ItemFunc]) -> Result<(), ErrorReported> {
    if let Some(ast::ItemFunc { ty_keyword, .. }) = funcs.iter().next() {
        return Err(emitter.emit(error!(
            message("unexpected function definition"),
            primary(ty_keyword, "not valid in this format"),
        )))
    }
    Ok(())
}

pub fn pragma_not_supported(emitter: &impl Emitter, pragmas: &[ast::ItemPragma], note: Option<String>) -> Result<(), ErrorReported> {
    if let Some(ast::ItemPragma { kind, .. }) = pragmas.iter().next() {
        return Err(emitter.emit(error!(
            message("unexpected 'pragma {kind}'"),
            primary(kind, "not valid in this format"),
        )));
    }
    Ok(())
}
