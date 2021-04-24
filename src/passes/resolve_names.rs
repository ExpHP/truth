use crate::ast;
use crate::pos::Sp;
use crate::context::CompilerContext;
use crate::error::{ErrorReported, ErrorFlag};
use crate::game::InstrLanguage;
use crate::ident::ResIdent;

/// Assign [`ResId`]s to names in a script parsed from text.
///
/// This is an extremely early preprocessing pass, preferably done immediately after parsing.
/// (it can't be done during parsing because parsing should not require access to [`CompilerContext`])
pub fn assign_res_ids<A: ast::Visitable>(ast: &mut A, ctx: &mut CompilerContext<'_>) -> Result<(), ErrorReported> {
    let mut v = AssignResIdsVisitor { ctx };
    ast.visit_mut_with(&mut v);
    Ok(())
}

/// Assign [`InstrLanguage`]s to called functions and variables in a script parsed from text.
///
/// Basically, there are a number of passes that need to know what language each sub compiles to, and it is not easy
/// to factor out the logic that decides this in a way reusable by multiple `Visit` impls.  Therefore, places were added
/// to the AST that store language tags where useful, and this early pass is responsible for filling those tags.
///
/// The logic is:
/// * Tokens within `script`s and non-`const` functions will be painted with the given [`InstrLanguage`].
/// * Tokens inside `timeline` items will be painted with [`InstrLanguage::Timeline`] instead.
/// * Tokens inside `const` exprs and `const` functions will not be painted with any language.
///   Any raw syntax (`ins_23`, `REG[10004]`) in these locations will produce errors.
///
/// If called directly on [`ast::Block`] instead of a script file, it is assumed to be the body of a `script` and thus paints
/// with the specified language.  (this behavior is for use by tests)
pub fn assign_languages<A: ast::Visitable>(ast: &mut A, primary_language: InstrLanguage, ctx: &mut CompilerContext<'_>) -> Result<(), ErrorReported> {
    let mut v = AssignLanguagesVisitor {
        ctx,
        primary_language,
        language_stack: vec![Some(primary_language)],
        errors: ErrorFlag::new(),
    };
    ast.visit_mut_with(&mut v);
    v.errors.into_result(())
}

/// Resolve names in a script parsed from text.
///
/// All [`ResId`]s will be mapped to a unique [`DefId`] during this pass.  These mappings are available
/// through the [`crate::resolve::Resolutions`] type.
///
/// While some definitions are recorded before this (notably eclmap stuff, and things from meta),
/// the majority of definitions are discovered during this pass; this includes user-defined functions,
/// consts, and locals.  All of these will receive [`DefId`]s, and their names and type information
/// will be recorded in [`crate::context::Defs`].
///
/// **Note:** It is worth noting that that this pass takes `&A`; i.e. it **does not** modify the AST.
/// This means that, if you clone an AST node and then run name resolution on the original, then the
/// names will also be resolved in the copy.  This property is important to helping make some parts
/// of `const` evaluation tractable.  (especially consts defined in meta, like sprite ids)
pub fn run<A: ast::Visitable>(ast: &A, ctx: &mut CompilerContext<'_>) -> Result<(), ErrorReported> {
    let mut v = crate::resolve::ResolveVarsVisitor::new(ctx);
    ast.visit_with(&mut v);
    v.finish()
}

/// Convert any register aliases and instruction aliases to `REG[10000]` and `ins_32` syntax.
///
/// Requires name resolution to have been performed.
pub fn aliases_to_raw<A: ast::Visitable>(ast: &mut A, ctx: &CompilerContext<'_>) -> Result<(), ErrorReported> {
    let mut v = AliasesToRawVisitor { ctx };
    ast.visit_mut_with(&mut v);
    Ok(())
}

/// Convert any raw register references (e.g. `REG[10000]`) and raw instructions (`ins_32`) to aliases
/// when they are available.
///
/// When it converts a register to an alias, it will strip the type sigil if it isn't needed.
/// (sigils are left on registers it doesn't convert
///
/// FIXME: Stripping the sigil seems like a surprising side-effect.
///  Or rather, while it's true that we DO want redundant sigils on REG and not on other things,
///  this particular function is an odd place to implement this behavior!
///  (it's only here for historical reasons, back when raw registers always had a `VarReadType`)
///  &nbsp;
///  I did try separating this into two passes (one that switches to aliases, another that strips sigils
///  from non-`REG`s) but ran into https://github.com/ExpHP/truth/issues/13 when the second pass
///  encountered things like `sprite24`.
pub fn raw_to_aliases<A: ast::Visitable>(ast: &mut A, ctx: &CompilerContext<'_>) -> Result<(), ErrorReported> {
    let mut v = RawToAliasesVisitor { ctx };
    ast.visit_mut_with(&mut v);
    Ok(())
}

// =============================================================================

struct AssignResIdsVisitor<'a, 'ctx> {
    ctx: &'a mut CompilerContext<'ctx>,
}

impl ast::VisitMut for AssignResIdsVisitor<'_, '_> {
    fn visit_res_ident(&mut self, ident: &mut ResIdent) {
        ident.res.get_or_insert_with(|| self.ctx.resolutions.fresh_res());
    }
}

struct AliasesToRawVisitor<'a, 'ctx> {
    ctx: &'a CompilerContext<'ctx>,
}

impl ast::VisitMut for AliasesToRawVisitor<'_, '_> {
    fn visit_var(&mut self, var: &mut Sp<ast::Var>) {
        if let ast::VarName::Normal { .. } = &var.name {
            if let Ok((language, reg)) = self.ctx.var_reg_from_ast(&var.name) {
                var.name = ast::VarName::Reg { reg, language: Some(language) };
            }
        }
    }

    fn visit_expr(&mut self, expr: &mut Sp<ast::Expr>) {
        if let ast::Expr::Call { name, .. } = &mut expr.value {
            if let Ok((language, opcode)) = self.ctx.func_opcode_from_ast(name) {
                name.value = ast::CallableName::Ins { opcode, language: Some(language) };
            }
        }
        ast::walk_expr_mut(self, expr);
    }
}

struct RawToAliasesVisitor<'a, 'ctx> {
    ctx: &'a CompilerContext<'ctx>,
}

impl ast::VisitMut for RawToAliasesVisitor<'_, '_> {
    fn visit_var(&mut self, var: &mut Sp<ast::Var>) {
        if let ast::VarName::Reg { reg, language, .. } = var.name {
            let language = language.expect("must run assign_languages pass!");
            var.name = self.ctx.reg_to_ast(language, reg);

            // did it succeed?
            if var.name.is_named() {
                self.ctx.var_simplify_ty_sigil(&mut var.value);
            }
        }
    }

    fn visit_expr(&mut self, expr: &mut Sp<ast::Expr>) {
        if let ast::Expr::Call { name, .. } = &mut expr.value {
            if let ast::CallableName::Ins { opcode, language, .. } = name.value {
                let language = language.expect("must run assign_languages pass!");
                name.value = self.ctx.ins_to_ast(language, opcode);
            }
        }
        ast::walk_expr_mut(self, expr);
    }
}

struct AssignLanguagesVisitor<'a, 'ctx> {
    ctx: &'a CompilerContext<'ctx>,
    primary_language: InstrLanguage,
    language_stack: Vec<Option<InstrLanguage>>,
    errors: ErrorFlag,
}

impl ast::VisitMut for AssignLanguagesVisitor<'_, '_> {
    fn visit_var(&mut self, var: &mut Sp<ast::Var>) {
        let language_dest = match &mut var.name {
            ast::VarName::Reg { language, .. } => language,
            ast::VarName::Normal { language_if_reg, .. } => language_if_reg,
        };
        *language_dest = self.language_stack.last().expect("empty stack?!").clone();

        if let ast::VarName::Reg { language: None, .. } = var.name {
            self.errors.set(self.ctx.emitter.emit(error!(
                message("raw register in const context"),
                primary(var, "forbidden in this context"),
            )));
        }
    }

    fn visit_callable_name(&mut self, name: &mut Sp<ast::CallableName>) {
        let language_dest = match &mut name.value {
            ast::CallableName::Ins { language, .. } => language,
            ast::CallableName::Normal { language_if_ins, .. } => language_if_ins,
        };
        *language_dest = self.language_stack.last().expect("empty stack?!").clone();

        if let ast::CallableName::Ins { language: None, .. } = name.value {
            self.errors.set(self.ctx.emitter.emit(error!(
                message("raw instruction in const context"),
                primary(name, "forbidden in this context"),
            )));
        }
    }

    fn visit_item(&mut self, item: &mut Sp<ast::Item>) {
        match &mut item.value {
            | ast::Item::Func { qualifier: Some(sp_pat![token![const]]), .. }
            | ast::Item::ConstVar { .. }
            | ast::Item::Meta { .. }
            => {
                self.language_stack.push(None);
                ast::walk_item_mut(self, item);
                assert_eq!(self.language_stack.pop().unwrap(), None, "unbalanced stack usage!");
            },

            | ast::Item::Timeline { .. }
            => {
                self.language_stack.push(Some(InstrLanguage::Timeline));
                ast::walk_item_mut(self, item);
                assert_eq!(self.language_stack.pop().unwrap(), Some(InstrLanguage::Timeline), "unbalanced stack usage!");
            },

            _ => {
                self.language_stack.push(Some(self.primary_language));
                ast::walk_item_mut(self, item);
                assert_eq!(self.language_stack.pop().unwrap(), Some(self.primary_language), "unbalanced stack usage!");
            },
        }
    }
}
