
use enum_map::{enum_map, EnumMap};
use crate::ast::{self, Visit, VisitMut};
use crate::error::CompileError;
use crate::pos::Sp;
use crate::type_system::{TypeSystem, ScalarType};

pub struct Visitor<'ts> {
    general_use_regs: EnumMap<ScalarType, Vec<i32>>,
    unused_regs_stack: Vec<EnumMap<ScalarType, Vec<i32>>>, // stack for nested function bodies
    ty_ctx: &'ts TypeSystem,
    errors: CompileError,
}

impl<'ts> Visitor<'ts> {
    pub fn new(general_use_regs: EnumMap<ScalarType, Vec<i32>>, ty_ctx: &'ts TypeSystem) -> Self {
        Visitor {
            general_use_regs, ty_ctx,
            unused_regs_stack: vec![],
            errors: CompileError::new_empty(),
        }
    }

    pub fn finish(self) -> Result<(), CompileError> {
        self.errors.into_result(())
    }
}

impl VisitMut for Visitor<'_> {
    fn visit_func_body(&mut self, func_body: &mut ast::Block) {
        let used_regs = get_used_regs(func_body, self.ty_ctx);

        let mut unused_regs = self.general_use_regs.clone();
        for vec in unused_regs.values_mut() {
            vec.retain(|id| !used_regs.contains(id));
        }

        self.unused_regs_stack.push(unused_regs);
        self.visit_block(func_body);
        self.unused_regs_stack.pop();
    }

    fn visit_block(&mut self, x: &mut ast::Block) {
        ast::walk_mut_block(self, x);

        let mut new_stmts = Vec::with_capacity(x.0.len());

        for original_stmt in x.0.drain(..) {
            if let ast::StmtBody::Assignment { var, op, value } = &original_stmt.body.value {
                let unused_regs = self.unused_regs_stack
                    .last().expect("must be visiting a function body!");

                let mut original_labels = Some(original_stmt.labels.clone());

                match compile_expr_assignment(unused_regs, &original_stmt.body, var, op, value, self.ty_ctx) {
                    Ok(stmts) => {
                        // we have StmtBodys, now make Stmts
                        new_stmts.extend(stmts.into_iter().map(|body| {
                            sp!(body.span => ast::Stmt {
                                // .take() will only return Some() on the first call, so this puts all of
                                // the original labels on the first instruction
                                labels: original_labels.take().unwrap_or_default(),
                                time: original_stmt.time,
                                body,
                            })
                        }));
                        continue;  // don't follow default path
                    },
                    Err(e) => {
                        self.errors.append(e)
                        // follow default path
                    },
                }
            }
            // default path
            new_stmts.push(original_stmt);
        }
        x.0 = new_stmts;
    }
}

// --------------------------------------------

fn compile_expr_assignment(
    unused_regs: &EnumMap<ScalarType, Vec<i32>>,
    assignment: &Sp<ast::StmtBody>,
    dest_var: &Sp<ast::Var>,
    assign_op: &Sp<ast::AssignOpKind>,
    expr: &Sp<ast::Expr>,
    ty_ctx: &TypeSystem,
) -> Result<Vec<Sp<ast::StmtBody>>, CompileError> {
    let unused_reg_indices = enum_map!(ty => (0..unused_regs[ty].len()).rev().collect());

    let mut mut_expr_copy = expr.clone();
    let mut compiler = ExprCompiler { stmts: vec![], unused_regs, unused_reg_indices, ty_ctx };

    let temp_info = compiler.build_expr(&mut mut_expr_copy)?;
    match temp_info.info {
        BuiltExprKind::Atom => {
            // No temporaries were generated from this, so we can just write the statement as is.
            Ok(vec![assignment.clone()])
        },
        BuiltExprKind::Temp(index) => {
            // The current stmts build a temporary; add one final statement to modify the original LHS.
            let temp_var = sp!(expr.span => compiler.scratch_var_by_index(temp_info.ty, index));
            compiler.stmts.push(sp!(assignment.span => ast::StmtBody::Assignment {
                var: dest_var.clone(),
                op: assign_op.clone(),
                value: sp!(expr.span => ast::Expr::Var(temp_var)),
            }));
            Ok(compiler.stmts)
        },
    }
}

struct ExprCompiler<'a> {
    stmts: Vec<Sp<ast::StmtBody>>,
    /// register IDs of variables not used by this function.
    /// (i.e. the complete set of variables currently usable as scratch)
    unused_regs: &'a EnumMap<ScalarType, Vec<i32>>,
    /// Indices into `unused_regs` of variables that we are not *currently* using as scratch.
    unused_reg_indices: EnumMap<ScalarType, Vec<usize>>,
    ty_ctx: &'a TypeSystem,
}

impl ExprCompiler<'_> {
    fn scratch_var_by_index(&self, ty: ScalarType, index: usize) -> ast::Var {
        let temp_var_id = self.unused_regs[ty][index];
        self.ty_ctx.reg_to_ast(temp_var_id, ty)
    }

    fn build_expr(&mut self, expr: &mut Sp<ast::Expr>) -> Result<BuiltExpr, CompileError> {
        macro_rules! use_new_temporary {
            ($ty:expr) => {
                self.unused_reg_indices[$ty].pop().ok_or_else(|| error!(
                    message("expression too complex to compile"),
                    primary(expr, "ran out of scratch vars here!"),
                    note(
                        "in this function, there are only {} unused vars of this type available for scratch use",
                        self.unused_regs[$ty].len(),
                    ),
                ))?
            };
        }

        match &mut expr.value {
            ast::Expr::LitInt { .. }
            => Ok(BuiltExpr { info: BuiltExprKind::Atom, ty: ScalarType::Int }),
            ast::Expr::LitFloat { .. }
            => Ok(BuiltExpr { info: BuiltExprKind::Atom, ty: ScalarType::Float }),

            ast::Expr::Var(var) => {
                let ty = self.ty_ctx.var_type(var).ok_or_else(|| error!(
                    message("unable to determine type of variable"),
                    primary(var, "type cannot be determined"),
                ))?;
                Ok(BuiltExpr { info: BuiltExprKind::Atom, ty })
            },

            ast::Expr::Binop(a, op, b) => {
                let built_a = self.build_expr(a)?;
                let built_b = self.build_expr(b)?;
                let result_ty = op.result_type(built_a.ty, built_b.ty, (a.span, b.span))?;

                let new_temp_index = match (built_a.info, built_b.info) {
                    // If neither subexpression is a temporary, we need a new temporary
                    (BuiltExprKind::Atom, BuiltExprKind::Atom) => use_new_temporary!(result_ty),
                    // If at least one of the subexpressions was replaced with a temporary, reuse that temporary.
                    (BuiltExprKind::Atom, BuiltExprKind::Temp(temp_index)) => temp_index,
                    (BuiltExprKind::Temp(temp_index), BuiltExprKind::Atom) => temp_index,
                    (BuiltExprKind::Temp(t1_index), BuiltExprKind::Temp(t2_index)) => {
                        assert_ne!(t1_index, t2_index, "bug! (using same temp twice)");

                        // reuse the smaller index and put the bigger one back to be reused later.
                        self.unused_reg_indices[result_ty].push(usize::max(t1_index, t2_index));
                        usize::min(t1_index, t2_index)
                    },
                };

                // Replace the expression with a register.
                let temp_var = sp!(expr.span => self.scratch_var_by_index(result_ty, new_temp_index));
                let new_expr = ast::Expr::Var(temp_var.clone());
                let old_expr = std::mem::replace(&mut expr.value, new_expr);

                // Emit a statement which assigns the original expression to the register.
                self.stmts.push(sp!(expr.span => ast::StmtBody::Assignment {
                    var: temp_var,
                    op: sp!(expr.span => ast::AssignOpKind::Assign),
                    value: sp!(expr.span => old_expr),
                 }));

                Ok(BuiltExpr { ty: result_ty, info: BuiltExprKind::Temp(new_temp_index) })
            },

            ast::Expr::Unop(op, a) => {
                let built_a = self.build_expr(a)?;
                let result_ty = op.result_type(built_a.ty, a.span)?;

                let new_temp_index = match built_a.info {
                    BuiltExprKind::Atom => use_new_temporary!(result_ty),
                    BuiltExprKind::Temp(temp_index) => temp_index,
                };

                let temp_var = sp!(expr.span => self.scratch_var_by_index(result_ty, new_temp_index));
                let new_expr = ast::Expr::Var(temp_var.clone());
                let old_expr = std::mem::replace(&mut expr.value, new_expr);

                self.stmts.push(sp!(expr.span => ast::StmtBody::Assignment {
                    var: temp_var,
                    op: sp!(expr.span => ast::AssignOpKind::Assign),
                    value: sp!(expr.span => old_expr),
                 }));

                Ok(BuiltExpr { ty: result_ty, info: BuiltExprKind::Temp(new_temp_index) })
            },

            _ => Err(error!(
                message("cannot compile expression"),
                primary(expr, "this expression not supported for compilation"),
            )),
        }
    }
}

struct BuiltExpr {
    ty: ScalarType,
    info: BuiltExprKind,
}
enum BuiltExprKind {
    /// The expression was a literal or register, so we did nothing.
    Atom,
    /// The expression was complex, so we emitted a statement which saves it to the register
    /// at this index in `unused_regs[ty]`.
    Temp(usize),
}

// --------------------------------------------

// NOTE: Requires a TypeSystem so that it can resolve the names to their unique Ids so
// that we can easily see that `[10007.0]` and `%F3` and `$F3` are all the same register.
fn get_used_regs(func_body: &ast::Block, ty_ctx: &TypeSystem) -> Vec<i32> {
    struct UsedVisitor<'ts> {
        vars: Vec<i32>,
        ty_ctx: &'ts TypeSystem,
    }

    impl<'ts> Visit for UsedVisitor<'ts> {
        fn visit_stmt(&mut self, x: &Sp<ast::Stmt>) {
            ast::walk_stmt(self, x);
            if let ast::StmtBody::Assignment { var, .. } = &x.body.value {
                if let Some(id) = self.ty_ctx.reg_id(var) {
                    self.vars.push(id);
                }
            }
        }

        fn visit_expr(&mut self, x: &Sp<ast::Expr>) {
            ast::walk_expr(self, x);
            if let ast::Expr::Var(var) = &x.value {
                if let Some(id) = self.ty_ctx.reg_id(var) {
                    self.vars.push(id);
                }
            }
        }

        // in case we ever get nested functions, don't visit them
        fn visit_item(&mut self, _: &Sp<ast::Item>) {}
    }

    let mut v = UsedVisitor { vars: vec![], ty_ctx };
    v.visit_func_body(func_body);
    v.vars
}

// --------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fmt::Formatter;

    const SIMPLE_MAPFILE: &'static str = "\
        !anmmap\n\
        !gvar_names\n0 A\n1 B\n2 C\n3 D\n4 X\n5 Y\n6 Z\n7 W\n\
        !gvar_types\n0 $\n1 $\n2 $\n3 $\n4 %\n5 %\n6 %\n7 %\n";

    fn compile_exprs(text: &str) -> String {
        let general_use_regs = enum_map!{
            ScalarType::Int => vec![0, 1, 2, 3],
            ScalarType::Float => vec![4, 5, 6, 7],
        };

        let eclmap = crate::eclmap::Eclmap::parse(SIMPLE_MAPFILE).unwrap();
        let mut ty_ctx = crate::type_system::TypeSystem::new();
        ty_ctx.extend_from_eclmap("DUMMY.anmmap".as_ref(), &eclmap);

        let mut f = Formatter::new(vec![]).with_max_columns(99999);
        let mut files = crate::pos::Files::new();
        let mut script = files.parse::<ast::Script>("<input>", text.as_bytes()).unwrap_or_else(|e| panic!("{}", e));

        let mut visitor = Visitor::new(general_use_regs, &ty_ctx);
        ast::walk_mut_script(&mut visitor, &mut script);
        visitor.finish().unwrap();

        f.fmt(&script).unwrap();
        String::from_utf8(f.into_inner().unwrap()).unwrap()
    }

    #[test]
    fn lol() {
        assert_snapshot!("halp", compile_exprs(r#"void main() { A = (B + 2) * (B + 3) * (B + 4); }"#).trim());
    }

    #[test]
    fn lol2() {
        assert_snapshot!("bleh", compile_exprs(r#"void main() { A = 3 * (B + 2); }"#).trim());
    }

    #[test]
    fn lol3() {
        assert_snapshot!("blue", compile_exprs(r#"void main() { A = (B + 2) * 3; }"#).trim());
    }
}
