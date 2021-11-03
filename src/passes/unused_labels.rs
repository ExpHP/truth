use std::collections::HashMap;

use crate::Ident;
use crate::error::ErrorReported;
use crate::ast::{self, Visit, VisitMut};
use crate::pos::Sp;

/// Removes unused labels from function bodies.
///
/// To use this, you must call a method whose scope is at least as large as [`VisitMut::visit_root_block`].
pub fn run<V: ast::Visitable>(ast: &mut V) -> Result<(), ErrorReported> {
    let mut visitor = Visitor { label_refcounts_stack: vec![] };
    ast.visit_mut_with(&mut visitor);
    Ok(())
}

struct Visitor {
    // This is a stack for dealing with nested functions.
    label_refcounts_stack: Vec<HashMap<Ident, u32>>,
}

impl VisitMut for Visitor {
    fn visit_root_block(&mut self, func_body: &mut ast::Block) {
        self.label_refcounts_stack.push(get_label_refcounts(&func_body.0));
        self.visit_block(func_body);
        self.label_refcounts_stack.pop();
    }

    fn visit_block(&mut self, x: &mut ast::Block) {
        ast::walk_block_mut(self, x);
        x.0.retain(|stmt| match &stmt.kind {
            ast::StmtKind::Label(ident) => {
                self.label_refcounts_stack
                    .last().expect("must be visiting a function body!")
                    .get(&ident.value).copied()
                    .unwrap_or(0) > 0
            },
            _ => true,
        });
    }
}

/// Get the total number of times each label in a block is mentioned in a goto or instruction.
///
/// This should only be called on the outermost block of a function!
pub fn get_label_refcounts(block: &[Sp<ast::Stmt>]) -> HashMap<Ident, u32> {
    struct Visitor(HashMap<Ident, u32>);
    impl Visit for Visitor {
        fn visit_jump(&mut self, jump: &ast::StmtJumpKind) {
            ast::walk_jump(self, jump);
            match jump {
                ast::StmtJumpKind::Goto(ast::StmtGoto { destination, .. }) => {
                    *self.0.entry(destination.value.clone()).or_insert(0) += 1;
                },
                ast::StmtJumpKind::BreakContinue { .. } => {},
            }
        }

        fn visit_expr(&mut self, expr: &Sp<ast::Expr>) {
            ast::walk_expr(self, expr);
            match &expr.value {
                // count offsetof(label) and timeof(label)
                ast::Expr::LabelProperty { label, .. } => {
                    *self.0.entry(label.value.clone()).or_insert(0) += 1;
                },
                _ => {},
            }
        }

        // ignore inner functions
        fn visit_root_block(&mut self, _: &ast::Block) {}
    }

    let mut visitor = Visitor(HashMap::new());
    for stmt in block {
        visitor.visit_stmt(stmt);
    }
    visitor.0
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strip_unused_labels<A>(text: &str) -> A
    where
        A: crate::parse::Parse,
        Sp<A>: crate::ast::Visitable,
    {
        let mut scope = crate::Builder::new().build();
        let mut truth = scope.truth();

        let mut parsed = truth.parse::<A>("<input>", text.as_ref()).unwrap();
        let ctx = truth.ctx();
        crate::passes::resolution::resolve_names(&parsed, ctx).unwrap();
        crate::passes::unused_labels::run(&mut parsed).unwrap();

        parsed.value
    }

    struct CountIdentVisitor {
        search_ident: Ident,
        count: u32,
    }

    impl ast::Visit for CountIdentVisitor {
        fn visit_stmt(&mut self, stmt: &Sp<ast::Stmt>) {
            if let ast::StmtKind::Label(label) = &stmt.kind {
                if label == &self.search_ident {
                    self.count += 1;
                }
            }
            ast::walk_stmt(self, stmt);
        }
    }

    fn count_occurrences_of_label<A: ast::Visitable + crate::fmt::Format>(ast: &A, ident: &str) -> u32 {
        let mut v = CountIdentVisitor { search_ident: ident.parse().unwrap(), count: 0 };
        ast.visit_with(&mut v);
        v.count
    }

    #[test]
    fn simple() {
        let out = strip_unused_labels::<ast::ScriptFile>(r#"
void foo() {
    label_1:
    label_2:
    if (true) {
        goto label_1;
    }
}"#);
        assert_eq!(count_occurrences_of_label(&out, "label_1"), 1);
        assert_eq!(count_occurrences_of_label(&out, "label_2"), 0);
    }

    #[test]
    fn nested_func() {
        let out = strip_unused_labels::<ast::ScriptFile>(r#"
void foo() {
    label_1:
    const void bar() {
        label_1:
        goto label_1;
    }
}"#);
        // it should delete the label_1: in foo() but not the one in bar()
        assert_eq!(count_occurrences_of_label(&out, "label_1"), 1);
    }
}
