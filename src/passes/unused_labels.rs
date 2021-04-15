use std::collections::HashSet;

use crate::Ident;
use crate::error::ErrorReported;
use crate::ast::{self, Visit, VisitMut};
use crate::pos::Sp;

/// Removes unused labels from function bodies.
///
/// To use this, you must call a method whose scope is at least as large as [`VisitMut::visit_root_block`].
pub fn run<V: ast::Visitable>(ast: &mut V) -> Result<(), ErrorReported> {
    let mut visitor = Visitor { used_labels_stack: vec![] };
    ast.visit_mut_with(&mut visitor);
    Ok(())
}

struct Visitor {
    // This is a stack.  If we ever get nested functions this might become relevant,
    // but for now this is always 0 to 1 elements.
    used_labels_stack: Vec<HashSet<Ident>>,
}

impl VisitMut for Visitor {
    fn visit_root_block(&mut self, func_body: &mut ast::Block) {
        let used_labels = get_used_labels(func_body);

        self.used_labels_stack.push(used_labels);
        self.visit_block(func_body);
        self.used_labels_stack.pop();
    }

    fn visit_block(&mut self, x: &mut ast::Block) {
        ast::walk_block_mut(self, x);
        x.0.retain(|stmt| match &stmt.body {
            ast::StmtBody::Label(ident) => {
                self.used_labels_stack
                    .last().expect("must be visiting a function body!")
                    .contains(&ident.value)
            },
            _ => true,
        });
    }
}

fn get_used_labels(func_body: &ast::Block) -> HashSet<Ident> {
    struct UsedVisitor {
        labels: HashSet<Ident>,
    }

    impl Visit for UsedVisitor {
        fn visit_stmt(&mut self, x: &Sp<ast::Stmt>) {
            ast::walk_stmt(self, x);

            match &x.body {
                | ast::StmtBody::Goto(goto)
                | ast::StmtBody::CondGoto { goto, .. }
                => { self.labels.insert(goto.destination.value.clone()); }

                _ => {},
            };
        }

        // in case we ever get nested functions, don't visit them
        fn visit_item(&mut self, _: &Sp<ast::Item>) {}
    }

    let mut v = UsedVisitor { labels: HashSet::new() };
    v.visit_root_block(func_body);
    v.labels
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::Parse;

    fn strip_unused_labels<A: ast::Visitable + Parse>(text: &str) -> A {
        let mut scope = crate::Builder::new().build();
        let mut truth = scope.truth();

        let mut parsed = truth.parse::<A>("<input>", text.as_ref()).unwrap().value;
        let ctx = truth.ctx();
        crate::passes::resolve_names::assign_res_ids(&mut parsed, ctx).unwrap();
        crate::passes::resolve_names::run(&parsed, ctx).unwrap();
        crate::passes::unused_labels::run(&mut parsed).unwrap();

        parsed
    }

    struct CountIdentVisitor {
        search_ident: Ident,
        count: u32,
    }

    impl ast::Visit for CountIdentVisitor {
        fn visit_stmt(&mut self, stmt: &Sp<ast::Stmt>) {
            if let ast::StmtBody::Label(label) = &stmt.body {
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
