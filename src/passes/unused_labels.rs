use std::collections::HashSet;

use crate::Ident;
use crate::error::CompileError;
use crate::ast::{self, Visit, VisitMut};
use crate::pos::Sp;

/// Removes unused labels from function bodies.
///
/// To use this, you must call a method whose scope is at least as large as [`VisitMut::visit_func_body`].
pub struct Visitor {
    // This is a stack.  If we ever get nested functions this might become relevant,
    // but for now this is always 0 to 1 elements.
    used_labels_stack: Vec<HashSet<Ident>>,
}

impl Visitor {
    pub fn new() -> Self {
        Visitor { used_labels_stack: vec![] }
    }

    pub fn finish(self) -> Result<(), CompileError> { Ok(()) }
}

impl VisitMut for Visitor {
    fn visit_func_body(&mut self, func_body: &mut ast::Block) {
        let used_labels = get_used_labels(func_body);

        self.used_labels_stack.push(used_labels);
        self.visit_block(func_body);
        self.used_labels_stack.pop();
    }

    fn visit_block(&mut self, x: &mut ast::Block) {
        ast::walk_block_mut(self, x);
        x.0.retain(|stmt| match &stmt.body.value {
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

            match &x.body.value {
                | ast::StmtBody::Jump(jump)
                | ast::StmtBody::CondJump { jump, .. }
                => { self.labels.insert(jump.destination.value.clone()); },

                _ => {},
            };
        }

        // in case we ever get nested functions, don't visit them
        fn visit_item(&mut self, _: &Sp<ast::Item>) {}
    }

    let mut v = UsedVisitor { labels: HashSet::new() };
    v.visit_func_body(func_body);
    v.labels
}
