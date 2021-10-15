//! See [`run`].

use crate::ast;
use crate::pos::Sp;
use crate::error::{ErrorReported, ErrorFlag};
use crate::resolve::{NodeId, IdMap, node_id_helpers};
use crate::context::CompilerContext;

pub const DEFAULT_DIFFICULTY_MASK: u8 = 0xFF;

/// Time and difficulty assignment pass.
///
/// This pass runs over the whole AST, applying the semantics of time and difficulty labels
/// to compute the values for each statement.  It has been decided that this is preferable
/// to having the information encoded directly within each Stmt, as it saves us the trouble
/// of micromanaging this info during AST manipulations.
pub fn run<V: ast::Visitable>(ast: &V, ctx: &CompilerContext<'_>) -> Result<IdMap<NodeId, TimeAndDifficulty>, ErrorReported> {
    let mut visitor = Visitor::new(ctx);
    // start out as if we are just entering a function body, so that the visitor can run on
    // individual blocks during unit tests
    visitor.enter_root_block();

    ast.visit_with(&mut visitor);
    visitor.errors.into_result(visitor.output)
}

pub struct TimeAndDifficulty {
    pub time: i32,
    pub difficulty_mask: u8,
}

struct Visitor<'a, 'ctx> {
    ctx: &'a CompilerContext<'ctx>,
    errors: ErrorFlag,
    difficulty_stack: Vec<u8>,
    time_stack: Vec<i32>,
    output: IdMap<NodeId, TimeAndDifficulty>,
}

impl<'a, 'ctx> Visitor<'a, 'ctx> {
    pub fn new(ctx: &'a CompilerContext<'ctx>) -> Self {
        Visitor {
            ctx,
            errors: ErrorFlag::new(),
            difficulty_stack: vec![],
            time_stack: vec![],
            output: IdMap::new(),
        }
    }

    fn time(&self) -> i32 { *self.time_stack.last().expect("empty time stack?! (bug)") }
    fn difficulty_mask(&self) -> u8 { *self.difficulty_stack.last().expect("empty diff stack?! (bug)") }
    fn visit_stmt_shallow(&mut self, stmt: &ast::Stmt) {
        match &stmt.body {
            &ast::StmtBody::RawDifficultyLabel(value) => {
                *self.difficulty_stack.last_mut().expect("empty diff stack?! (bug)") = value.value as u8;
            },
            &ast::StmtBody::AbsTimeLabel(value) => {
                *self.time_stack.last_mut().expect("empty time stack?! (bug)") = value.value;
            },
            &ast::StmtBody::RelTimeLabel { delta, .. } => {
                *self.time_stack.last_mut().expect("empty time stack?! (bug)") += delta.value;
            },
            _ => {},
        }
    }

    /// Indicate that we are entering the root block of an item.
    pub fn enter_root_block(&mut self) {
        self.time_stack.push(0);
        self.difficulty_stack.push(DEFAULT_DIFFICULTY_MASK);
    }

    pub fn exit_root_block(&mut self) {
        self.time_stack.pop().expect("empty time stack?! (bug)");
        self.difficulty_stack.pop().expect("empty diff stack?! (bug)");
    }
}

impl ast::Visit for Visitor<'_, '_> {
    fn visit_stmt(&mut self, stmt: &Sp<ast::Stmt>) {
        // time/difficulty labels should affect their own attributes,
        // so perform a shallow visit before storing data.
        self.visit_stmt_shallow(stmt);

        // record data for this statement
        let data = TimeAndDifficulty { time: self.time(), difficulty_mask: self.difficulty_mask() };
        if let Err(e) = node_id_helpers::id_map_insert(&self.ctx.emitter, &mut self.output, stmt, stmt.node_id, data) {
            self.errors.set(e);
        }

        // recurse if it has blocks or items
        ast::walk_stmt(self, stmt);
    }

    fn visit_root_block(&mut self, block: &ast::Block) {
        self.enter_root_block();
        ast::walk_block(self, block);
        self.exit_root_block();
    }
}
