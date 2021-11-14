//! See [`run`].

use crate::raw;
use crate::ast;
use crate::bitset::BitSet32;
use crate::pos::Sp;
use crate::error::{ErrorReported, ErrorFlag};
use crate::diagnostic::Emitter;
use crate::resolve::{NodeId, IdMap, node_id_helpers};

pub const DEFAULT_DIFFICULTY_MASK_BYTE: raw::DifficultyMask = 0xFF;
pub const DEFAULT_DIFFICULTY_MASK: BitSet32 = BitSet32::from_mask(DEFAULT_DIFFICULTY_MASK_BYTE as _);

/// Time and difficulty assignment pass.
///
/// This pass runs over the whole AST, applying the semantics of time and difficulty labels
/// to compute the values for each statement.  It has been decided that this is preferable
/// to having the information encoded directly within each Stmt, as it saves us the trouble
/// of micromanaging this info during AST manipulations.
pub fn run<V: ast::Visitable + ?Sized>(ast: &V, emitter: &dyn Emitter) -> Result<IdMap<NodeId, TimeAndDifficulty>, ErrorReported> {
    let mut visitor = Visitor {
        emitter,
        errors: Default::default(),
        helper: Default::default(),
        output: Default::default(),
    };
    // start out as if we are just entering a function body, so that the visitor can run on
    // individual blocks during unit tests
    visitor.helper.enter_root_block();
    visitor.helper.enter_block();

    ast.visit_with(&mut visitor);
    visitor.errors.into_result(visitor.output)
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct TimeAndDifficulty {
    pub time: raw::Time,
    pub difficulty_mask: BitSet32,
}

struct Visitor<'a> {
    emitter: &'a dyn Emitter,
    errors: ErrorFlag,
    output: IdMap<NodeId, TimeAndDifficulty>,
    helper: TimeAndDifficultyHelper,
}

/// This guy is public to allow another pass to be written which reports errors based on
/// difficulty labels. (we wouldn't want those in this semantics pass as they might get
/// reported multiple times)
#[derive(Default)]
pub struct TimeAndDifficultyHelper {
    difficulty_stack: Vec<Sp<BitSet32>>,
    time_stack: Vec<i32>,
}

impl TimeAndDifficultyHelper {
    pub fn new() -> Self { Default::default() }
    pub fn time(&self) -> i32 { *self.time_stack.last().expect("empty time stack?! (bug)") }
    pub fn _difficulty_mask_sp(&self) -> Sp<BitSet32> { *self.difficulty_stack.last().expect("empty diff stack?! (bug)") }

    // this provides no span because root blocks will have a null span for their difficulty
    pub fn difficulty_mask(&self) -> BitSet32 { self._difficulty_mask_sp().value }
    // this DOES provide a span because nontrivial difficulties must have come from a label
    pub fn difficulty_mask_if_nontrivial(&self) -> Option<Sp<BitSet32>> {
        let mask = self._difficulty_mask_sp();
        (mask != DEFAULT_DIFFICULTY_MASK).then(|| mask)
    }

    pub fn visit_stmt_shallow(&mut self, stmt: &ast::Stmt) {
        match &stmt.kind {
            &ast::StmtKind::AbsTimeLabel(value) => {
                *self.time_stack.last_mut().expect("empty time stack?! (bug)") = value.value;
            },
            &ast::StmtKind::RelTimeLabel { delta, .. } => {
                *self.time_stack.last_mut().expect("empty time stack?! (bug)") += delta.value;
            },
            _ => {},
        }
    }

    /// Indicate that we are entering the root block of an item.
    pub fn enter_root_block(&mut self) {
        self.time_stack.push(0);
        self.difficulty_stack.push(sp!(DEFAULT_DIFFICULTY_MASK));
    }

    pub fn exit_root_block(&mut self) {
        self.time_stack.pop().expect("empty time stack?! (bug)");
        self.difficulty_stack.pop().expect("empty diff stack?! (bug)");
    }

    pub fn enter_block(&mut self) {
        let &outer_difficulty = self.difficulty_stack.last().unwrap();
        self.difficulty_stack.push(outer_difficulty);
    }

    pub fn exit_block(&mut self) {
        self.difficulty_stack.pop().expect("empty diff stack?! (bug)");
    }

    /// Set the time and difficulty appropriately for the current statement.
    pub fn enter_stmt(&mut self, stmt: &Sp<ast::Stmt>) {
        // time labels should affect their own attributes,
        // so perform a shallow visit before storing data.
        self.visit_stmt_shallow(stmt);

        if let Some(&sp_pat!(label_span => ast::DiffLabel { mask, .. })) = stmt.diff_label.as_ref() {
            let mask = mask.expect("compute_diff_label_masks pass was not run!");
            self.difficulty_stack.push(sp!(label_span => mask));
        }
    }

    pub fn exit_stmt(&mut self, stmt: &Sp<ast::Stmt>) {
        if let Some(ast::DiffLabel { .. }) = stmt.diff_label.as_ref().map(|d| &d.value) {
            self.difficulty_stack.pop().expect("empty diff stack?! (bug)");
        }
    }
}

impl ast::Visit for Visitor<'_> {
    fn visit_stmt(&mut self, stmt: &Sp<ast::Stmt>) {
        self.helper.enter_stmt(stmt);

        // record data for this statement
        let data = TimeAndDifficulty {
            time: self.helper.time(),
            difficulty_mask: self.helper.difficulty_mask(),
        };
        if let Err(e) = node_id_helpers::id_map_insert(&self.emitter, &mut self.output, stmt, stmt.node_id, data) {
            self.errors.set(e);
        }

        // recurse if it has blocks or items
        ast::walk_stmt(self, stmt);

        self.helper.exit_stmt(stmt);
    }

    fn visit_root_block(&mut self, block: &ast::Block) {
        self.helper.enter_root_block();
        self.visit_block(block);
        self.helper.exit_root_block();
    }

    fn visit_block(&mut self, block: &ast::Block) {
        self.helper.enter_block();
        ast::walk_block(self, block);
        self.helper.exit_block();
    }
}
