//! Sanity checks.
//!
//! Checks that invariants of the AST are upheld.

use crate::error::ErrorReported;
use crate::ast::{self, Visit};

/// Check that blocks are properly bookended.
pub fn validate_block_bookending<V: ast::Visitable>(ast: &V) -> Result<(), ErrorReported> {
    struct BlockBookendCheckVisitor;
    impl Visit for BlockBookendCheckVisitor {
        fn visit_block(&mut self, block: &ast::Block) {
            assert!(block.0.len() >= 2);
            assert_eq!(block.first_stmt().kind, ast::StmtKind::NoInstruction);
            assert_eq!(block.last_stmt().kind, ast::StmtKind::NoInstruction);
            if block.0.len() > 2 {
                assert_ne!(block.0[1].kind, ast::StmtKind::NoInstruction);
                assert_ne!(block.0[block.0.len() - 2].kind, ast::StmtKind::NoInstruction);
            }
        }
    }

    ast.visit_with(&mut BlockBookendCheckVisitor);
    Ok(())
}



