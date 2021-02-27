use std::collections::HashMap;

use crate::ast;
use crate::error::CompileError;
use crate::resolve::{DefId, Resolutions};
use crate::ident::{Ident, ResIdent};

/// Appends a suffix to every name to make it distinct.  (e.g. `foo -> foo_0`)
///
/// This is a neat and visual way to inspect the results of name resolution, as it will let
/// you see which instances of the same identifier were resolved to the same definition.
/// The renumbering scheme is deterministic and tries to be vaguely robust to spurious changes
/// that could arise from compiler implementation details, but it is otherwise unspecified.
///
/// Note that [`CompilerContext`] and spans will still refer to the old identifiers.  To get the
/// most out of this, try formatting the modified node [to a string][`crate::fmt::stringify`].
pub fn run<A: ast::Visitable>(ast: &mut A, resolutions: &Resolutions) -> Result<(), CompileError> {
    let mut v = Visitor {
        resolutions,
        next_numbers: Default::default(),
        assigned_numbers: Default::default(),
    };
    ast.visit_mut_with(&mut v);
    Ok(())
}

// =============================================================================

struct Visitor<'a> {
    resolutions: &'a Resolutions,
    next_numbers: HashMap<Ident, u32>,
    assigned_numbers: HashMap<DefId, u32>,
}

impl ast::VisitMut for Visitor<'_> {
    fn visit_res_ident(&mut self, ident: &mut ResIdent) {
        let Visitor { resolutions, next_numbers, assigned_numbers } = self;

        let def_id = resolutions.expect_def(ident);

        let number = assigned_numbers.entry(def_id).or_insert_with(|| {
            let stored_number = next_numbers.entry(ident.as_raw().clone()).or_insert(0);
            let number = *stored_number;
            *stored_number += 1;
            number
        });

        let new_ident = format!("{}_{}", ident, number).parse().expect("adding suffix to ident made it invalid?!");
        *ident.as_raw_mut() = new_ident;
    }
}
