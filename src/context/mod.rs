//! Structs that carry important global compiler state.

use std::path::PathBuf;
use std::cell::RefCell;
use std::rc::Rc;
use std::fmt;
use std::any::Any;

use crate::ident::GensymContext;
use crate::error::CompileError;
use crate::resolve::Resolutions;
use crate::resolve::rib::Rib;

use codespan_reporting as cs;
use cs::term::termcolor as tc;

use crate::pos::Files;

pub use defs::Defs;
pub mod defs;

pub use consts::Consts;
pub mod consts;

/// Context object for the majority of compilation.
///
/// This is a context object that holds a significant portion of the mutable state that is shared between
/// compiler passes (in particular passes that traverse the AST or that convert between the AST and
/// low-level representations).
///
/// It provides some methods for creating definitions and returning [`DefId`]s.  This is partly historical,
/// but also because it's not clear how to move these methods to [`Defs`] where they might conceptually belong.
///
/// # Limitation of scope
///
//   NOTE: To the future me who is about to delete this section from the documentation:
//         Please consider the examples of concessions in the section.
//         Are you absolutely certain you cannot do something similar to achieve your current goal?
//
/// While there is no doubt a great deal of code which depends on this type (or at least on one or more of
/// its fields), there are a number of phases of compilation that are **forbidden** to depend on this type
/// or any of its fields (except [`DiagnosticEmitter`]), just as a matter of principle.  These are:
///
/// * Parsing of text to AST
/// * Formatting of AST to text
/// * Reading binary files to the low-level representation
/// * Writing the low-level representation to a binary file
///
/// There have been numerous instances of things in the past which appeared that they may require breaking
/// this rule, but it has always been found possible to make concessions in favor of keeping this separation.
/// (e.g. [`llir::RawInstr`] holds an args blob so that reading/writing doesn't require signatures.
/// [`crate::passes::resolve_names::assign_res_ids`] allows the parser to not require `Resolutions`, and
/// [`crate::passes::debug::make_idents_unique`] does the same for the formatter)
#[derive(Debug, Clone)]
pub struct CompilerContext<'ctx> {
    pub diagnostics: DiagnosticEmitter,

    /// Catalogues all loaded mapfiles for generating imports.
    mapfiles: Vec<PathBuf>,
    /// Results of name resolution.  Maps [`ResId`]s to [`DefId`]s.
    pub resolutions: Resolutions,
    /// Stores information about [`DefId`]s.
    pub defs: Defs,
    /// For generating identifiers.
    pub gensym: GensymContext,
    /// Cached const values.
    pub consts: Consts,
    /// The initial set of ribs for name resolution, containing names from mapfiles and meta.
    pub initial_ribs: Vec<Rib>,

    /// Ok so... the field that I initially added that needed a lifetime doesn't need one anymore,
    /// but this is here because we might still eventually need a lifetime for arenas, so I don't
    /// want to have to undo the changes that added 'ctx quite just yet.
    ///
    /// FIXME: remove if still unused after a long time
    _lifetime: std::marker::PhantomData<*mut &'ctx ()>, // invariant
}

pub trait WriteError: tc::WriteColor + Any {
    fn as_any(&self) -> &dyn Any;
    fn as_write_color(&mut self) -> &mut dyn tc::WriteColor;
}

impl<T: tc::WriteColor + Any> WriteError for T {
    fn as_any(&self) -> &dyn Any { self }
    fn as_write_color(&mut self) -> &mut dyn tc::WriteColor { self }
}

impl CompilerContext<'_> {
    fn from_diagnostic_writer<W: WriteError>(writer: W) -> Self {
        CompilerContext {
            diagnostics: DiagnosticEmitter::from_writer(writer),
            mapfiles: Default::default(),
            resolutions: Default::default(),
            defs: Default::default(),
            gensym: Default::default(),
            consts: Default::default(),
            initial_ribs: Default::default(),
            _lifetime: Default::default(),
        }
    }

    /// Create a [`CompilerContext`] that writes diagnostics to the standard error stream.
    pub fn new_stderr() -> Self {
        Self::from_diagnostic_writer(tc::StandardStream::stderr(tc::ColorChoice::Auto))
    }

    /// Create a [`CompilerContext`] that captures diagnostic output which can be recovered
    /// by calling [`Self::get_captured_diagnostics`].
    pub fn new_captured() -> Self {
        let writer: CapturedWriter = tc::NoColor::new(vec![]);
        Self::from_diagnostic_writer(writer)
    }

    /// Obtain captured diagnostics written to stderr, provided that this [`CompilerContext`]
    /// was constructed using [`Self::new_captured`]. (otherwise, returns `None`)
    pub fn get_captured_diagnostics(&self) -> Option<String> {
        let writer = self.diagnostics.writer.borrow().as_any().downcast_ref::<CapturedWriter>()?;

        Some(String::from_utf8_lossy(&writer.get_ref()).into_owned())
    }
}

type CapturedWriter = tc::NoColor<Vec<u8>>;

// =============================================================================

/// Type responsible for emitting diagnostics and storing the metadata necessary to render them.
#[derive(Clone)]
pub struct DiagnosticEmitter {
    files: Files,
    config: cs::term::Config,
    writer: Rc<RefCell<dyn WriteError>>,
}

impl fmt::Debug for DiagnosticEmitter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("DiagnosticEmitter")
            .field("files", &self.files)
            .field("config", &self.config)
            .field("writer", &(..))
            .finish()
    }
}

impl DiagnosticEmitter {
    fn from_writer<W: WriteError>(writer: W) -> Self {
        DiagnosticEmitter {
            files: Files::new(),
            config: default_term_config(),
            writer: Rc::new(RefCell::new(writer)),
        }
    }

    pub fn emit(&self, error: CompileError) {
        let mut writer = self.writer.borrow_mut();

        error.emit_to_writer(writer.as_write_color(), &self.files, &self.config);
    }
}

fn default_term_config() -> cs::term::Config {
    let mut config = cs::term::Config::default();
    // Make output closer to rustc. Fewer colors overall, looks better.
    config.styles.primary_label_error.set_intense(true);
    config.styles.secondary_label.set_intense(true);
    config.styles.line_number.set_intense(true);
    config.styles.source_border.set_intense(true);
    config
}
