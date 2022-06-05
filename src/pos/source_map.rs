use std::borrow::Cow;
use std::num::NonZeroU32;
use std::cell::RefCell;
use std::rc::Rc;

use codespan_reporting::{files as cs_files};

use crate::pos::{FileId, Span, BytePos};
use crate::diagnostic::Diagnostic;
use crate::debug_info;

/// An implementation of [`codespan_reporting::files::Files`] for `truth`.
///
/// This is the type responsible for keeping track of source text so that snippets can be displayed
/// in diagnostic error messages.
#[derive(Debug, Clone)]
pub struct Files {
    inner: RefCell<FilesImpl>,
}

#[derive(Debug, Clone)]
pub struct FilesImpl {
    files: cs_files::SimpleFiles<String, Rc<str>>,
    max_file_id: FileId,
}

impl Files {
    pub fn new() -> Self { Files { inner: RefCell::new(FilesImpl {
        files: cs_files::SimpleFiles::new(),
        max_file_id: None,
    }) } }

    /// Add a piece of source text to the database, and give it a name (usually a filepath)
    /// which will appear in error messages.  Also validate the source as UTF-8.
    ///
    /// The name does not need to be a valid path or even unique; for instance, it is common to use
    /// the name `"<input>"` for source text not associated with any file.
    pub fn add(&self, name: &str, source: &[u8]) -> Result<(FileId, Rc<str>), Diagnostic> {
        let utf8_cow = prepare_diagnostic_text_source(source);
        let rc_source: Rc<str> = utf8_cow[..].into();

        let mut inner = self.inner.borrow_mut();
        let file_id = Self::shift_file_id(inner.files.add(name.to_owned(), rc_source.clone()));
        inner.max_file_id = file_id;

        // the cow is borrowed iff the input was valid UTF-8
        if let Cow::Owned(_) = utf8_cow {
            let err = std::str::from_utf8(source).unwrap_err();
            let pos = err.valid_up_to();
            return Err(error!(
                message("invalid UTF-8"),
                primary(Span::new(file_id, BytePos(pos as _), BytePos(pos as _)), "not valid UTF-8"),
                note("truth expects all input script files to be UTF-8 regardless of the output encoding"),
            ));
        }

        Ok((file_id, rc_source))
    }

    fn unshift_file_id(file_id: FileId) -> Result<usize, cs_files::Error> {
        // produce Error on file_id = None; such spans aren't fit for diagnostics
        let file_id: u32 = file_id.ok_or(cs_files::Error::FileMissing)?.into();
        Ok(file_id as usize - 1)
    }

    fn shift_file_id(file_id: usize) -> FileId {
        NonZeroU32::new(file_id as u32 + 1)
    }

    fn file_ids(&self) -> impl Iterator<Item=FileId> {
        let max_file_id = self.inner.borrow().max_file_id.map_or(0, |x| x.get());
        (1..=max_file_id).map(|x| Some(NonZeroU32::new(x).unwrap()))
    }

    pub fn debug_info(&self) -> Vec<debug_info::SourceFile> {
        self.file_ids().map(|file_id| {
            debug_info::SourceFile {
                id: file_id.map_or(0, |x| x.get() as i32),
                name: cs_files::Files::name(self, file_id).unwrap(),
            }
        }).collect()
    }
}

/// This implementation provides source text that has been lossily modified to be valid UTF-8,
/// and which should only be used for diagnostic purposes.
impl<'a> cs_files::Files<'a> for Files {
    type FileId = FileId;
    type Name = String;
    type Source = Rc<str>;

    // Just delegate everything
    fn name(&self, file_id: FileId) -> Result<String, cs_files::Error> {
        self.inner.borrow().files.name(Self::unshift_file_id(file_id)?)
    }

    fn source(&self, file_id: FileId) -> Result<Rc<str>, cs_files::Error> {
        Ok(self.inner.borrow().files.get(Self::unshift_file_id(file_id)?)?.source().clone())
    }

    fn line_index(&self, file_id: FileId, byte_index: usize) -> Result<usize, cs_files::Error> {
        self.inner.borrow().files.line_index(Self::unshift_file_id(file_id)?, byte_index)
    }
    fn line_range(&self, file_id: FileId, line_index: usize) -> Result<std::ops::Range<usize>, cs_files::Error> {
        self.inner.borrow().files.line_range(Self::unshift_file_id(file_id)?, line_index)
    }
}

/// Obtain a UTF-8 version of the source that is suitable for rendering spans in error messages
/// for potentially non-UTF8 text.
fn prepare_diagnostic_text_source(s: &[u8]) -> Cow<'_, str> {
    // Back when truth allowed scripts to be Shift-JIS, we had to worry about the replacement character
    // messing up byte offsets, and so this was more complicated.
    //
    // Now that we require UTF-8, the only possible error that needs to be rendered from a non-UTF-8 file
    // is an error at the FIRST appearance of non-UTF8 data; thus the byte offsets will be just fine.
    String::from_utf8_lossy(s)
}
