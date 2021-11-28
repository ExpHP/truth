use super::Format;
use std::path::{PathBuf, Path};
use std::rc::Rc;

/// A file possibly backed by a temp directory (which, if so, will be deleted on drop).
///
/// The file need not necessarily even exist yet; e.g. you can use [`Self::new_temp`] to create a
/// temp dir, then use [`Self::as_path`] as an output file argument to a CLI command.
#[derive(Debug, Clone)]
pub struct TestFile {
    descr: String,
    _tempdir: Option<Rc<tempfile::TempDir>>,
    filepath: PathBuf,
}

impl TestFile {
    /// Construct a [`TestFile`] referring to a (not yet created) filepath inside a newly created
    /// tempdir.  The tempdir will be deleted on drop.
    pub fn new_temp(filename: &str) -> Self {
        let descr = filename.to_string();
        let tempdir = tempfile::tempdir().unwrap_or_else(|e| panic!("while making tempdir for {}: {}", descr, e));
        let filepath = tempdir.path().join(filename);
        TestFile { descr, _tempdir: Some(Rc::new(tempdir)), filepath }
    }

    /// Construct a [`TestFile`] from file contents, which will be written to a new file inside
    /// of a new temporary directory.  The tempdir will be deleted on drop.
    pub fn from_content(filename: &str, bytes: impl AsRef<[u8]>) -> Self {
        let out = TestFile::new_temp(filename);
        std::fs::write(out.as_path(), bytes)
            .unwrap_or_else(|e| panic!("while writing to {}: {}", filename, e));
        out
    }

    /// Construct from an existing file without creating a tempdir.
    pub fn from_path(filepath: impl AsRef<Path>) -> Self {
        let filepath = filepath.as_ref().to_owned();
        let descr = filepath.display().to_string();
        TestFile { descr, filepath, _tempdir: None }
    }

    pub fn as_path(&self) -> &Path {
        &self.filepath
    }

    pub fn create(&self) -> std::fs::File {
        std::fs::File::create(&self.filepath)
            .unwrap_or_else(|e| panic!("while creating file for {}: {}", self.descr, e))
    }

    pub fn read(&self) -> Vec<u8> {
        std::fs::read(&self.filepath)
            .unwrap_or_else(|e| panic!("while reading bytes from {}: {}", self.descr, e))
    }

    pub fn read_to_string(&self) -> String {
        std::fs::read_to_string(&self.filepath)
            .unwrap_or_else(|e| panic!("while reading text from {}: {}", self.descr, e))
    }

    pub fn read_anm(&self, format: &Format) -> truth::AnmFile {
        let mut scope = truth::Builder::new().build();
        let mut truth = scope.truth();
        truth.read_anm(format.game, self.as_path(), true).unwrap()
    }

    pub fn read_msg(&self, format: &Format) -> truth::MsgFile {
        let mut scope = truth::Builder::new().build();
        let mut truth = scope.truth();
        truth.read_msg(format.game, truth::LanguageKey::Msg, self.as_path()).unwrap()
    }

    pub fn read_std(&self, format: &Format) -> truth::StdFile {
        let mut scope = truth::Builder::new().build();
        let mut truth = scope.truth();
        truth.read_std(format.game, self.as_path()).unwrap()
    }

    pub fn read_ecl(&self, format: &Format) -> truth::EclFile {
        let mut scope = truth::Builder::new().build();
        let mut truth = scope.truth();
        truth.read_ecl(format.game, self.as_path()).unwrap()
    }
}
