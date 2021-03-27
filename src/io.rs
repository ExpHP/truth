use std::io::{self, Write, Seek, Read, SeekFrom};
use std::path::{Path, PathBuf};
use std::fs;

use byteorder::{LittleEndian as Le, ReadBytesExt, WriteBytesExt};

use crate::pos::Sp;
use crate::diagnostic::{self, Diagnostic, Emitter, RootEmitter};
use crate::error::{ErrorReported};

// Binary file IO uses anyhow instead of codespan_reporting because most span info is lost
// in the lowered form.
pub type ReadError = crate::error::ErrorReported;
pub type WriteError = crate::error::ErrorReported;
pub type ReadResult<T> = Result<T, ReadError>;
pub type WriteResult<T = ()> = Result<T, WriteError>;

/// String bytes encoded using the user's selected binary string encoding.
///
/// This is a wrapper around `Vec<u8>` to help ensure that string encoding/decoding
/// is done using the correct encoding, and not through accidental or habitual usage of
/// `std::str::from_utf8` and `str::as_bytes`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Encoded(Vec<u8>);

pub type Encoding = &'static encoding_rs::Encoding;

pub use encoding_rs::SHIFT_JIS as DEFAULT_ENCODING;

impl Encoded {
    pub fn encode<S: AsRef<str> + ?Sized>(str: &Sp<S>, enc: Encoding) -> Result<Self, Diagnostic> {
        match enc.encode(str.value.as_ref()) {
            (_, _, true) => Err(error!(
                message("string encoding error"),
                primary(str, "cannot be encoded using '{}'", enc.name()),
            )),

            (bytes, _, _) => Ok(Encoded(bytes.into_owned())),
        }
    }

    pub fn decode(&self, enc: Encoding) -> Result<String, Diagnostic> {
        match enc.decode_without_bom_handling(self.0.as_ref()) {
            (_, true) => Err(error!("could not read string using encoding '{}'", enc.name())),
            (str, _) => Ok(str.into_owned().into()),
        }
    }

    pub fn len(&self) -> usize { self.0.len() }
}

// =================================================================================================

/// Trait alias that allows the creation of a `dyn Read + Seek`.
pub trait DynReadSeek: Read + Seek {}
/// Trait alias that allows the creation of a `dyn Write + Seek`.
pub trait DynWriteSeek: Write + Seek {}

impl<R: Read + Seek> DynReadSeek for R {}
impl<W: Write + Seek> DynWriteSeek for W {}

// =================================================================================================

/// Helper to simplify functions that read from Touhou's binary script files.
///
/// Implements [`BinRead`] with automatic handling of diagnostics.
pub struct BinReader<'a, R: Read + Seek + ?Sized = dyn DynReadSeek + 'a> {
    /// Emitter with no additional context beyond the filename.
    fname_emitter: diagnostic::WhileReading<'a>,
    display_filename: String,
    reader: R,
}

/// Helper to simplify functions that write binary script files for Touhou.
///
/// Implements [`BinWrite`] with automatic handling of diagnostics.
pub struct BinWriter<'a, W: Write + Seek + ?Sized = dyn DynWriteSeek + 'a> {
    /// Emitter with no additional context beyond the filename.
    fname_emitter: diagnostic::WhileWriting<'a>,
    writer: W,
}

// -------------
// from/to inner

impl<'a, R: Read + Seek + 'a> BinReader<'a, R> {
    pub fn from_reader(root_emitter: &'a RootEmitter, filename: &str, reader: R) -> Self {
        let fname_emitter = root_emitter.while_reading(filename);
        BinReader { fname_emitter, reader, display_filename: filename.to_owned() }
    }

    pub fn map_reader<R2: Read + Seek + 'a>(self, func: impl FnOnce(R) -> R2) -> BinReader<'a, R2> {
        let BinReader { fname_emitter: emitter, reader, display_filename } = self;
        BinReader { fname_emitter: emitter, reader: func(reader), display_filename }
    }
    pub fn into_inner(self) -> R { self.reader }
}

impl<'a, W: Write + Seek + 'a> BinWriter<'a, W> {
    pub fn from_writer(root_emitter: &'a RootEmitter, filename: &str, writer: W) -> Self {
        let fname_emitter = root_emitter.while_writing(filename);
        BinWriter { fname_emitter, writer }
    }

    pub fn map_writer<W2: Write + Seek + 'a>(self, func: impl FnOnce(W) -> W2) -> BinWriter<'a, W2> {
        let BinWriter { fname_emitter: emitter, writer } = self;
        BinWriter { fname_emitter: emitter, writer: func(writer) }
    }
    pub fn into_inner(self) -> W { self.writer }
}

impl<'a, R: Read + Seek + ?Sized + 'a> BinReader<'a, R> {
    pub fn emitter(&self) -> impl Emitter + 'a { self.fname_emitter.clone() }
    pub fn inner_mut(&mut self) -> &mut R { &mut self.reader }
    pub fn display_filename(&self) -> &str { &self.display_filename }
}

impl<'a, W: Write + Seek + ?Sized + 'a> BinWriter<'a, W> {
    pub fn emitter(&self) -> impl Emitter + 'a { self.fname_emitter.clone() }
    pub fn inner_mut(&mut self) -> &mut W { &mut self.writer }
}

// =============================================================================
// Other IO wrappers.

/// Helper that wraps some functions and methods from [`std::fs`].
#[derive(Debug, Copy, Clone)]
pub struct Fs<'ctx> {
    pub emitter: &'ctx RootEmitter,
}

impl<'ctx> Fs<'ctx> {
    pub fn new(emitter: &'ctx RootEmitter) -> Self { Fs { emitter } }

    /// Wraps [`std::fs::write`].
    pub fn write(&self, path: &Path, data: impl AsRef<[u8]>) -> WriteResult {
        std::fs::write(path, data)
            .map_err(|e| self.emitter.emit(error!("while writing file '{}': {}", path.display(), e)))
    }

    /// Wraps [`std::fs::read`].
    pub fn read(&self, path: &Path) -> ReadResult<Vec<u8>> {
        std::fs::read(path)
            .map_err(|e| self.emitter.emit(error!("while reading file '{}': {}", path.display(), e)))
    }

    /// Wraps [`std::fs::read_to_string`].
    pub fn read_to_string(&self, path: &Path) -> ReadResult<String> {
        std::fs::read_to_string(path)
            .map_err(|e| self.emitter.emit(error!("while reading file '{}': {}", path.display(), e)))
    }

    /// Reads all contents of a file upfront and returns a [`BinReader`] for deserializing the bytes from memory.
    ///
    /// This is generally the preferred way to work with [`BinReader`], as reading the game's binary files requires
    /// a lot of seeking, and the size of these files is already constrained by limitations of the games.
    pub fn open_read(&self, path: impl AsRef<Path>) -> ReadResult<BinReader<'ctx, io::Cursor<Vec<u8>>>> {
        let path = path.as_ref();
        let bytes = self.read(path)?;
        let path_string = path.display().to_string();

        Ok(BinReader::from_reader(self.emitter, &path_string, io::Cursor::new(bytes)))
    }

    /// Open a file handle for reading and wrap it in a [`BinReader`].
    pub fn open(&self, path: impl AsRef<Path>) -> ReadResult<BinReader<'ctx, fs::File>> {
        let path = path.as_ref();
        let path_string = path.display().to_string();
        let file = std::fs::File::open(path)
            .map_err(|e| self.emitter.emit(error!("while opening file '{}': {}", path_string, e)))?;

        Ok(BinReader::from_reader(self.emitter, &path_string, file))
    }

    /// Create a file and wrap a buffered write handle in a [`BinWriter`].
    ///
    /// This is the preferred way to open files for writing.
    pub fn create_buffered(&self, path: impl AsRef<Path>) -> WriteResult<BinWriter<'ctx, io::BufWriter<fs::File>>> {
        Ok(self.create(path)?.map_writer(io::BufWriter::new))
    }

    /// Create a file and wrap a write handle in a [`BinWriter`].
    pub fn create(&self, path: impl AsRef<Path>) -> WriteResult<BinWriter<'ctx, fs::File>> {
        let path = path.as_ref();
        let path_string = path.display().to_string();
        let file = fs::File::create(path)
            .map_err(|e| self.emitter.emit(error!("while creating file '{}': {}", path_string, e)))?;

        Ok(BinWriter::from_writer(self.emitter, &path_string, file))
    }

    pub fn canonicalize(&self, path: &Path) -> Result<PathBuf, Diagnostic> {
        path.canonicalize().map_err(|e| error!("while resolving '{}': {}", path.display(), e))
    }

    /// Make a path user-friendly (e.g. automatically change to relative or absolute
    /// based on location).  Conversion may be lossy.
    pub fn display_path(&self, path: &Path) -> String {
        nice_display_path(path)
    }
}

/// Make a path "nice" for display, *if possible*.
pub(crate) fn nice_display_path(path: impl AsRef<Path>) -> String {
    let path = path.as_ref();
    nice_or_bust(path).unwrap_or_else(|| path.to_string_lossy().into_owned())
}

fn nice_or_bust(path: impl AsRef<Path>) -> Option<String> {
    let cwd = std::env::current_dir().ok()?;
    let absolute = cwd.join(path.as_ref());

    // (just bail if it's not a child. "../../../other/place" would hardly be nice.)
    let relative = absolute.strip_prefix(&cwd).ok()?;
    Some(relative.to_string_lossy().into_owned())
}

// =============================================================================

/// Helper trait to simplify functions that read from Touhou's binary script files.
///
/// All functions read little endian (because all of the game's binary formats are little endian),
/// and simpler versions of the Seek API are provided (because the formats are full of offsets).
pub trait BinRead {
    type Reader: Read + Seek + ?Sized;
    type Err;

    fn _bin_read_io_error(&mut self, err: io::Error) -> Self::Err;
    fn _bin_read_reader(&mut self) -> &mut Self::Reader;

    fn read_i8(&mut self) -> Result<i8, Self::Err> { ReadBytesExt::read_i8(self._bin_read_reader()).map_err(|e| self._bin_read_io_error(e)) }
    fn read_u8(&mut self) -> Result<u8, Self::Err> { ReadBytesExt::read_u8(self._bin_read_reader()).map_err(|e| self._bin_read_io_error(e)) }
    fn read_i16(&mut self) -> Result<i16, Self::Err> { ReadBytesExt::read_i16::<Le>(self._bin_read_reader()).map_err(|e| self._bin_read_io_error(e)) }
    fn read_u16(&mut self) -> Result<u16, Self::Err> { ReadBytesExt::read_u16::<Le>(self._bin_read_reader()).map_err(|e| self._bin_read_io_error(e)) }
    fn read_i32(&mut self) -> Result<i32, Self::Err> { ReadBytesExt::read_i32::<Le>(self._bin_read_reader()).map_err(|e| self._bin_read_io_error(e)) }
    fn read_u32(&mut self) -> Result<u32, Self::Err> { ReadBytesExt::read_u32::<Le>(self._bin_read_reader()).map_err(|e| self._bin_read_io_error(e)) }
    fn read_f32(&mut self) -> Result<f32, Self::Err> { ReadBytesExt::read_f32::<Le>(self._bin_read_reader()).map_err(|e| self._bin_read_io_error(e)) }

    fn read_f32s_2(&mut self) -> Result<[f32; 2], Self::Err> {
        Ok([self.read_f32()?, self.read_f32()?])
    }
    fn read_f32s_3(&mut self) -> Result<[f32; 3], Self::Err> {
        Ok([self.read_f32()?, self.read_f32()?, self.read_f32()?])
    }

    fn read_byte_vec(&mut self, len: usize) -> Result<Vec<u8>, Self::Err> {
        let mut buf = vec![0; len];
        self.read_exact(&mut buf)?;
        Ok(buf)
    }

    fn read_exact(&mut self, out: &mut [u8]) -> Result<(), Self::Err> {
        io::Read::read_exact(self._bin_read_reader(), out).map_err(|e| self._bin_read_io_error(e))
    }

    /// Reads a null-terminated string that is zero-padded to a multiple of the given block-size.
    /// (a common pattern in ZUN's script files)
    ///
    /// All trailing nulls will be stripped from the returned string, but the reader will always
    /// be advanced by a multiple of `block_size` bytes.
    ///
    /// This method expects that the string is zero-padded to the given block-size (similar to
    /// the output of [`BinWrite::write_cstring`]), so it only checks the last byte in each block
    /// for a null terminator.  Due to these properties, it is possible for the returned string
    /// to contain an interior null byte for maliciously crafted inputs.
    fn read_cstring_blockwise(&mut self, block_size: usize) -> Result<Encoded, Self::Err> {
        assert_ne!(block_size, 0);

        let mut out = vec![];
        while out.last() != Some(&0) {
            let old_end = out.len();
            out.resize(old_end + block_size, 0);

            self.read_exact(&mut out[old_end..])?;
        }

        while out.last() == Some(&0) {
            out.pop();
        }
        Ok(Encoded(out))
    }

    /// Reads the given number of bytes as a masked string, where the null bytes are also masked.
    ///
    /// This reads exactly the given number of bytes, then xors every byte with a mask,
    /// and finally trims trailing nulls.  The returned value may contain interior nulls.
    ///
    /// The returned string will be less than `num_bytes` long due to the trimming of nulls.
    fn read_cstring_masked_exact(&mut self, num_bytes: usize, mask: u8) -> Result<Encoded, Self::Err> {
        let mut out = self.read_byte_vec(num_bytes)?;
        for byte in &mut out {
            *byte ^= mask;
        }
        while out.last() == Some(&0) {
            out.pop();
        }
        Ok(Encoded(out))
    }

    fn pos(&mut self) -> Result<u64, Self::Err> {
        self._bin_read_reader().seek(SeekFrom::Current(0)).map_err(|e| self._bin_read_io_error(e))
    }
    fn seek_to(&mut self, offset: u64) -> Result<(), Self::Err> {
        self._bin_read_reader().seek(SeekFrom::Start(offset)).map_err(|e| self._bin_read_io_error(e))?;
        Ok(())
    }
}

impl<'a, R: Read + Seek + ?Sized + 'a> BinReader<'a, R> {
    pub fn expect_magic(&mut self, emitter: &impl Emitter, magic: &str) -> ReadResult<()> {
        let mut read_bytes = vec![0; magic.len()];
        self.read_exact(&mut read_bytes)?;

        if read_bytes != magic.as_bytes() {
            return Err(emitter.emit(error!("failed to find magic: '{}'", magic)));
        }
        Ok(())
    }
}

/// Returns the number of bytes that would be read by [`BinRead::read_cstring`], or written by
/// [`BinWrite::write_cstring`] and [`BinWrite::write_cstring_masked`].
pub fn cstring_num_bytes(string_len: usize, block_size: usize) -> usize {
    let min_size = string_len + 1;  // NUL terminator

    // basically a ceiling divide
    match min_size % block_size {
        0 => min_size,
        r => min_size + block_size - r,
    }
}

/// Helper trait to simplify functions that write to Touhou's binary script files.
///
/// All functions read little endian (because all of the game's binary formats are little endian),
/// and simpler versions of the Seek API are provided (because the formats are full of offsets).
pub trait BinWrite {
    type Writer: Write + Seek + ?Sized;
    type Err;

    fn _bin_write_io_error(&mut self, err: io::Error) -> Self::Err;
    fn _bin_write_writer(&mut self) -> &mut Self::Writer;

    fn write_i8(&mut self, x: i8) -> Result<(), Self::Err> { WriteBytesExt::write_i8(self._bin_write_writer(), x).map_err(|e| self._bin_write_io_error(e)) }
    fn write_u8(&mut self, x: u8) -> Result<(), Self::Err> { WriteBytesExt::write_u8(self._bin_write_writer(), x).map_err(|e| self._bin_write_io_error(e)) }
    fn write_i16(&mut self, x: i16) -> Result<(), Self::Err> { WriteBytesExt::write_i16::<Le>(self._bin_write_writer(), x).map_err(|e| self._bin_write_io_error(e)) }
    fn write_u16(&mut self, x: u16) -> Result<(), Self::Err> { WriteBytesExt::write_u16::<Le>(self._bin_write_writer(), x).map_err(|e| self._bin_write_io_error(e)) }
    fn write_i32(&mut self, x: i32) -> Result<(), Self::Err> { WriteBytesExt::write_i32::<Le>(self._bin_write_writer(), x).map_err(|e| self._bin_write_io_error(e)) }
    fn write_u32(&mut self, x: u32) -> Result<(), Self::Err> { WriteBytesExt::write_u32::<Le>(self._bin_write_writer(), x).map_err(|e| self._bin_write_io_error(e)) }
    fn write_f32(&mut self, x: f32) -> Result<(), Self::Err> { WriteBytesExt::write_f32::<Le>(self._bin_write_writer(), x).map_err(|e| self._bin_write_io_error(e)) }

    fn write_all(&mut self, bytes: &[u8]) -> Result<(), Self::Err> {
        io::Write::write_all(self._bin_write_writer(), bytes).map_err(|e| self._bin_write_io_error(e))
    }

    /// Writes a null-terminated string, zero-padding it to a multiple of the given `block_size`.
    fn write_cstring(&mut self, s: &Encoded, block_size: usize) -> Result<(), Self::Err> {
        self.write_cstring_masked(s, block_size, 0)
    }

    /// Writes a null-terminated string, zero-padding it to a multiple of the given `block_size`,
    /// then xor-ing every byte (including the nulls) with a mask.
    fn write_cstring_masked(&mut self, s: &Encoded, block_size: usize, mask: u8) -> Result<(), Self::Err> {
        let mut to_write = s.0.to_vec();
        let final_len = cstring_num_bytes(to_write.len(), block_size);
        to_write.resize(final_len, 0);

        for byte in &mut to_write {
            *byte ^= mask;
        }
        BinWrite::write_all(self, &to_write)?;
        Ok(())
    }

    fn write_u32s(&mut self, xs: &[u32]) -> Result<(), Self::Err> {
        xs.iter().copied().map(|x| self.write_u32(x)).collect()
    }
    fn write_f32s(&mut self, xs: &[f32]) -> Result<(), Self::Err> {
        xs.iter().copied().map(|x| self.write_f32(x)).collect()
    }

    fn pos(&mut self) -> Result<u64, Self::Err> {
        self._bin_write_writer().seek(SeekFrom::Current(0)).map_err(|e| self._bin_write_io_error(e))
    }
    fn seek_to(&mut self, offset: u64) -> Result<(), Self::Err> {
        self._bin_write_writer().seek(SeekFrom::Start(offset)).map_err(|e| self._bin_write_io_error(e))?;
        Ok(())
    }
}

// =============================================================================

impl<'a, R: Read + Seek + ?Sized + 'a> BinRead for BinReader<'a, R> {
    type Err = ErrorReported;
    type Reader = R;

    fn _bin_read_io_error(&mut self, err: io::Error) -> Self::Err {
        // This deliberately uses the base emitter to print just the filename (without any more context) since
        // it's for things like access errors and EoF errors.
        self.fname_emitter.emit(error!("{}", err))
    }
    fn _bin_read_reader(&mut self) -> &mut Self::Reader { &mut self.reader }
}

impl<'a, W: Write + Seek + ?Sized + 'a> BinWrite for BinWriter<'a, W> {
    type Err = ErrorReported;
    type Writer = W;

    fn _bin_write_io_error(&mut self, err: io::Error) -> Self::Err {
        // This deliberately uses the base emitter to print just the filename (without any more context) since
        // it's for things like access errors and EoF errors.
        self.fname_emitter.emit(error!("{}", err))
    }
    fn _bin_write_writer(&mut self) -> &mut Self::Writer { &mut self.writer }
}

impl<R: Read + Seek + ?Sized> BinRead for R {
    type Err = io::Error;
    type Reader = R;

    fn _bin_read_io_error(&mut self, err: io::Error) -> Self::Err { err }
    fn _bin_read_reader(&mut self) -> &mut Self::Reader { self }
}

impl<W: Write + Seek + ?Sized> BinWrite for W {
    type Err = io::Error;
    type Writer = W;

    fn _bin_write_io_error(&mut self, err: io::Error) -> Self::Err { err }
    fn _bin_write_writer(&mut self) -> &mut Self::Writer { self }
}

// =============================================================================

#[test]
fn test_cstring_io() {
    fn check(block_size: usize, bytes: &[u8], encoded: Vec<u8>) {
        // check length function
        assert_eq!(cstring_num_bytes(bytes.len(), block_size), encoded.len());

        // check writing
        let emitter = RootEmitter::new_stderr();
        let mut w = BinWriter::from_writer(&emitter, "test".into(), std::io::Cursor::new(vec![]));
        w.write_cstring(&Encoded(bytes.to_vec()), block_size).unwrap();
        assert_eq!(encoded, w.into_inner().into_inner());

        // check reading
        let mut longer_padded = encoded.clone();  // have a longer vec so we can be sure it stops on its own
        longer_padded.extend(vec![0; 10]);

        let mut r = std::io::Cursor::new(longer_padded);
        let read_back = r.read_cstring_blockwise(block_size).unwrap();
        assert_eq!(bytes, &read_back.0[..]);  // make sure it dropped the nul bytes
        assert_eq!(encoded.len() as u64, BinRead::pos(&mut r).unwrap());
    }

    check(4, &[], vec![0, 0, 0, 0]);
    check(4, &[1], vec![1, 0, 0, 0]);
    check(4, &[1, 2], vec![1, 2, 0, 0]);
    check(4, &[1, 2, 3], vec![1, 2, 3, 0]);
    check(4, &[1, 2, 3, 4], vec![1, 2, 3, 4, 0, 0, 0, 0]);
    check(4, &[1, 2, 3, 4, 5], vec![1, 2, 3, 4, 5, 0, 0, 0]);
}

#[test]
fn test_masked_cstring() {
    fn check(mask: u8, block_size: usize, bytes: &[u8], encoded: Vec<u8>) {
        // check writing
        let mut w = std::io::Cursor::new(vec![]);
        w.write_cstring_masked(&Encoded(bytes.to_vec()), block_size, mask).unwrap();
        assert_eq!(encoded, w.into_inner());

        // check reading
        let mut longer_padded = encoded.clone();  // have a longer vec so we can be sure it stops on its own
        longer_padded.extend(vec![mask; 10]);

        let mut r = std::io::Cursor::new(longer_padded);
        let read_back = r.read_cstring_masked_exact(encoded.len(), mask).unwrap();
        assert_eq!(bytes, &read_back.0[..]);  // make sure it dropped the nul bytes
        assert_eq!(encoded.len() as u64, BinRead::pos(&mut r).unwrap());
    }

    check(0x77, 4, &[1, 2, 3], vec![0x76, 0x75, 0x74, 0x77]);
    check(0x77, 4, &[1, 2, 3, 4], vec![0x76, 0x75, 0x74, 0x73, 0x77, 0x77, 0x77, 0x77]);
}
