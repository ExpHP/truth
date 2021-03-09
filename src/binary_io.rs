use std::io::{Write, Seek, Read, SeekFrom};

use byteorder::{LittleEndian as Le, ReadBytesExt, WriteBytesExt};

pub use anyhow::bail;

use crate::pos::Sp;

// Binary file IO uses anyhow instead of codespan_reporting because most span info is lost
// in the lowered form.
pub type ReadError = crate::error::SimpleError;
pub type WriteError = crate::error::SimpleError;
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
    pub fn encode<S: AsRef<str> + ?Sized>(str: &Sp<S>, enc: Encoding) -> Result<Self, crate::error::CompileError> {
        match enc.encode(str.value.as_ref()) {
            (_, _, true) => Err(error!(
                message("string encoding error"),
                primary(str, "cannot be encoded using '{}'", enc.name()),
            )),

            (bytes, _, _) => Ok(Encoded(bytes.into_owned())),
        }
    }

    pub fn decode(&self, enc: Encoding) -> Result<String, crate::error::SimpleError> {
        match enc.decode_without_bom_handling(self.0.as_ref()) {
            (_, true) => bail!("could not read string using encoding '{}'", enc.name()),
            (str, _) => Ok(str.into_owned().into()),
        }
    }

    pub fn len(&self) -> usize { self.0.len() }
}

/// Helper extension trait to simplify functions that read from Touhou's binary script files.
///
/// All functions read little endian (because all of the game's binary formats are little endian),
/// and simpler versions of the Seek API are provided (because the formats are full of offsets).
pub trait BinRead: Read + Seek {
    fn read_i8(&mut self) -> ReadResult<i8> { ReadBytesExt::read_i8(self).map_err(Into::into) }
    fn read_u8(&mut self) -> ReadResult<u8> { ReadBytesExt::read_u8(self).map_err(Into::into) }
    fn read_i16(&mut self) -> ReadResult<i16> { ReadBytesExt::read_i16::<Le>(self).map_err(Into::into) }
    fn read_u16(&mut self) -> ReadResult<u16> { ReadBytesExt::read_u16::<Le>(self).map_err(Into::into) }
    fn read_i32(&mut self) -> ReadResult<i32> { ReadBytesExt::read_i32::<Le>(self).map_err(Into::into) }
    fn read_u32(&mut self) -> ReadResult<u32> { ReadBytesExt::read_u32::<Le>(self).map_err(Into::into) }
    fn read_f32(&mut self) -> ReadResult<f32> { ReadBytesExt::read_f32::<Le>(self).map_err(Into::into) }

    fn read_f32s_2(&mut self) -> ReadResult<[f32; 2]> {
        Ok([self.read_f32()?, self.read_f32()?])
    }
    fn read_f32s_3(&mut self) -> ReadResult<[f32; 3]> {
        Ok([self.read_f32()?, self.read_f32()?, self.read_f32()?])
    }

    fn read_byte_vec(&mut self, len: usize) -> ReadResult<Vec<u8>> {
        let mut buf = vec![0; len];
        self.read_exact(&mut buf)?;
        Ok(buf)
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
    fn read_cstring_blockwise(&mut self, block_size: usize) -> ReadResult<Encoded> {
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
    fn read_cstring_masked_exact(&mut self, num_bytes: usize, mask: u8) -> WriteResult<Encoded> {
        let mut out = self.read_byte_vec(num_bytes)?;
        for byte in &mut out {
            *byte ^= mask;
        }
        while out.last() == Some(&0) {
            out.pop();
        }
        Ok(Encoded(out))
    }

    fn expect_magic(&mut self, magic: &str) -> ReadResult<()> {
        let mut read_bytes = vec![0; magic.len()];
        self.take(magic.len() as u64).read_exact(&mut read_bytes)?;

        if read_bytes != magic.as_bytes() {
            bail!("failed to find magic: '{}'", magic);
        }
        Ok(())
    }

    fn pos(&mut self) -> ReadResult<u64> {
        self.seek(SeekFrom::Current(0)).map_err(Into::into)
    }
    fn seek_to(&mut self, offset: u64) -> ReadResult<()> {
        self.seek(SeekFrom::Start(offset))?;
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

/// Helper extension trait to simplify functions that write binary script files for Touhou.
///
/// All functions read little endian (because all of the game's binary formats are little endian),
/// and simpler versions of the Seek API are provided (because the formats are full of offsets).
pub trait BinWrite: Write + Seek {
    fn write_i8(&mut self, x: i8) -> WriteResult { WriteBytesExt::write_i8(self, x).map_err(Into::into) }
    fn write_u8(&mut self, x: u8) -> WriteResult { WriteBytesExt::write_u8(self, x).map_err(Into::into) }
    fn write_i16(&mut self, x: i16) -> WriteResult { WriteBytesExt::write_i16::<Le>(self, x).map_err(Into::into) }
    fn write_u16(&mut self, x: u16) -> WriteResult { WriteBytesExt::write_u16::<Le>(self, x).map_err(Into::into) }
    fn write_i32(&mut self, x: i32) -> WriteResult { WriteBytesExt::write_i32::<Le>(self, x).map_err(Into::into) }
    fn write_u32(&mut self, x: u32) -> WriteResult { WriteBytesExt::write_u32::<Le>(self, x).map_err(Into::into) }
    fn write_f32(&mut self, x: f32) -> WriteResult { WriteBytesExt::write_f32::<Le>(self, x).map_err(Into::into) }

    /// Writes a null-terminated string, zero-padding it to a multiple of the given `block_size`.
    fn write_cstring(&mut self, s: &Encoded, block_size: usize) -> WriteResult<()> {
        self.write_cstring_masked(s, block_size, 0)
    }

    /// Writes a null-terminated string, zero-padding it to a multiple of the given `block_size`,
    /// then xor-ing every byte (including the nulls) with a mask.
    fn write_cstring_masked(&mut self, s: &Encoded, block_size: usize, mask: u8) -> WriteResult<()> {
        let mut to_write = s.0.to_vec();
        let final_len = cstring_num_bytes(to_write.len(), block_size);
        to_write.resize(final_len, 0);

        for byte in &mut to_write {
            *byte ^= mask;
        }
        self.write_all(&to_write)?;
        Ok(())
    }

    fn write_u32s(&mut self, xs: &[u32]) -> WriteResult {
        xs.iter().copied().map(|x| self.write_u32(x)).collect()
    }
    fn write_f32s(&mut self, xs: &[f32]) -> WriteResult {
        xs.iter().copied().map(|x| self.write_f32(x)).collect()
    }
    fn pos(&mut self) -> WriteResult<u64> {
        self.seek(SeekFrom::Current(0)).map_err(Into::into)
    }
    fn seek_to(&mut self, offset: u64) -> WriteResult {
        self.seek(SeekFrom::Start(offset))?;
        Ok(())
    }
}

impl<R: Read + Seek> BinRead for R {}
impl<R: Write + Seek> BinWrite for R {}


#[test]
fn test_cstring_io() {
    fn check(block_size: usize, bytes: &[u8], encoded: Vec<u8>) {
        // check length function
        assert_eq!(cstring_num_bytes(bytes.len(), block_size), encoded.len());

        // check writing
        let mut w = std::io::Cursor::new(vec![]);
        w.write_cstring(&Encoded(bytes.to_vec()), block_size).unwrap();
        assert_eq!(encoded, w.into_inner());

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
