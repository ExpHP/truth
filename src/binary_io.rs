use std::io::{Write, Seek, Read, SeekFrom};
use byteorder::{LittleEndian as Le, ReadBytesExt, WriteBytesExt};
use bstr::BString;

pub use anyhow::bail;

// Binary file IO uses anyhow instead of codespan_reporting because most span info is lost
// in the lowered form.
pub type ReadError = anyhow::Error;
pub type WriteError = anyhow::Error;
pub type ReadResult<T> = Result<T, ReadError>;
pub type WriteResult<T = ()> = Result<T, WriteError>;

pub trait BinRead: Read {
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

    /// Will consume blocks of the given size until a null terminator is found.
    fn read_cstring(&mut self, block_size: usize) -> ReadResult<BString> {
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
        Ok(out.into())
    }

    fn expect_magic(&mut self, magic: &str) -> ReadResult<()> {
        let mut read_bytes = vec![0; magic.len()];
        self.take(magic.len() as u64).read_exact(&mut read_bytes)?;

        if read_bytes != magic.as_bytes() {
            bail!("failed to find magic: '{}'", magic);
        }
        Ok(())
    }
}

// Seek is needed because some formats contain offsets.
pub trait BinWrite: Write + Seek {
    fn write_i8(&mut self, x: i8) -> WriteResult { WriteBytesExt::write_i8(self, x).map_err(Into::into) }
    fn write_u8(&mut self, x: u8) -> WriteResult { WriteBytesExt::write_u8(self, x).map_err(Into::into) }
    fn write_i16(&mut self, x: i16) -> WriteResult { WriteBytesExt::write_i16::<Le>(self, x).map_err(Into::into) }
    fn write_u16(&mut self, x: u16) -> WriteResult { WriteBytesExt::write_u16::<Le>(self, x).map_err(Into::into) }
    fn write_i32(&mut self, x: i32) -> WriteResult { WriteBytesExt::write_i32::<Le>(self, x).map_err(Into::into) }
    fn write_u32(&mut self, x: u32) -> WriteResult { WriteBytesExt::write_u32::<Le>(self, x).map_err(Into::into) }
    fn write_f32(&mut self, x: f32) -> WriteResult { WriteBytesExt::write_f32::<Le>(self, x).map_err(Into::into) }

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

impl<R: Read> BinRead for R {}
impl<R: Write + Seek> BinWrite for R {}
