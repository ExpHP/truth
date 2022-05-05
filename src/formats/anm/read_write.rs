use std::num::NonZeroU64;
use std::collections::HashSet;

use indexmap::{IndexSet, IndexMap};

use crate::io::{BinRead, BinWrite, BinReader, BinWriter, Encoded, ReadResult, WriteResult, DEFAULT_ENCODING};
use crate::diagnostic::{Emitter};
use crate::error::{ErrorReported};
use crate::game::{Game};
use crate::image::ColorFormat;
use crate::llir::{self, ReadInstr, RawInstr, InstrFormat};

use super::{AnmFile, Entry, EntrySpecs, Sprite, Script, Version, TextureData, TextureMetadata};

#[derive(Debug, Clone)]
struct EntryHeaderData {
    version: u32,
    num_sprites: u32,
    num_scripts: u32,
    rt_width: u32,
    rt_height: u32,
    rt_format: u32,
    name_offset: u64,
    secondary_name_offset: Option<NonZeroU64>, // EoSD only?
    colorkey: u32, // Only in old format
    offset_x: u32,
    offset_y: u32,
    memory_priority: u32,
    thtx_offset: Option<NonZeroU64>,
    has_data: u32,
    low_res_scale: u32,
    next_offset: u64,
}

pub fn read_anm(
    reader: &mut BinReader,
    emitter: &impl Emitter,
    game: Game,
    with_images: bool,
) -> ReadResult<AnmFile> {
    let format = FileFormat::from_game(game);

    let mut entries = vec![];
    let mut next_script_index = 0;
    let mut entry_positions = Default::default();
    loop {
        let (entry, control_flow) = read_entry(reader, emitter, &format, with_images, &mut entry_positions, &mut next_script_index)?;
        entries.push(entry);
        match control_flow {
            ControlFlow::Continue => {},
            ControlFlow::Stop => break,
        }
    }

    let binary_filename = Some(reader.display_filename().to_string());
    let mut anm = AnmFile { entries, binary_filename };
    super::strip_unnecessary_sprite_ids(anm.entries.iter_mut().map(|e| &mut e.sprites));
    Ok(anm)
}

fn read_entry(
    reader: &mut BinReader,
    emitter: &impl Emitter,
    format: &FileFormat,
    with_images: bool,
    entry_positions: &mut HashSet<crate::raw::BytePos>,
    next_script_index: &mut u32,
) -> ReadResult<(Entry, ControlFlow)> {
    let instr_format = &*format.instr_format;

    let entry_pos = reader.pos()?;
    if entry_positions.contains(&entry_pos) {
        return Err(emitter.emit(error!("loop in entries beginning at file offset {:#X}", entry_pos)));
    }
    entry_positions.insert(entry_pos);

    // 64 byte header regardless of version
    let header_data = emitter.chain_with(|f| write!(f, "in header"), |emitter| {
        let header_data = format.read_header(reader, emitter)?;
        if header_data.has_data != header_data.has_data % 2 {
            emitter.emit(warning!("non-boolean value found for 'has_data': {}", header_data.has_data)).ignore();
        }
        if header_data.low_res_scale != header_data.low_res_scale % 2 {
            emitter.emit(warning!("non-boolean value found for 'low_res_scale': {}", header_data.low_res_scale)).ignore();
        }
        Ok(header_data)
    })?;

    let sprite_offsets = reader.read_u32s(header_data.num_sprites as usize)?;
    let script_ids_and_offsets = (0..header_data.num_scripts).map(|_| {
        Ok((reader.read_i32()?, reader.read_u32()? as u64))
    }).collect::<ReadResult<Vec<_>>>()?;
    // eprintln!("{:?}", header_data);
    // eprintln!("{:?}", sprite_offsets);
    // eprintln!("{:?}", script_ids_and_offsets);

    reader.seek_to(entry_pos + header_data.name_offset)?;
    let path = reader.read_cstring_blockwise(16)?.decode(DEFAULT_ENCODING).map_err(|e| emitter.emit(e))?;
    let path_2 = match header_data.secondary_name_offset {
        None => None,
        Some(n) => {
            reader.seek_to(entry_pos + n.get())?;
            Some(reader.read_cstring_blockwise(16)?.decode(DEFAULT_ENCODING).map_err(|e| emitter.emit(e))?)
        },
    };

    let mut sprites_seen_in_entry = IndexSet::new();
    let sprites = sprite_offsets.iter().map(|&offset| {
        reader.seek_to(entry_pos + offset as u64)?;
        let sprite = read_sprite(reader)?;
        let sprite_id = sprite.id.expect("(bug!) sprite read from binary must always have id");

        // Note: Duplicate IDs do happen between different entries, so we don't check that.
        if !sprites_seen_in_entry.insert(sprite_id) {
            emitter.emit(warning!("sprite ID {} appeared twice in same entry; only one will be kept", sprite_id)).ignore();
        }
        let key = sp!(super::auto_sprite_name(sprite_id as u32));

        Ok((key, sprite))
    }).collect::<ReadResult<IndexMap<_, _>>>()?;

    // We need to know all the possible offsets at which a script may end.
    // Why?  Blame StB.
    let mut all_offsets = vec![header_data.name_offset];
    all_offsets.extend(header_data.thtx_offset.map(NonZeroU64::get));
    all_offsets.extend(header_data.secondary_name_offset.map(NonZeroU64::get));
    all_offsets.extend(sprite_offsets.iter().map(|&offset| offset as u64));
    all_offsets.extend(script_ids_and_offsets.iter().map(|&(_, offset)| offset as u64));

    let scripts = script_ids_and_offsets.iter().map(|&(id, offset)| {
        let script_index = *next_script_index;
        let key = sp!(super::auto_script_name(script_index));
        *next_script_index += 1;

        let end_offset = all_offsets.iter().copied().filter(|&x| x > offset).min();

        let instrs = {
            reader.seek_to(entry_pos + offset)?;
            emitter.chain_with(|f| write!(f, "script {}", script_index), |emitter| {
                llir::read_instrs(reader, emitter, instr_format, offset, end_offset)
            })?
        };
        Ok((key, Script { id, instrs }))
    }).collect::<ReadResult<IndexMap<_, _>>>()?;

    let expect_no_texture = header_data.has_data == 0 || path.starts_with("@");
    if expect_no_texture != header_data.thtx_offset.is_none() {
        return Err(emitter.emit(error!("inconsistency between thtx_offset and has_data/name")));
    }

    let (texture_metadata, texture_data) = match header_data.thtx_offset {
        None => (None, None),
        Some(n) => {
            reader.seek_to(entry_pos + n.get())?;
            let (texture_metadata, maybe_texture_data) = read_texture(reader, emitter, with_images)?;
            (Some(texture_metadata), maybe_texture_data)
        },
    };
    let specs = EntrySpecs {
        rt_width: header_data.rt_width,
        rt_height: header_data.rt_height,
        rt_format: header_data.rt_format,
        colorkey: header_data.colorkey,
        offset_x: header_data.offset_x, offset_y: header_data.offset_y,
        memory_priority: header_data.memory_priority,
        low_res_scale: header_data.low_res_scale != 0,
    };

    let entry = Entry {
        path: sp!(path),
        path_2: path_2.map(|x| sp!(x)),
        texture_data, texture_metadata,
        specs, sprites, scripts
    };

    reader.seek_to(entry_pos + header_data.next_offset)?;
    match header_data.next_offset {
        0 => Ok((entry, ControlFlow::Stop)),
        _ => Ok((entry, ControlFlow::Continue)),
    }
}

enum ControlFlow { Stop, Continue }

// =============================================================================

pub fn write_anm(
    w: &mut BinWriter,
    emitter: &impl Emitter,
    game: Game,
    file: &AnmFile,
) -> WriteResult {
    let format = FileFormat::from_game(game);

    let mut last_entry_pos = None;
    let mut next_auto_sprite_id = 0;
    for (entry_index, entry) in file.entries.iter().enumerate() {
        let entry_pos = w.pos()?;
        if let Some(last_entry_pos) = last_entry_pos {
            w.seek_to(last_entry_pos + format.offset_to_next_offset())?;
            w.write_u32((entry_pos - last_entry_pos) as _)?;
            w.seek_to(entry_pos)?;
        }

        emitter.chain_with(|f| write!(f, "in entry {} (for '{}')", entry_index, entry.path), |emitter| {
            write_entry(w, emitter, &format, entry, &mut next_auto_sprite_id)
        })?;

        last_entry_pos = Some(entry_pos);
    }
    Ok(())
}

fn write_entry(
    w: &mut BinWriter,
    emitter: &impl Emitter,
    file_format: &FileFormat,
    entry: &Entry,
    // automatic numbering state that needs to persist from one entry to the next
    next_auto_sprite_id: &mut u32,
) -> Result<(), ErrorReported> {
    let instr_format = &*file_format.instr_format;

    let entry_pos = w.pos()?;

    let EntrySpecs {
        rt_width, rt_height, rt_format,
        colorkey, offset_x, offset_y, memory_priority,
        low_res_scale,
    } = entry.specs;

    file_format.write_header(w, &EntryHeaderData {
        rt_width, rt_height, rt_format, colorkey,
        offset_x, offset_y,
        memory_priority,
        low_res_scale: low_res_scale as u32,
        has_data: entry.texture_data.is_some() as u32,
        version: file_format.version as u32,
        num_sprites: entry.sprites.len() as u32,
        num_scripts: entry.scripts.len() as u32,
        // we will overwrite these later
        name_offset: 0, secondary_name_offset: None,
        next_offset: 0, thtx_offset: None,
    })?;

    let sprite_offsets_pos = w.pos()?;
    w.write_u32s(&vec![0; entry.sprites.len()])?;
    let script_headers_pos = w.pos()?;
    w.write_u32s(&vec![0; 2 * entry.scripts.len()])?;

    let path_offset = w.pos()? - entry_pos;
    w.write_cstring(&Encoded::encode(&entry.path, DEFAULT_ENCODING).map_err(|e| emitter.emit(e))?, 16)?;

    let mut path_2_offset = 0;
    if let Some(path_2) = &entry.path_2 {
        path_2_offset = w.pos()? - entry_pos;
        w.write_cstring(&Encoded::encode(path_2, DEFAULT_ENCODING).map_err(|e| emitter.emit(e))?, 16)?;
    };

    let sprite_offsets = entry.sprites.iter().map(|(_, sprite)| {
        let sprite_offset = w.pos()? - entry_pos;

        let sprite_id = sprite.id.unwrap_or(*next_auto_sprite_id);
        *next_auto_sprite_id = sprite_id + 1;

        write_sprite(w, sprite_id, sprite)?;
        Ok(sprite_offset)
    }).collect::<WriteResult<Vec<_>>>()?;

    let script_ids_and_offsets = entry.scripts.iter().map(|(name, script)| {
        let script_offset = w.pos()? - entry_pos;
        emitter.chain_with(|f| write!(f, "in script {} (id {})", name, script.id), |emitter| {
            llir::write_instrs(w, emitter, instr_format, &script.instrs)
        })?;

        Ok((script.id, script_offset))
    }).collect::<WriteResult<Vec<_>>>()?;

    let mut texture_offset = 0;
    if let Some(texture_data) = &entry.texture_data {
        let texture_metadata = entry.texture_metadata.as_ref().expect("always Some if texture_data is");
        texture_offset = w.pos()? - entry_pos;
        write_texture(w, texture_data, texture_metadata)?;
    };

    let end_pos = w.pos()?;

    if let Some(texture_metadata) = &entry.texture_metadata {
        for (noun, img_dim, rt_dim) in vec![
            ("width", texture_metadata.width, rt_width),
            ("height", texture_metadata.height, rt_height),
        ] {
            if img_dim > rt_dim {
                emitter.emit(warning!(
                    message("runtime {} of {} too small for image {} of {}", noun, rt_dim, noun, img_dim),
                    // no img dimension span because it might not have one
                )).ignore();
            }
        }
    }

    w.seek_to(entry_pos + file_format.offset_to_thtx_offset())?;
    w.write_u32(texture_offset as _)?;

    w.seek_to(entry_pos + file_format.offset_to_path_offset())?;
    w.write_u32(path_offset as _)?;

    if let Some(offset_to_path_2_offset) = file_format.offset_to_path_2_offset() {
        w.seek_to(entry_pos + offset_to_path_2_offset)?;
        w.write_u32(path_2_offset as _)?;
    }

    w.seek_to(sprite_offsets_pos)?;
    for sprite_offset in sprite_offsets {
        w.write_u32(sprite_offset as _)?;
    }

    w.seek_to(script_headers_pos)?;
    for (script_id, script_offset) in script_ids_and_offsets {
        w.write_u32(script_id as _)?;
        w.write_u32(script_offset as _)?;
    }

    w.seek_to(end_pos)?;
    Ok(())
}

fn read_sprite(f: &mut BinReader) -> ReadResult<Sprite> {
    Ok(Sprite {
        id: Some(f.read_u32()?),
        offset: f.read_f32s_2()?,
        size: f.read_f32s_2()?,
    })
}

fn write_sprite(
    f: &mut BinWriter,
    sprite_id: u32,  // we ignore sprite.id because that can be None
    sprite: &Sprite,
) -> WriteResult {
    f.write_u32(sprite_id)?;
    f.write_f32s(&sprite.offset)?;
    f.write_f32s(&sprite.size)
}

#[inline(never)]
fn read_texture(f: &mut BinReader, emitter: &impl Emitter, with_images: bool) -> ReadResult<(TextureMetadata, Option<TextureData>)> {
    f.expect_magic(emitter, "THTX")?;

    let zero = f.read_u16()?;
    let format = f.read_u16()? as u32;
    let width = f.read_u16()? as u32;
    let height = f.read_u16()? as u32;
    let size = f.read_u32()?;
    if zero != 0 {
        emitter.emit(warning!("nonzero thtx_zero lost: {}", zero)).ignore();
    }
    let thtx = TextureMetadata { format, width, height };

    if let Some(cformat) = ColorFormat::from_format_num(format) {
        let expected_size = cformat.bytes_per_pixel() as usize * width as usize * height as usize;
        if expected_size != size as usize {
            emitter.emit(warning!("strange image data size: {} bytes, expected {}", size, expected_size)).ignore();
        }
    }

    if with_images {
        let mut data = vec![0; size as usize];
        f.read_exact(&mut data)?;
        Ok((thtx, Some(data.into())))
    } else {
        Ok((thtx, None))
    }
}

#[inline(never)]
fn write_texture(f: &mut BinWriter, data: &TextureData, metadata: &TextureMetadata) -> WriteResult {
    f.write_all(b"THTX")?;

    f.write_u16(0)?;
    f.write_u16(metadata.format as _)?;
    f.write_u16(metadata.width as _)?;
    f.write_u16(metadata.height as _)?;

    f.write_u32(data.data.len() as _)?;
    f.write_all(&data.data)?;
    Ok(())
}

/// Type responsible for dealing with version differences in the container format.
struct FileFormat {
    version: Version,
    instr_format: Box<dyn InstrFormat>,
}

struct InstrFormat06;
struct InstrFormat07;

impl FileFormat {
    fn from_game(game: Game) -> Self {
        let version = Version::from_game(game);
        let instr_format = get_instr_format(version);
        FileFormat { version, instr_format }
    }

    fn read_header(&self, f: &mut BinReader, emitter: &dyn Emitter) -> ReadResult<EntryHeaderData> {
        let emitter = emitter.as_sized();

        macro_rules! warn_if_nonzero {
            ($name:literal, $expr:expr) => {
                match $expr {
                    0 => {},
                    x => emitter.emit(warning!("nonzero {} will be lost (value: {})", $name, x)).ignore(),
                }
            };
        }

        if self.version.is_old_header() {
            // old format
            let num_sprites = f.read_u32()? as _;
            let num_scripts = f.read_u32()? as _;
            warn_if_nonzero!("rt_textureslot", f.read_u32()?);
            let width = f.read_u32()? as _;
            let height = f.read_u32()? as _;
            let format = f.read_u32()? as _;
            let colorkey = f.read_u32()? as _;
            let name_offset = f.read_u32()? as _;
            warn_if_nonzero!("unused_1", f.read_u32()?);
            let secondary_name_offset = NonZeroU64::new(f.read_u32()? as _);
            let version = f.read_u32()? as _;
            let memory_priority = f.read_u32()? as _;
            let thtx_offset = NonZeroU64::new(f.read_u32()? as _) as _;
            let has_data = f.read_u16()? as _;
            warn_if_nonzero!("unused_2", f.read_u16()?);
            let next_offset = f.read_u32()? as _;
            warn_if_nonzero!("unused_3", f.read_u32()?);

            Ok(EntryHeaderData {
                version, num_sprites, num_scripts,
                rt_width: width,
                rt_height: height,
                rt_format: format, name_offset,
                next_offset, secondary_name_offset, colorkey,
                memory_priority, thtx_offset, has_data,
                offset_x: 0, offset_y: 0, low_res_scale: 0,
            })

        } else {
            // new format
            let version = f.read_u32()? as _;
            let num_sprites = f.read_u16()? as _;
            let num_scripts = f.read_u16()? as _;
            warn_if_nonzero!("rt_textureslot", f.read_u16()?);
            let width = f.read_u16()? as _;
            let height = f.read_u16()? as _;
            let format = f.read_u16()? as _;
            let name_offset = f.read_u32()? as _;
            let offset_x = f.read_u16()? as _;
            let offset_y = f.read_u16()? as _;
            let memory_priority = f.read_u32()? as _;
            let thtx_offset = NonZeroU64::new(f.read_u32()? as _);
            let has_data = f.read_u16()? as _;
            let low_res_scale = f.read_u16()? as _;
            let next_offset = f.read_u32()? as _;

            for _ in 0..6 {  // header gets padded to 16 dwords
            warn_if_nonzero!("header padding", f.read_u32()?);
            }
            Ok(EntryHeaderData {
                version, num_sprites, num_scripts,
                rt_width: width,
                rt_height: height,
                rt_format: format, name_offset,
                offset_x, offset_y, low_res_scale, next_offset,
                memory_priority, thtx_offset, has_data,
                secondary_name_offset: None,
                colorkey: 0,
            })
        }
    }

    fn write_header(&self, f: &mut BinWriter, header: &EntryHeaderData) -> WriteResult {
        if self.version.is_old_header() {
            // old format
            f.write_u32(header.num_sprites as _)?;
            f.write_u32(header.num_scripts as _)?;
            f.write_u32(0)?;
            f.write_u32(header.rt_width as _)?;
            f.write_u32(header.rt_height as _)?;
            f.write_u32(header.rt_format as _)?;
            f.write_u32(header.colorkey as _)?;
            f.write_u32(header.name_offset as _)?;
            f.write_u32(0)?;
            f.write_u32(header.secondary_name_offset.map(NonZeroU64::get).unwrap_or(0) as _)?;
            f.write_u32(header.version)?;
            f.write_u32(header.memory_priority)?;
            f.write_u32(header.thtx_offset.map(NonZeroU64::get).unwrap_or(0) as _)?;
            f.write_u16(header.has_data as _)?;
            f.write_u16(0)?;
            f.write_u32(header.next_offset as _)?;
            f.write_u32(0)?;

        } else {
            // new format
            f.write_u32(header.version as _)?;
            f.write_u16(header.num_sprites as _)?;
            f.write_u16(header.num_scripts as _)?;
            f.write_u16(0)?;
            f.write_u16(header.rt_width as _)?;
            f.write_u16(header.rt_height as _)?;
            f.write_u16(header.rt_format as _)?;
            f.write_u32(header.name_offset as _)?;
            f.write_u16(header.offset_x as _)?;
            f.write_u16(header.offset_y as _)?;
            f.write_u32(header.memory_priority as _)?;
            f.write_u32(header.thtx_offset.map(NonZeroU64::get).unwrap_or(0) as _)?;
            f.write_u16(header.has_data as _)?;
            f.write_u16(header.low_res_scale as _)?;
            f.write_u32(header.next_offset as _)?;
            f.write_u32s(&[0; 6])?;
        }
        Ok(())
    }

    /// Offset into entry of the `next_offset` field.
    fn offset_to_next_offset(&self) -> u64 {
        if self.version.is_old_header() { 0x38 } else { 0x24 }
    }

    /// Offset into entry of the `name_offset` field.
    fn offset_to_path_offset(&self) -> u64 {
        if self.version.is_old_header() { 0x1c } else { 0x10 }
    }

    /// Offset into entry of the `name_offset` field.
    fn offset_to_path_2_offset(&self) -> Option<u64> {
        if self.version.is_old_header() { Some(0x24) } else { None }
    }

    /// Offset into entry of the `thtx_offset` field.
    fn offset_to_thtx_offset(&self) -> u64 {
        if self.version.is_old_header() { 0x30 } else { 0x1c }
    }
}

pub(super) fn get_instr_format(version: Version) -> Box<dyn InstrFormat> {
    match version {
        Version::V0 => Box::new(InstrFormat06),
        _ => Box::new(InstrFormat07),
    }
}

impl InstrFormat for InstrFormat06 {
    fn instr_header_size(&self) -> usize { 4 }

    fn read_instr(&self, f: &mut BinReader, _: &dyn Emitter) -> ReadResult<ReadInstr> {
        let time = match f.read_i16_or_eof() {
            Ok(Some(time)) => time as i32,
            Ok(None) => return Ok(ReadInstr::EndOfFile),
            Err(e) => return Err(e),
        };

        let opcode = f.read_i8()?;
        let argsize = f.read_u8()? as usize;
        let args_blob = f.read_byte_vec(argsize)?;
        let instr = RawInstr { time, opcode: opcode as u16, param_mask: 0, args_blob, ..RawInstr::DEFAULTS };

        if (time, opcode, argsize) == (0, 0, 0) {
            Ok(ReadInstr::MaybeTerminal(instr))
        } else {
            Ok(ReadInstr::Instr(instr))
        }
    }

    fn write_instr(&self, f: &mut BinWriter, _: &dyn Emitter, instr: &RawInstr) -> WriteResult {
        f.write_i16(instr.time as _)?;
        f.write_u8(instr.opcode as _)?;
        f.write_u8(instr.args_blob.len() as _)?;
        f.write_all(&instr.args_blob)?;
        Ok(())
    }

    fn write_terminal_instr(&self, f: &mut BinWriter, _: &dyn Emitter) -> WriteResult {
        f.write_u32(0)
    }
}

impl InstrFormat for InstrFormat07 {
    fn instr_header_size(&self) -> usize { 8 }

    fn read_instr(&self, f: &mut BinReader, emitter: &dyn Emitter) -> ReadResult<ReadInstr> {
        let opcode = f.read_i16()?;
        let size = f.read_u16()? as usize;
        if opcode == -1 {
            return Ok(ReadInstr::Terminal);
        }

        let time = f.read_i16()? as _;
        let param_mask = f.read_u16()?;
        let args_size = size.checked_sub(self.instr_header_size()).ok_or_else(|| {
            emitter.as_sized().emit(error!("bad instruction size ({} < {})", size, self.instr_header_size()))
        })?;
        let args_blob = f.read_byte_vec(args_size)?;
        // eprintln!("opcode: {:04x}  size: {:04x}  time: {:04x}  param_mask: {:04x}  args: {:?}", opcode, size, time, param_mask, args);
        Ok(ReadInstr::Instr(RawInstr { time, opcode: opcode as _, param_mask, args_blob, ..RawInstr::DEFAULTS }))
    }

    fn write_instr(&self, f: &mut BinWriter, _: &dyn Emitter, instr: &RawInstr) -> WriteResult {
        f.write_u16(instr.opcode)?;
        f.write_u16(self.instr_size(instr) as _)?;
        f.write_i16(instr.time as _)?;
        f.write_u16(instr.param_mask as _)?;
        f.write_all(&instr.args_blob)?;
        Ok(())
    }

    fn write_terminal_instr(&self, f: &mut BinWriter, _: &dyn Emitter) -> WriteResult {
        f.write_i16(-1)?;
        f.write_u16(0)?;
        f.write_u16(0)?;
        f.write_u16(0)
    }
}
