use std::fmt;
use bstr::{BStr, BString, ByteSlice};
use indexmap::IndexMap;

use crate::error::{CompileError};
use crate::pos::{Sp};
use crate::ast;
use crate::ident::Ident;
use crate::type_system::{TypeSystem};
use crate::meta::{self, ToMeta, FromMeta, Meta, FromMetaError};
use crate::game::Game;
use crate::instr::{self, Instr, InstrFormat, IntrinsicInstrKind};
use crate::binary_io::{BinRead, BinWrite, ReadResult, WriteResult, bail};

// =============================================================================

#[derive(Debug, Clone)]
pub struct Entry {
    pub specs: EntrySpecs,
    pub texture: Texture,
    pub path: BString,
    pub eosd_name_2: Option<BString>, // idfk
    pub scripts: IndexMap<Sp<Ident>, Script>,
    pub sprites: IndexMap<Sp<Ident>, Sprite>,
}

#[derive(Debug, Clone)]
pub struct Script {
    pub id: i32,
    pub instrs: Vec<Instr>,
}

#[derive(Debug, Clone)]
pub struct EntrySpecs {
    pub width: u32,
    pub height: u32,
    pub format: u32,
    pub colorkey: u32, // Only in old format
    pub offset_x: u32,
    pub offset_y: u32,
    pub memory_priority: u32,
    pub has_data: bool,
    pub low_res_scale: bool,
}

impl Entry {
    fn make_meta(&self) -> meta::Fields {
        let EntrySpecs {
            width, height, format, colorkey, offset_x, offset_y,
            memory_priority, has_data, low_res_scale,
        } = &self.specs;

        Meta::make_object()
            .field("format", format)
            .field("width", width)
            .field("height", height)
            .field("colorkey", colorkey)
            .field("offset_x", offset_x)
            .field("offset_y", offset_y)
            .field("memory_priority", memory_priority)
            .field("low_res_scale", low_res_scale)
            .field("has_data", has_data)
            .field("path", &self.path)
            .field("thtx_format", &self.texture.thtx.format)
            .field("thtx_width", &self.texture.thtx.width)
            .field("thtx_height", &self.texture.thtx.height)
            .with_mut(|b| if let Some(s) = &self.eosd_name_2 {
                b.field("eosd_name_2", s);
            })
            .field("sprites", &self.sprites)
            .build_fields()
    }
}

#[derive(Clone)]
pub struct Texture {
    pub thtx: ThtxHeader,
    pub data: Vec<u8>,
}

#[derive(Debug, Clone)]
pub struct ThtxHeader {
    pub format: u32,
    pub width: u32,
    pub height: u32,
}

impl fmt::Debug for Texture {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Texture")
            .field("thtx", &self.thtx)
            .field("data", &(..))
            .finish()
    }
}

#[derive(Debug, Clone)]
pub struct Sprite {
    pub id: u32,
    pub offset: [f32; 2],
    pub size: [f32; 2],
}

impl ToMeta for Sprite {
    fn to_meta(&self) -> Meta {
        let &Sprite { id, offset, size } = self;
        Meta::make_object()
            .field("id", &id)
            .field("x", &offset[0])
            .field("y", &offset[1])
            .field("w", &size[0])
            .field("h", &size[1])
            .build()
    }
}

// =============================================================================

pub fn decompile(game: Game, entries: &[Entry], ty_ctx: &TypeSystem) -> ast::Script {
    let format = game_format(game);
    let instr_format = format.instr_format();

    let mut items = vec![];
    for entry in entries {
        items.push(Sp::null(ast::Item::Meta {
            keyword: Sp::null(ast::MetaKeyword::Entry),
            name: None,
            fields: Sp::null(entry.make_meta()),
        }));

        for (name, &Script { id, ref instrs }) in &entry.scripts {
            let code = instr::raise_instrs_to_sub_ast(ty_ctx, instr_format, instrs);

            items.push(Sp::null(ast::Item::AnmScript {
                number: Some(Sp::null(id)),
                name: name.clone(),
                code: ast::Block(code),
            }));
        }
    }

    use crate::passes::{unused_labels, decompile_loop};

    let mut out = ast::Script { items, mapfiles: ty_ctx.mapfiles_to_ast() };
    crate::ast::walk_mut_script(&mut decompile_loop::Visitor::new(), &mut out);
    crate::ast::walk_mut_script(&mut unused_labels::Visitor::new(), &mut out);
    out
}

// =============================================================================

#[derive(Debug, Clone)]
struct EntryHeaderData {
    version: u32,
    num_sprites: u32,
    num_scripts: u32,
    width: u32,
    height: u32,
    format: u32,
    name_offset: usize,
    secondary_name_offset: Option<usize>, // EoSD only?
    colorkey: u32, // Only in old format
    offset_x: u32,
    offset_y: u32,
    memory_priority: u32,
    thtx_offset: usize,
    has_data: u32,
    low_res_scale: u32,
    next_offset: u32,
}

pub fn read_anm(game: Game, mut entry_bytes: &[u8]) -> ReadResult<Vec<Entry>> {
    let format = game_format(game);
    let instr_format = format.instr_format();

    let mut out = vec![];
    let mut next_script_index = 0;
    let mut next_sprite_index = 0;
    loop {
        let mut f = entry_bytes;

        // 64 byte header regardless of version
        let header_data = format.read_header(&mut f)?;
        eprintln!("{:?}", header_data);
        if header_data.has_data != header_data.has_data % 2 {
            fast_warning!("non-boolean value found for 'has_data': {}", header_data.has_data);
        }
        if header_data.low_res_scale != header_data.low_res_scale % 2 {
            fast_warning!("non-boolean value found for 'low_res_scale': {}", header_data.low_res_scale);
        }

        let sprite_offsets = (0..header_data.num_sprites).map(|_| f.read_u32()).collect::<ReadResult<Vec<_>>>()?;
        let script_ids_and_offsets = (0..header_data.num_scripts).map(|_| {
            Ok((f.read_i32()?, f.read_u32()? as usize))
        }).collect::<ReadResult<Vec<_>>>()?;
        eprintln!("{:?}", sprite_offsets);
        eprintln!("{:?}", script_ids_and_offsets);

        let path = (&entry_bytes[header_data.name_offset..]).read_cstring(16)?;
        let eosd_name_2 = {
            header_data.secondary_name_offset
                .map(|x| (&entry_bytes[x..]).read_cstring(16)).transpose()?
        };

        let sprites = sprite_offsets.iter().map(|&offset| {
            let key = Sp::null(auto_sprite_name(next_sprite_index as u32));
            let value = read_sprite(&mut &entry_bytes[offset as usize..])?;
            next_sprite_index += 1;
            Ok((key, value))
        }).collect::<ReadResult<IndexMap<_, _>>>()?;

        let scripts = script_ids_and_offsets.iter().map(|&(id, offset)| {
            let key = Sp::null(auto_script_name(next_script_index));

            let mut f = &entry_bytes[offset..];
            let mut instrs = vec![];
            while let Some(instr) = instr_format.read_instr(&mut f)? {
                instrs.push(instr);
            }
            next_script_index += 1;
            Ok((key, Script { id, instrs }))
        }).collect::<ReadResult<IndexMap<_, _>>>()?;

        let texture = read_texture(&mut &entry_bytes[header_data.thtx_offset..])?;
        let specs = EntrySpecs {
            width: header_data.width, height: header_data.height,
            format: header_data.format, colorkey: header_data.colorkey,
            offset_x: header_data.offset_x, offset_y: header_data.offset_y,
            memory_priority: header_data.memory_priority,
            has_data: header_data.has_data != 0,
            low_res_scale: header_data.low_res_scale != 0,
        };

        out.push(Entry { texture, specs, path, eosd_name_2, sprites, scripts });

        if header_data.next_offset == 0 {
            break;
        }
        entry_bytes = &entry_bytes[header_data.next_offset as usize..];
    }
    Ok(out)
}

fn auto_sprite_name(i: u32) -> Ident {
    format!("sprite{}", i).parse::<Ident>().unwrap()
}
fn auto_script_name(i: u32) -> Ident {
    format!("script{}", i).parse::<Ident>().unwrap()
}

pub fn read_sprite(f: &mut dyn BinRead) -> ReadResult<Sprite> {
    Ok(Sprite {
        id: f.read_u32()?,
        offset: [f.read_f32()?, f.read_f32()?],
        size: [f.read_f32()?, f.read_f32()?],
    })
}

pub fn read_texture(f: &mut dyn BinRead) -> ReadResult<Texture> {
    f.expect_magic("THTX")?;

    let zero = f.read_u16()?;
    let format = f.read_u16()? as u32;
    let width = f.read_u16()? as u32;
    let height = f.read_u16()? as u32;
    let size = f.read_u32()?;
    if zero != 0 {
        fast_warning!("nonzero thtx_zero lost: {}", zero);
    }
    let thtx = ThtxHeader { format, width, height };

    let mut data = vec![0; size as usize];
    f.read_exact(&mut data)?;

    Ok(Texture { thtx, data })
}

// =============================================================================

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Version { V0, V2, V3, V4, V7, V8 }
impl Version {
    fn from_game(game: Game) -> Self {
        use Game::*;
        match game {
            Th06 => Version::V0,
            Th07 => Version::V2,
            Th08 | Th09 => Version::V3,
            Th095 | Th10 | Alcostg => Version::V4,
            Th11 | Th12 | Th125 | Th128 => Version::V7,
            Th13 | Th14 | Th143 | Th15 | Th16 | Th165 | Th17 => Version::V8,
        }
    }

    fn is_new_header(self) -> bool { self >= Version::V7 }
    fn has_vars(self) -> bool { self >= Version::V2 }
}

fn game_format(game: Game) -> FileFormat {
    FileFormat { version: Version::from_game(game) }
}

struct FileFormat { version: Version }
struct InstrFormat06;
struct InstrFormat07;

impl InstrFormat06 { const HEADER_SIZE: usize = 4; }
impl InstrFormat07 { const HEADER_SIZE: usize = 8; }

impl FileFormat {
    fn read_header(&self, f: &mut dyn BinRead) -> ReadResult<EntryHeaderData> {
        if self.version.is_new_header() {
            // new format
            let version = f.read_u32()?;
            let num_sprites = f.read_u16()? as u32;
            let num_scripts = f.read_u16()? as u32;
            let rt_textureslot = f.read_u16()? as u32;
            let width = f.read_u16()? as u32;
            let height = f.read_u16()? as u32;
            let format = f.read_u16()? as u32;
            let name_offset = f.read_u32()? as usize;
            let offset_x = f.read_u16()? as u32;
            let offset_y = f.read_u16()? as u32;
            let memory_priority = f.read_u32()?;
            let thtx_offset = f.read_u32()? as usize;
            let has_data = f.read_u16()? as u32;
            let low_res_scale = f.read_u16()? as u32;
            let next_offset = f.read_u32()?;

            for _ in 0..6 {  // header gets padded to 16 dwords
                if f.read_u32()? != 0 {
                    fast_warning!("nonzero data in header padding will be lost")
                }
            }
            if rt_textureslot != 0 {
                fast_warning!("nonzero rt_textureslot will be lost (value: {})", rt_textureslot);
            }
            Ok(EntryHeaderData {
                version, num_sprites, num_scripts,
                width, height, format, name_offset,
                offset_x, offset_y, low_res_scale, next_offset,
                memory_priority, thtx_offset, has_data,
                secondary_name_offset: None,
                colorkey: 0,
            })
        } else {
            // old format
            let num_sprites = f.read_u32()?;
            let num_scripts = f.read_u32()?;
            let rt_textureslot = f.read_u32()?;
            let width = f.read_u32()?;
            let height = f.read_u32()?;
            let format = f.read_u32()?;
            let colorkey = f.read_u32()?;
            let name_offset = f.read_u32()? as usize;
            let unused_1 = f.read_u32()?;
            let secondary_name_offset = Some(f.read_u32()? as usize);
            let version = f.read_u32()?;
            let memory_priority = f.read_u32()?;
            let thtx_offset = f.read_u32()? as usize;
            let has_data = f.read_u16()? as u32;
            let unused_2 = f.read_u16()? as u32;
            let next_offset = f.read_u32()?;
            let unused_3 = f.read_u32()?;

            if rt_textureslot != 0 { fast_warning!("nonzero rt_textureslot will be lost (value: {})", rt_textureslot); }
            if unused_1 != 0 { fast_warning!("nonzero unused_1 will be lost (value: {})", unused_1); }
            if unused_2 != 0 { fast_warning!("nonzero unused_2 will be lost (value: {})", unused_2); }
            if unused_3 != 0 { fast_warning!("nonzero unused_3 will be lost (value: {})", unused_3); }
            Ok(EntryHeaderData {
                version, num_sprites, num_scripts,
                width, height, format, name_offset,
                next_offset, secondary_name_offset, colorkey,
                memory_priority, thtx_offset, has_data,
                offset_x: 0, offset_y: 0, low_res_scale: 0,

            })
        }
    }

    fn instr_format(&self) -> &dyn InstrFormat {
        if self.version.has_vars() {
            &InstrFormat07
        } else {
            &InstrFormat06
        }
    }
}

impl InstrFormat for InstrFormat06 {
    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, u16)> {
        vec![]
    }

    fn read_instr(&self, f: &mut dyn BinRead) -> ReadResult<Option<Instr>> {
        let time = f.read_i16()? as i32;
        let opcode = f.read_i8()?;
        let size = f.read_u8()? as usize;
        if opcode == -1 {
            return Ok(None);
        }

        let args = instr::read_dword_args_upto_size(f, size - Self::HEADER_SIZE, 0)?;
        Ok(Some(Instr { time, opcode: opcode as u16, args }))
    }

    fn write_instr(&self, f: &mut dyn BinWrite, instr: &Instr) -> WriteResult<()> {
        f.write_u16(instr.opcode)?;
        f.write_u16(self.instr_size(instr) as u16)?;
        f.write_i16(instr.time as i16)?;
        f.write_u16(0) // FIXME: param_mask
    }

    fn write_terminal_instr(&self, f: &mut dyn BinWrite) -> WriteResult<()> {
        f.write_i32(-1)?;
        f.write_i32(-1)
    }

    fn instr_size(&self, instr: &Instr) -> usize { Self::HEADER_SIZE + 4 * instr.args.len() }

    fn encode_label(&self, offset: usize) -> u32 { offset as _ }
    fn decode_label(&self, bits: u32) -> usize { bits as _ }
}

impl InstrFormat for InstrFormat07 {
    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, u16)> {
        vec![]
    }

    fn read_instr(&self, f: &mut dyn BinRead) -> ReadResult<Option<Instr>> {
        let opcode = f.read_i16()?;
        let size = f.read_u16()? as usize;
        if opcode == -1 {
            return Ok(None);
        }

        let time = f.read_i16()? as i32;
        let param_mask = f.read_u16()?;
        let args = instr::read_dword_args_upto_size(f, size - Self::HEADER_SIZE, param_mask)?;
        Ok(Some(Instr { time, opcode: opcode as u16, args }))
    }

    fn write_instr(&self, f: &mut dyn BinWrite, instr: &Instr) -> WriteResult<()> {
        f.write_u16(instr.opcode)?;
        f.write_u16(self.instr_size(instr) as u16)?;
        f.write_i16(instr.time as i16)?;
        f.write_u16(instr.param_mask())
    }

    fn write_terminal_instr(&self, f: &mut dyn BinWrite) -> WriteResult<()> {
        f.write_i32(-1)?;
        f.write_i32(-1)
    }

    fn instr_size(&self, instr: &Instr) -> usize { Self::HEADER_SIZE + 4 * instr.args.len() }

    fn encode_label(&self, offset: usize) -> u32 { offset as _ }
    fn decode_label(&self, bits: u32) -> usize { bits as _ }
}
