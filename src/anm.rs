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
    id: i32,
    instrs: Vec<Instr>,
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

impl ToMeta for Entry {
    fn to_meta(&self) -> Meta {
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
            .build()
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
    pub offset: [u32; 2],
    pub size: [u32; 2],
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

// fn _decompile_std(format: &dyn FileFormat, std: &StdFile, ty_ctx: &TypeSystem) -> ast::Script {
//     let instr_format = format.instr_format();
//     let script = &std.script;
//
//     let code = instr::raise_instrs_to_sub_ast(ty_ctx, instr_format, script);
//
//     let code = {
//         use crate::passes::{unused_labels, decompile_loop};
//         use crate::ast::VisitMut;
//
//         let mut code = ast::Block(code);
//         decompile_loop::Visitor::new().visit_func_body(&mut code);
//         unused_labels::Visitor::new().visit_func_body(&mut code);
//         code
//     };
//
//     ast::Script {
//         items: vec! [
//             Sp::null(ast::Item::Meta {
//                 keyword: Sp::null(ast::MetaKeyword::Meta),
//                 name: None,
//                 fields: Sp::null(std.make_meta(format)),
//             }),
//             Sp::null(ast::Item::AnmScript {
//                 number: None,
//                 name: Sp::null("main".parse().unwrap()),
//                 code,
//             }),
//         ],
//     }
// }

// =============================================================================

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

pub fn read_anm(game: Game, full_bytes: &[u8]) -> ReadResult<Vec<Entry>> {
    let format = game_format(game);
    let instr_format = format.instr_format();

    let mut entry_bytes = full_bytes;

    let mut out = vec![];
    loop {
        let mut f = entry_bytes;

        // 64 byte header regardless of version
        let header_data = format.read_header(&mut f)?;
        if header_data.has_data != header_data.has_data % 2 {
            fast_warning!("non-boolean value found for 'has_data': {}", header_data.has_data);
        }
        if header_data.low_res_scale != header_data.low_res_scale % 2 {
            fast_warning!("non-boolean value found for 'low_res_scale': {}", header_data.low_res_scale);
        }

        let sprite_offsets = (0..header_data.num_sprites).map(|_| f.read_u32()).collect::<ReadResult<Vec<_>>>()?;
        let script_offsets = (0..header_data.num_scripts).map(|_| f.read_u32()).collect::<ReadResult<Vec<_>>>()?;

        let path = (&full_bytes[header_data.name_offset..]).read_cstring(16)?;
        let eosd_name_2 = {
            header_data.secondary_name_offset
                .map(|x| (&full_bytes[x..]).read_cstring(16)).transpose()?
        };

        let sprites = sprite_offsets.iter().enumerate().map(|(i, &offset)| {
            let key = Sp::null(auto_sprite_name(i as u32));
            let value = read_sprite(&mut &full_bytes[offset as usize..])?;
            Ok((key, value))
        }).collect::<ReadResult<IndexMap<_, _>>>()?;

        let scripts = script_offsets.iter().enumerate().map(|(i, &offset)| {
            let key = Sp::null(auto_script_name(i as u32));
            // the script offset points to a weird tiny little struct with an id and another offset.
            let mut f = &full_bytes[offset as usize..];
            let id = f.read_i32()?;
            let instr_offset = f.read_u32()? as usize;

            let mut f = &full_bytes[instr_offset..];
            let mut instrs = vec![];
            while let Some(instr) = instr_format.read_instr(&mut f)? {
                instrs.push(instr);
            }
            Ok((key, Script { id, instrs }))
        }).collect::<ReadResult<IndexMap<_, _>>>()?;

        let texture = read_texture(&mut &full_bytes[header_data.thtx_offset..])?;
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
        offset: [f.read_u32()?, f.read_u32()?],
        size: [f.read_u32()?, f.read_u32()?],
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

fn game_format(_game: Game) -> Box<dyn FileFormat> {
    Box::new(FileFormat11)
}

trait FileFormat {
    fn read_header(&self, f: &mut dyn BinRead) -> ReadResult<EntryHeaderData>;
    fn instr_format(&self) -> &dyn InstrFormat;
}

struct FileFormat11;
struct InstrFormat11;
impl FileFormat for FileFormat11 {
    fn read_header(&self, f: &mut dyn BinRead) -> ReadResult<EntryHeaderData> {
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
                fast_warning!("nonzero data in header padding!")
            }
        }
        Ok(EntryHeaderData {
            version, num_sprites, num_scripts,
            width, height, format, name_offset,
            offset_x, offset_y, low_res_scale, next_offset,
            memory_priority, thtx_offset, has_data,
            secondary_name_offset: None,
            colorkey: 0,
        })
    }

    fn instr_format(&self) -> &dyn InstrFormat { &InstrFormat11 }
}
impl InstrFormat for InstrFormat11 {
    fn instr_size(&self, instr: &Instr) -> usize { 8 + 4 * instr.args.len() }

    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, u16)> {
        vec![]
    }

    fn read_instr(&self, f: &mut dyn BinRead) -> ReadResult<Option<Instr>> {
        let opcode = f.read_i16()?;
        let size = f.read_u16()?;
        if opcode == -1 {
            return Ok(None);
        }

        let time = f.read_i16()? as i32;
        let param_mask = f.read_u16()?;

        assert_eq!(size % 4, 0);
        let nargs = (size - 8)/4;
        let args = (0..nargs).map(|_| {
            Ok(instr::InstrArg::Raw(f.read_u32()?.into()))
        }).collect::<ReadResult<Vec<_>>>()?;
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

    fn encode_label(&self, offset: usize) -> u32 { offset as _ }
    fn decode_label(&self, bits: u32) -> usize { bits as _ }
}
