use std::convert::TryInto;

use crate::ast;
use crate::io::{BinRead, BinWrite, BinReader, BinWriter, Encoded, ReadResult, WriteResult, DEFAULT_ENCODING};
use crate::diagnostic::{Emitter};
use crate::error::{GatherErrorIteratorExt, ErrorReported};
use crate::game::Game;
use crate::llir::AcceleratingByteMask;
use crate::meta::{self, FromMetaError, Meta};
use crate::pos::{Sp};
use crate::context::CompilerContext;

// =============================================================================

#[derive(Debug, Clone)]
pub enum MissionMsgFile {
    Th095(MissionMsg095),
}

#[derive(Debug, Clone)]
pub struct MissionMsg095 {
    pub entries: Vec<Entry095>,
    binary_filename: Option<String>,
}

#[derive(Debug, Clone)]
pub struct Entry095 {
    pub stage: u16,
    pub scene: u16,
    pub face: u32,
    pub point: u32,
    pub text: [Sp<String>; 3],
}

impl MissionMsgFile {
    pub fn decompile_to_ast(&self, _: Game, _: &mut CompilerContext) -> Result<ast::ScriptFile, ErrorReported> {
        match self {
            MissionMsgFile::Th095(msg) => decompile(msg),
        }
    }

    pub fn compile_from_ast(game: Game, ast: &ast::ScriptFile, ctx: &mut CompilerContext) -> Result<Self, ErrorReported> {
        match game {
            Game::Th095 => compile(ast, ctx).map(MissionMsgFile::Th095),
            _ => Err(ctx.emitter.emit(error!("--mission does not exist for game {}", game))),
        }
    }

    pub fn write_to_stream(&self, w: &mut BinWriter, _: Game) -> WriteResult {
        let emitter = w.emitter();
        match self {
            MissionMsgFile::Th095(msg) => write_095(w, &emitter, msg),
        }
    }

    pub fn read_from_stream(r: &mut BinReader, game: Game) -> ReadResult<Self> {
        let emitter = r.emitter();
        match game {
            Game::Th095 => read_095(r, &emitter).map(MissionMsgFile::Th095),
            _ => Err(emitter.emit(error!("--mission does not exist for game {}", game))),
        }
    }
}

impl Entry095 {
    fn make_meta(&self) -> meta::Fields {
        Meta::make_object()
            .field("stage", &(self.stage as i32))
            .field("scene", &(self.scene as i32))
            .field("face", &self.face)
            .field("point", &self.point)
            .field("text", &self.text.iter().map(|x| &x.value).collect::<Vec<_>>())
            .build_fields()
    }

    fn from_fields(fields: &Sp<meta::Fields>) -> Result<Self, FromMetaError<'_>> {
        meta::ParseObject::scope(fields, |m| {
            let stage = m.expect_field::<u32>("stage")? as u16;
            let scene = m.expect_field::<u32>("scene")? as u16;
            let face = m.expect_field("face")?;
            let point = m.expect_field("point")?;
            let text = m.expect_field("text")?;
            Ok(Entry095 { stage, scene, face, point, text })
        })
    }
}

// =============================================================================

fn decompile(
    msg: &MissionMsg095,
) -> Result<ast::ScriptFile, ErrorReported> {
    Ok(ast::ScriptFile {
        items: msg.entries.iter().map(|entry| {
            sp!(ast::Item::Meta {
                keyword: sp!(ast::MetaKeyword::Entry),
                fields: sp!(entry.make_meta()),
            })
        }).collect(),
        mapfiles: vec![],
        image_sources: vec![],
    })
}

// =============================================================================

fn compile(
    ast: &ast::ScriptFile,
    ctx: &mut CompilerContext,
) -> Result<MissionMsg095, ErrorReported> {
    let ast = {
        let mut ast = ast.clone();

        // reduced set of passes because only compile-time stuff is possible
        crate::passes::resolve_names::assign_res_ids(&mut ast, ctx)?;
        crate::passes::resolve_names::run(&ast, ctx)?;
        crate::passes::type_check::run(&ast, ctx)?;
        crate::passes::evaluate_const_vars::run(ctx)?;
        crate::passes::const_simplify::run(&mut ast, ctx)?;
        ast
    };

    let mut entries = vec![];
    ast.items.iter().map(|item| {
        match &item.value {
            ast::Item::Meta { keyword: sp_pat!(ast::MetaKeyword::Entry), fields, .. } => {
                entries.push(Entry095::from_fields(fields).map_err(|e| ctx.emitter.emit(e))?);
            },
            ast::Item::ConstVar { .. } => {},
            _ => return Err(ctx.emitter.emit(error!(
                message("feature not supported by format"),
                primary(item, "not supported by ANM files"),
            ))),
        }
        Ok(())
    }).collect_with_recovery()?;

    Ok(MissionMsg095 { entries, binary_filename: None })
}

// =============================================================================

fn read_095(
    reader: &mut BinReader,
    emitter: &impl Emitter,
) -> ReadResult<MissionMsg095> {
    let num_entries = reader.read_u32()?;
    for expected_offset in entry_offsets_095(num_entries as usize) {
        let read_offset = reader.read_u32()? as u64;
        if read_offset != expected_offset {
            emitter.emit(warning!(
                "strange offset in offset table ({:#x} instead of {:#x})",
                read_offset, expected_offset,
            )).ignore();
        }
    }

    let entries = (0..num_entries).map(|i| {
        emitter.chain_with(|f| write!(f, "while reading entry {}", i), |emitter| {
            read_entry_095(reader, emitter)
        })
    }).collect::<Result<_, _>>()?;

    let binary_filename = Some(reader.display_filename().to_string());
    Ok(MissionMsg095 { entries, binary_filename })
}

fn read_entry_095(
    reader: &mut BinReader,
    emitter: &impl Emitter,
) -> Result<Entry095, ErrorReported> {
    let stage = reader.read_u16()?;
    let scene = reader.read_u16()?;
    let face = reader.read_u32()?;
    let point = reader.read_u32()?;

    let text = (0..3).map(|line| {
        emitter.chain_with(|f| write!(f, "in line {}", line), |emitter| {
            let mut bytes = reader.read_byte_vec(64)?;

            let cipher = ZunMissionCipher { stage: stage as u8, scene: scene as u8, line: line as u8, player: 0};
            for (byte, c) in bytes.iter_mut().zip(cipher.bytes()) {
                *byte = u8::wrapping_add(*byte, c)
            }

            let mut encoded = Encoded(bytes);
            encoded.trim_first_nul(emitter);
            encoded.decode(DEFAULT_ENCODING).map_err(|e| emitter.emit(e)).map(|s| sp!(s))
        })
    }).collect::<Result<Vec<_>, _>>()?.try_into().unwrap();

    Ok(Entry095 { stage, scene, face, point, text })
}

struct ZunMissionCipher { stage: u8, scene: u8, player: u8, line: u8 }
impl ZunMissionCipher {
    pub fn bytes(&self) -> impl Iterator<Item=u8> {
        use std::num::Wrapping as W;

        let W(mask) = W(7) * W(self.stage) + W(11) * W(self.scene) + W(13) * W(self.player) + W(58);
        let W(vel) = W(23) * (W(self.line) + W(1));
        let accel = 1;
        AcceleratingByteMask { mask, vel, accel }
    }
}

fn write_095(
    w: &mut BinWriter,
    emitter: &impl Emitter,
    file: &MissionMsg095,
) -> WriteResult {
    w.write_u32(file.entries.len() as u32)?;
    for offset in entry_offsets_095(file.entries.len()) {
        w.write_u32(offset as u32)?;
    }

    for entry in &file.entries {
        write_entry_095(w, emitter, entry)?;
    }
    Ok(())
}

fn write_entry_095(
    w: &mut BinWriter,
    emitter: &impl Emitter,
    entry: &Entry095,
) -> Result<(), ErrorReported> {
    let &Entry095 { stage, scene, face, point, ref text } = entry;
    w.write_u16(stage)?;
    w.write_u16(scene)?;
    w.write_u32(face)?;
    w.write_u32(point)?;

    const SIZE: usize = 64;

    for (line, s) in text.iter().enumerate() {
        // FIXME: std copypasta
        let mut encoded = Encoded::encode(&s, DEFAULT_ENCODING).map_err(|e| emitter.emit(e))?;
        if encoded.len() >= SIZE {
            return Err(emitter.emit(error!(
                message("string too long for mission.msg"),
                primary(s, "{} bytes (max allowed: {})", encoded.len(), SIZE - 1),
            )));
        }

        encoded.0.resize(SIZE, 0);

        let cipher = ZunMissionCipher { stage: stage as u8, scene: scene as u8, line: line as u8, player: 0};
        for (byte, c) in encoded.0.iter_mut().zip(cipher.bytes()) {
            *byte = u8::wrapping_sub(*byte, c)
        }
        w.write_all(&encoded.0)?;
    }
    Ok(())
}

fn entry_offsets_095(num_entries: usize) -> impl Iterator<Item=u64> {
    let entry_size = 2 + 2 + 4 + 4 + 64 * 3;
    let entry_table_size = 4 + 4 * (num_entries as u64);
    (0..num_entries).map(move |entry| entry_table_size + entry_size * entry as u64)
}
