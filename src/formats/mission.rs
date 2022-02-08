use crate::ast;
use crate::ast::meta::{self, FromMetaError, Meta};
use crate::io::{BinRead, BinWrite, BinReader, BinWriter, Encoded, ReadResult, WriteResult, DEFAULT_ENCODING};
use crate::diagnostic::{Emitter};
use crate::error::{GatherErrorIteratorExt, ErrorReported};
use crate::game::Game;
use crate::llir::AcceleratingByteMask;
use crate::pos::{Sp};
use crate::context::CompilerContext;

// =============================================================================

#[derive(Debug, Clone)]
pub enum MissionMsgFile {
    Th095(MissionMsg<Entry095>),
    Th125(MissionMsg<Entry125>),
}

#[derive(Debug, Clone)]
pub struct MissionMsg<E: Entry> {
    pub entries: Vec<E>,
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

#[derive(Debug, Clone)]
pub struct Entry125 {
    pub stage: u16,
    pub scene: u16,
    pub player: u16,
    pub unknown_1: u8,
    pub unknown_2: u8,
    pub point_1: u32,
    pub point_2: u32,
    pub furigana: [[u32; 2]; 3],
    pub text: [Sp<String>; 6],
}

impl MissionMsgFile {
    pub fn decompile_to_ast(&self, _: Game, ctx: &mut CompilerContext) -> Result<ast::ScriptFile, ErrorReported> {
        match self {
            MissionMsgFile::Th095(msg) => {
                let emitter = ctx.emitter.while_decompiling(msg.binary_filename.as_deref());
                decompile(msg, &emitter)
            },
            MissionMsgFile::Th125(msg) => {
                let emitter = ctx.emitter.while_decompiling(msg.binary_filename.as_deref());
                decompile(msg, &emitter)
            },
        }
    }

    pub fn compile_from_ast(game: Game, ast: &ast::ScriptFile, ctx: &mut CompilerContext) -> Result<Self, ErrorReported> {
        match game {
            Game::Th095 => compile(ast, ctx).map(MissionMsgFile::Th095),
            Game::Th125 => compile(ast, ctx).map(MissionMsgFile::Th125),
            _ => Err(ctx.emitter.emit(error!("--mission does not exist for game {}", game))),
        }
    }

    pub fn write_to_stream(&self, w: &mut BinWriter, _: Game) -> WriteResult {
        let emitter = w.emitter();
        match self {
            MissionMsgFile::Th095(msg) => write_mission_msg(w, &emitter, msg),
            MissionMsgFile::Th125(msg) => write_mission_msg(w, &emitter, msg),
        }
    }

    pub fn read_from_stream(r: &mut BinReader, game: Game) -> ReadResult<Self> {
        let emitter = r.emitter();
        match game {
            Game::Th095 => read_mission_msg(r, &emitter).map(MissionMsgFile::Th095),
            Game::Th125 => read_mission_msg(r, &emitter).map(MissionMsgFile::Th125),
            _ => Err(emitter.emit(error!("--mission does not exist for game {}", game))),
        }
    }
}

pub trait Entry: Sized {
    fn size() -> usize;
    fn write(&self, w: &mut BinWriter, emitter: &impl Emitter) -> Result<(), ErrorReported>;
    fn make_meta(&self) -> meta::Fields;
    fn from_fields(fields: &Sp<meta::Fields>) -> Result<Self, FromMetaError<'_>>;
    fn read(reader: &mut BinReader, emitter: &impl Emitter) -> Result<Self, ErrorReported>;
}

impl Entry for Entry095 {
    fn size() -> usize { 2 + 2 + 4 + 4 + 64 * 3 }

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

    fn read(
        reader: &mut BinReader,
        emitter: &impl Emitter,
    ) -> Result<Entry095, ErrorReported> {
        let stage = reader.read_u16()?;
        let scene = reader.read_u16()?;
        let face = reader.read_u32()?;
        let point = reader.read_u32()?;

        let cipher = ZunMissionCipher { stage: stage as u8, scene: scene as u8, player: 0};
        let text = read_mission_text_lines(reader, emitter, cipher)?;

        Ok(Entry095 { stage, scene, face, point, text })
    }

    fn write(
        &self,
        writer: &mut BinWriter,
        emitter: &impl Emitter,
    ) -> Result<(), ErrorReported> {
        let &Entry095 { stage, scene, face, point, ref text } = self;
        writer.write_u16(stage)?;
        writer.write_u16(scene)?;
        writer.write_u32(face)?;
        writer.write_u32(point)?;

        let cipher = ZunMissionCipher { stage: stage as u8, scene: scene as u8, player: 0};
        write_mission_text_lines(writer, emitter, cipher, text)
    }
}

impl Entry for Entry125 {
    fn size() -> usize { 40 + 64 * 6 }

    fn make_meta(&self) -> meta::Fields {
        Meta::make_object()
            .field("stage", &(self.stage as i32))
            .field("scene", &(self.scene as i32))
            .field("player", &(self.player as i32))
            .field("unknown_1", &(self.unknown_1 as i32))
            .field("unknown_2", &(self.unknown_2 as i32))
            .field("point_1", &self.point_1)
            .field("point_2", &self.point_2)
            .field("furigana", &self.furigana)
            .field("text", &self.text.iter().map(|x| &x.value).collect::<Vec<_>>())
            .build_fields()
    }

    fn from_fields(fields: &Sp<meta::Fields>) -> Result<Self, FromMetaError<'_>> {
        meta::ParseObject::scope(fields, |m| {
            let stage = m.expect_field::<u32>("stage")? as u16;
            let scene = m.expect_field::<u32>("scene")? as u16;
            let player = m.expect_field::<u32>("player")? as u16;
            let unknown_1 = m.expect_field::<u32>("unknown_1")? as u8;
            let unknown_2 = m.expect_field::<u32>("unknown_2")? as u8;
            let point_1 = m.expect_field("point_1")?;
            let point_2 = m.expect_field("point_2")?;
            let furigana = m.expect_field("furigana")?;
            let text = m.expect_field("text")?;
            Ok(Entry125 { stage, scene, player, unknown_1, unknown_2, point_1, point_2, furigana, text })
        })
    }

    fn read(
        reader: &mut BinReader,
        emitter: &impl Emitter,
    ) -> Result<Entry125, ErrorReported> {
        let stage = reader.read_u16()?;
        let scene = reader.read_u16()?;
        let player = reader.read_u16()?;
        let unknown_1 = reader.read_u8()?;
        let unknown_2 = reader.read_u8()?;
        let point_1 = reader.read_u32()?;
        let point_2 = reader.read_u32()?;
        let furigana = [
            [reader.read_u32()?, reader.read_u32()?],
            [reader.read_u32()?, reader.read_u32()?],
            [reader.read_u32()?, reader.read_u32()?],
        ];
        let cipher = ZunMissionCipher { stage: stage as u8, scene: scene as u8, player: player as u8};
        let text = read_mission_text_lines(reader, emitter, cipher)?;

        Ok(Entry125 { stage, scene, player, unknown_1, unknown_2, point_1, point_2, furigana, text })
    }

    fn write(
        &self,
        writer: &mut BinWriter,
        emitter: &impl Emitter,
    ) -> Result<(), ErrorReported> {
        let &Entry125 { stage, scene, player, unknown_1, unknown_2, point_1, point_2, ref furigana, ref text } = self;
        writer.write_u16(stage)?;
        writer.write_u16(scene)?;
        writer.write_u16(player)?;
        writer.write_u8(unknown_1)?;
        writer.write_u8(unknown_2)?;
        writer.write_u32(point_1)?;
        writer.write_u32(point_2)?;
        for array in furigana {
            for &x in array {
                writer.write_u32(x)?;
            }
        }

        let cipher = ZunMissionCipher { stage: stage as u8, scene: scene as u8, player: player as u8};
        write_mission_text_lines(writer, emitter, cipher, text)
    }
}

// =============================================================================

fn decompile<E: Entry>(
    msg: &MissionMsg<E>,
    _: &impl Emitter,
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

fn compile<E: Entry>(
    ast: &ast::ScriptFile,
    ctx: &mut CompilerContext,
) -> Result<MissionMsg<E>, ErrorReported> {
    let ast = {
        let mut ast = ast.clone();

        // reduced set of passes because only compile-time stuff is possible
        crate::passes::resolution::resolve_names(&ast, ctx)?;
        crate::passes::type_check::run(&ast, ctx)?;
        crate::passes::evaluate_const_vars::run(ctx)?;
        crate::passes::const_simplify::run(&mut ast, ctx)?;
        ast
    };

    let mut entries = vec![];
    ast.items.iter().map(|item| {
        match &item.value {
            ast::Item::Meta { keyword: sp_pat!(ast::MetaKeyword::Entry), fields, .. } => {
                entries.push(E::from_fields(fields).map_err(|e| ctx.emitter.emit(e))?);
            },
            ast::Item::ConstVar { .. } => {},
            _ => return Err(ctx.emitter.emit(error!(
                message("feature not supported by format"),
                primary(item, "not supported by mission.msg"),
            ))),
        }
        Ok(())
    }).collect_with_recovery()?;

    Ok(MissionMsg { entries, binary_filename: None })
}

// =============================================================================

struct ZunMissionCipher { stage: u8, scene: u8, player: u8 }
impl ZunMissionCipher {
    pub fn bytes_for_line(&self, line: usize) -> impl Iterator<Item=u8> {
        use std::num::Wrapping as W;

        let W(mask) = W(7) * W(self.stage) + W(11) * W(self.scene) + W(13) * W(self.player) + W(58);
        let W(vel) = W(23) * W(line as u8 + 1);
        let accel = 1;
        AcceleratingByteMask { mask, vel, accel }
    }
}

fn read_mission_msg<E: Entry>(
    reader: &mut BinReader,
    emitter: &impl Emitter,
) -> ReadResult<MissionMsg<E>> {
    let num_entries = reader.read_u32()?;
    for expected_offset in entry_offsets::<E>(num_entries as usize) {
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
            E::read(reader, emitter)
        })
    }).collect::<Result<_, _>>()?;

    let binary_filename = Some(reader.display_filename().to_string());
    Ok(MissionMsg { entries, binary_filename })
}

fn read_mission_text_lines<const N: usize>(
    reader: &mut BinReader,
    emitter: &impl Emitter,
    cipher: ZunMissionCipher,
) -> ReadResult<[Sp<String>; N]>{
    let text = (0..N).map(|line| {
        emitter.chain_with(|f| write!(f, "in line {}", line), |emitter| {
            let mut bytes = reader.read_byte_vec(64)?;
            for (byte, c) in bytes.iter_mut().zip(cipher.bytes_for_line(line)) {
                *byte = u8::wrapping_add(*byte, c)
            }

            let mut encoded = Encoded(bytes);
            encoded.trim_first_nul(emitter, true);
            encoded.decode(DEFAULT_ENCODING).map_err(|e| emitter.emit(e)).map(|s| sp!(s))
        })
    }).collect::<Result<Vec<_>, _>>()?.try_into().unwrap();
    Ok(text)
}

fn write_mission_msg<E: Entry>(
    writer: &mut BinWriter,
    emitter: &impl Emitter,
    file: &MissionMsg<E>,
) -> WriteResult {
    writer.write_u32(file.entries.len() as u32)?;
    for offset in entry_offsets::<E>(file.entries.len()) {
        writer.write_u32(offset as u32)?;
    }

    for entry in &file.entries {
        E::write(entry, writer, emitter)?;
    }
    Ok(())
}

fn write_mission_text_lines(
    writer: &mut BinWriter,
    emitter: &impl Emitter,
    cipher: ZunMissionCipher,
    text: &[Sp<String>],
) -> Result<(), ErrorReported> {
    for (line, s) in text.iter().enumerate() {
        let mut encoded = Encoded::encode_fixed_size(&s, DEFAULT_ENCODING, 64).map_err(|e| emitter.emit(e))?;

        for (byte, c) in encoded.0.iter_mut().zip(cipher.bytes_for_line(line)) {
            *byte = u8::wrapping_sub(*byte, c)
        }
        writer.write_all(&encoded.0)?;
    }
    Ok(())
}

fn entry_offsets<E: Entry>(num_entries: usize) -> impl Iterator<Item=u64> {
    let entry_table_size = 4 + 4 * (num_entries as u64);
    (0..num_entries).map(move |entry| entry_table_size + (E::size() * entry) as u64)
}
