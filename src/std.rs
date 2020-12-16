use std::io::{self, Read, Cursor, Write, Seek};
use byteorder::{LittleEndian as Le, ReadBytesExt, WriteBytesExt};
use bstr::{BStr, BString, ByteSlice};

#[derive(Debug, Clone, PartialEq)]
pub struct StdFile {
    pub unknown: u32,
    pub entries: Vec<Entry>,
    pub instances: Vec<Instance>,
    pub script: Vec<Instr>,
    pub extra: StdExtra,
}

#[derive(Debug, Clone, PartialEq)]
pub enum StdExtra {
    Th06 {
        bgm_names: [BString; 5],
        bgm_paths: [BString; 5],
    },
    Th10 {
        anm_name: BString,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Entry {
    pub id: u16,
    pub unknown: u16,
    pub pos: [f32; 3],
    pub size: [f32; 3],
    pub quads: Vec<Quad>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Quad {
    pub unknown: u16,
    pub script_index: u16,
    pub pos: [f32; 3],
    pub size: [f32; 2],
}

#[derive(Debug, Clone, PartialEq)]
pub struct Instance {
    pub object_id: u16,
    pub unknown: u16,
    pub pos: [f32; 3],
}

#[derive(Debug, Clone, PartialEq)]
pub struct Instr {
    pub time: i32,
    pub opcode: u16,
    pub args: Vec<u32>,
}

// FIXME clean up API, return Result
pub fn read_std_10(bytes: &[u8]) -> StdFile {
    let mut f = Cursor::new(bytes);

    let num_entries = f.read_u16::<Le>().expect("incomplete header") as usize;
    let num_quads = f.read_u16::<Le>().expect("incomplete header") as usize;
    let instances_offset = f.read_u32::<Le>().expect("incomplete header") as usize;
    let script_offset = f.read_u32::<Le>().expect("incomplete header") as usize;
    let unknown = f.read_u32::<Le>().expect("incomplete header");
    let extra = read_extra(&mut f).expect("incomplete header");
    let entry_offsets = (0..num_entries).map(|_| f.read_u32::<Le>().expect("unexpected EOF")).collect::<Vec<_>>();
    let entries = (0..num_entries)
        .map(|i| read_entry(&bytes[entry_offsets[i] as usize..]))
        .collect::<Vec<_>>();
    assert_eq!(num_quads, entries.iter().map(|x| x.quads.len()).sum());
    let instances = {
        let mut f = Cursor::new(&bytes[instances_offset..]);
        let mut vec = vec![];
        while let Some(instance) = read_instance(&mut f) {
            vec.push(instance);
        }
        vec
    };
    let script = {
        let mut f = Cursor::new(&bytes[script_offset..]);
        let mut script = vec![];
        while let Some(instr) = read_instr(&mut f) {
            script.push(instr);
        }
        script
    };
    StdFile { unknown, extra, entries, instances, script }
}

pub fn write_std_10(f: &mut (impl Write + Seek), std: &StdFile) -> io::Result<()> {
    let start_pos = f.seek(io::SeekFrom::Current(0))?;

    f.write_u16::<Le>(std.entries.len() as u16)?;
    f.write_u16::<Le>(std.entries.iter().map(|x| x.quads.len()).sum::<usize>() as u16)?;

    let instances_offset_pos = f.seek(io::SeekFrom::Current(0))?;
    f.write_u32::<Le>(0)?;
    let script_offset_pos = f.seek(io::SeekFrom::Current(0))?;
    f.write_u32::<Le>(0)?;

    f.write_u32::<Le>(std.unknown)?;

    write_extra(f, &std.extra)?;

    let entry_offsets_pos = f.seek(io::SeekFrom::Current(0))?;
    for _ in &std.entries {
        f.write_u32::<Le>(0)?;
    }

    let mut entry_offsets = vec![];
    for entry in &std.entries {
        entry_offsets.push(f.seek(io::SeekFrom::Current(0))? - start_pos);
        write_entry(f, entry)?;
    }

    let instances_offset = f.seek(io::SeekFrom::Current(0))? - start_pos;
    for instance in &std.instances {
        write_instance(f, instance)?;
    }
    write_terminal_instance(f)?;

    let script_offset = f.seek(io::SeekFrom::Current(0))? - start_pos;
    for instr in &std.script {
        write_instr(f, instr)?;
    }
    write_terminal_instr(f)?;

    let end_pos = f.seek(io::SeekFrom::Current(0))?;
    f.seek(io::SeekFrom::Start(instances_offset_pos))?;
    f.write_u32::<Le>(instances_offset as u32)?;
    f.seek(io::SeekFrom::Start(script_offset_pos))?;
    f.write_u32::<Le>(script_offset as u32)?;
    f.seek(io::SeekFrom::Start(entry_offsets_pos))?;
    for offset in entry_offsets {
        f.write_u32::<Le>(offset as u32)?;
    }
    f.seek(io::SeekFrom::Start(end_pos))?;
    Ok(())
}

fn read_extra(f: &mut Cursor<&[u8]>) -> Option<StdExtra> {
    Some(StdExtra::Th10 { anm_name: read_string_128(f) })
}
fn write_extra(f: &mut impl Write, x: &StdExtra) -> io::Result<()> {
    match x {
        StdExtra::Th10 { anm_name } => write_string_128(f, anm_name.as_bstr())?,
        StdExtra::Th06 { .. } => unimplemented!(),
    };
    Ok(())
}

fn read_string_128(f: &mut Cursor<&[u8]>) -> BString {
    let mut out = [0u8; 128];
    f.read_exact(&mut out).expect("unexpected EOF");
    let mut out = out.as_bstr().to_owned();
    while let Some(0) = out.last() {
        out.pop();
    }
    out
}
fn write_string_128(f: &mut impl Write, s: &BStr) -> io::Result<()> {
    let mut buf = [0u8; 128];
    assert!(s.len() < 127, "string too long: {:?}", s);
    buf[..s.len()].copy_from_slice(&s[..]);
    f.write_all(&mut buf)
}
fn read_vec2(f: &mut Cursor<&[u8]>) -> Option<[f32; 2]> {
    Some([f.read_f32::<Le>().ok()?, f.read_f32::<Le>().ok()?])
}
fn read_vec3(f: &mut Cursor<&[u8]>) -> Option<[f32; 3]> {Some([
    f.read_f32::<Le>().ok()?,
    f.read_f32::<Le>().ok()?,
    f.read_f32::<Le>().ok()?,
])}

fn write_vec2(f: &mut impl Write, x: &[f32; 2]) -> io::Result<()> {
    f.write_f32::<Le>(x[0])?;
    f.write_f32::<Le>(x[1])?;
    Ok(())
}
fn write_vec3(f: &mut impl Write, x: &[f32; 3]) -> io::Result<()> {
    f.write_f32::<Le>(x[0])?;
    f.write_f32::<Le>(x[1])?;
    f.write_f32::<Le>(x[2])?;
    Ok(())
}


fn read_entry(bytes: &[u8]) -> Entry {
    let mut f = Cursor::new(bytes);
    let id = f.read_u16::<Le>().expect("unexpected EOF");
    let unknown = f.read_u16::<Le>().expect("unexpected EOF");
    let pos = read_vec3(&mut f).expect("unexpected EOF");
    let size = read_vec3(&mut f).expect("unexpected EOF");
    let mut quads = vec![];
    while let Some(quad) = read_quad(&mut f) {
        quads.push(quad);
    }
    Entry { id, unknown, pos, size, quads }
}

fn write_entry(f: &mut impl Write, x: &Entry) -> io::Result<()> {
    f.write_u16::<Le>(x.id)?;
    f.write_u16::<Le>(x.unknown)?;
    write_vec3(f, &x.pos)?;
    write_vec3(f, &x.size)?;
    for quad in &x.quads {
        write_quad(f, quad)?;
    }
    write_terminal_quad(f)
}

fn read_quad(f: &mut Cursor<&[u8]>) -> Option<Quad> {
    let unknown = f.read_u16::<Le>().expect("unexpected EOF");
    match f.read_u16::<Le>().expect("unexpected EOF") {
        0x1c => {},
        0x4 => { // End of stream
            assert_eq!(unknown, 0xffff);
            return None;
        },
        s => panic!("bad object size: {}", s),
    };

    let script_index = f.read_u16::<Le>().expect("unexpected EOF");
    match f.read_u16::<Le>().expect("unexpected EOF") {
        0 => {},
        s => panic!("unexpected nonzero padding: {}", s),
    };

    let pos = read_vec3(f).expect("unexpected EOF");
    let size = read_vec2(f).expect("unexpected EOF");
    Some(Quad { unknown, script_index, pos, size })
}

fn write_quad(f: &mut impl Write, quad: &Quad) -> io::Result<()> {
    f.write_u16::<Le>(quad.unknown)?;
    f.write_u16::<Le>(0x1c)?; // size
    f.write_u16::<Le>(quad.script_index)?;
    f.write_u16::<Le>(0)?;
    write_vec3(f, &quad.pos)?;
    write_vec2(f, &quad.size)?;
    Ok(())
}
fn write_terminal_quad(f: &mut impl Write) -> io::Result<()> {
    f.write_i16::<Le>(-1)?;
    f.write_u16::<Le>(0x4)?; // size
    Ok(())
}


fn read_instance(f: &mut Cursor<&[u8]>) -> Option<Instance> {
    let object_id = f.read_u16::<Le>().expect("unexpected EOF");
    let unknown = f.read_u16::<Le>().expect("unexpected EOF");
    if object_id == 0xffff {
        return None;
    }
    let pos = read_vec3(f).expect("unexpected EOF");
    Some(Instance { object_id, unknown, pos })
}

fn write_instance(f: &mut impl Write, inst: &Instance) -> io::Result<()> {
    f.write_u16::<Le>(inst.object_id)?;
    f.write_u16::<Le>(inst.unknown)?;
    write_vec3(f, &inst.pos)?;
    Ok(())
}
fn write_terminal_instance(f: &mut impl Write) -> io::Result<()> {
    for _ in 0..4 {
        f.write_i32::<Le>(-1)?;
    }
    Ok(())
}

fn read_instr(f: &mut Cursor<&[u8]>) -> Option<Instr> {
    let time = f.read_i32::<Le>().expect("unexpected EOF");
    let opcode = f.read_i16::<Le>().expect("unexpected EOF");
    let size = f.read_u16::<Le>().expect("unexpected EOF");
    if opcode == -1 {
        return None
    }

    assert_eq!(size % 4, 0);
    let nargs = (size - 8)/4;
    let args = (0..nargs).map(|_| f.read_u32::<Le>().expect("unexpected EOF")).collect::<Vec<_>>();
    Some(Instr { time, opcode: opcode as u16, args })
}
fn write_instr(f: &mut impl Write, instr: &Instr) -> io::Result<()> {
    f.write_i32::<Le>(instr.time)?;
    f.write_u16::<Le>(instr.opcode)?;
    f.write_u16::<Le>(8 + 4 * instr.args.len() as u16)?;
    for &x in &instr.args {
        f.write_u32::<Le>(x)?;
    }
    Ok(())
}
fn write_terminal_instr(f: &mut impl Write) -> io::Result<()> {
    for _ in 0..5 {
        f.write_i32::<Le>(-1)?;
    }
    Ok(())
}
