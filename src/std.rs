use std::io::{self, Read, Cursor, Write, Seek};
use std::collections::{HashMap};

use byteorder::{LittleEndian as Le, ReadBytesExt, WriteBytesExt};
use bstr::{BStr, BString, ByteSlice};
use crate::error::{Diagnostic, Label};

use crate::CompileError;
use crate::pos::{Spanned};
use crate::ast::{self, Expr};
use crate::ident::Ident;
use crate::signature::Functions;
use crate::meta::{ToMeta, FromMeta, Meta, FromMetaError};

// =============================================================================

/// Game-independent representation of a STD file.
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
        anm_path: BString,
    },
}

impl StdFile {
    pub fn decompile(&self, functions: &Functions) -> ast::Script {
        _decompile_std(&InstrFormat10, self, functions)
    }

    pub fn compile(script: &ast::Script, functions: &Functions) -> Result<Self, CompileError> {
        _compile_std(&InstrFormat10, script, functions)
    }
}

impl FromMeta for StdFile {
    fn from_meta(meta: &Meta) -> Result<Self, FromMetaError<'_>> {
        Ok(StdFile {
            unknown: meta.expect_field("unknown")?,
            entries: meta.expect_field("objects")?,
            instances: meta.expect_field("instances")?,
            script: vec![],
            extra: StdExtra::Th10 {
                anm_path: meta.expect_field("anm_file")?,
            },
        })
    }
}

impl ToMeta for StdFile {
    fn to_meta(&self) -> Meta {
        let anm_path = match &self.extra {
            StdExtra::Th10 { anm_path } => anm_path,
            StdExtra::Th06 { .. } => unimplemented!(),
        };
        Meta::make_object()
            .field("unknown", &self.unknown)
            .field("anm_file", &anm_path)
            .field("objects", &self.entries)
            .field("instances", &self.instances)
            .build()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Entry {
    pub id: u16,
    pub unknown: u16,
    pub pos: [f32; 3],
    pub size: [f32; 3],
    pub quads: Vec<Quad>,
}

impl FromMeta for Entry {
    fn from_meta(meta: &Meta) -> Result<Self, FromMetaError<'_>> {
        Ok(Entry {
            id: meta.expect_field::<i32>("id")? as u16,
            unknown: meta.expect_field::<i32>("unknown")? as u16,
            pos: meta.expect_field("pos")?,
            size: meta.expect_field("size")?,
            quads: meta.expect_field("quads")?,
        })
    }
}

impl ToMeta for Entry {
    fn to_meta(&self) -> Meta {
        Meta::make_object()
            .field("id", &(self.id as i32))
            .field("unknown", &(self.unknown as i32))
            .field("pos", &self.pos)
            .field("size", &self.size)
            .field("quads", &self.quads)
            .build()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Quad {
    pub unknown: u16,
    pub anm_script: u16,
    pub pos: [f32; 3],
    pub size: [f32; 2],
}

impl FromMeta for Quad {
    fn from_meta(meta: &Meta) -> Result<Self, FromMetaError<'_>> {
        Ok(Quad {
            unknown: meta.get_field::<i32>("unknown")?.unwrap_or(0) as u16,
            anm_script: meta.expect_field::<i32>("anm_script")? as u16,
            pos: meta.expect_field("pos")?,
            size: meta.expect_field("size")?,
        })
    }
}

impl ToMeta for Quad {
    fn to_meta(&self) -> Meta {
        Meta::make_object()
            .field_default("unknown", &(self.unknown as i32), &0)
            .field("anm_script", &(self.anm_script as i32))
            .field("pos", &self.pos)
            .field("size", &self.size)
            .build()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Instance {
    pub object_id: u16,
    pub unknown: u16,
    pub pos: [f32; 3],
}

impl FromMeta for Instance {
    fn from_meta(meta: &Meta) -> Result<Self, FromMetaError<'_>> {
        Ok(Instance {
            object_id: meta.expect_field::<i32>("object")? as u16,
            unknown: meta.get_field::<i32>("unknown")?.unwrap_or(256) as u16,
            pos: meta.expect_field("pos")?,
        })
    }
}

impl ToMeta for Instance {
    fn to_meta(&self) -> Meta {
        Meta::make_object()
            .field("object", &(self.object_id as i32))
            .field_default("unknown", &(self.unknown as i32), &256)
            .field("pos", &self.pos)
            .build()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum InstrOrLabel {
    Label(Spanned<Ident>),
    Instr(Instr),
}
#[derive(Debug, Clone, PartialEq)]
pub struct Instr {
    pub time: i32,
    pub opcode: u16,
    pub args: Vec<InstrArg>,
}
#[derive(Debug, Clone, PartialEq)]
pub enum InstrArg {
    DwordBits(u32),
    /// A label that has not yet been converted to an integer argument.
    ///
    /// This may be present in the input to [`InstrFormat::instr_size`], but will be replaced with
    /// a dword before [`InstrFormat::write_instr`] is called.
    Label(Spanned<Ident>),
    /// A `timeof(label)` that has not yet been converted to an integer argument.
    ///
    /// This may be present in the input to [`InstrFormat::instr_size`], but will be replaced with
    /// a dword before [`InstrFormat::write_instr`] is called.
    TimeOf(Spanned<Ident>),
}

impl InstrArg {
    /// Call this at a time when the arg is known to have a fully resolved value.
    ///
    /// Such times are:
    /// * During decompilation.
    /// * Within [`InstrFormat::write_instr`].
    fn expect_dword(&self) -> u32 {
        match *self {
            InstrArg::DwordBits(x) => x,
            _ => panic!("unexpected unresolved argument (bug!): {:?}", self),
        }
    }
}

// =============================================================================

fn _decompile_std(format: &dyn InstrFormat, std: &StdFile, functions: &Functions) -> ast::Script {
    use crate::signature::ArgEncoding;

    let opcode_intrinsics: HashMap<_, _> = {
        format.intrinsic_opcode_pairs().into_iter()
            .map(|(a, b)| (b, a)).collect()
    };

    let default_label = |offset: usize| {
        Spanned::null_from(format!("label_{}", offset).parse::<Ident>().unwrap())
    };

    let mut offset = 0;
    let code = std.script.iter().map(|instr| {
        // For now we give every instruction a label and strip the unused ones later.
        let this_instr_label = Spanned::null_from(ast::StmtLabel::Label(default_label(offset)));
        offset += format.instr_size(instr);

        let Instr { time, opcode, args } = instr;

        match opcode_intrinsics.get(&opcode) {
            Some(IntrinsicInstrKind::Jmp) => {
                assert_eq!(args.len(), 2); // FIXME: print proper error
                let dest_offset = format.decode_label(args[0].expect_dword());
                let dest_time = args[1].expect_dword() as i32;
                return Spanned::null_from(ast::Stmt {
                    time: *time,
                    labels: vec![this_instr_label],
                    body: Spanned::null_from(ast::StmtBody::Jump(ast::StmtGoto {
                        destination: default_label(dest_offset),
                        time: Some(dest_time),
                    })),
                })
            },
            None => {}, // continue
        }

        let ins_ident = {
            functions.opcode_names.get(&(*opcode as u32)).cloned()
                .unwrap_or_else(|| Ident::new_ins(*opcode as u32))
        };

        let encodings = match functions.ins_signature(&ins_ident) {
            Some(siggy) => siggy.arg_encodings(),
            None => vec![ArgEncoding::Dword; args.len()],
        };

        assert_eq!(encodings.len(), args.len()); // FIXME: return Error
        let args = encodings.iter().zip(args).map(|(enc, arg)| {
            let bits = arg.expect_dword();
            match enc {
                ArgEncoding::Dword => <Spanned<Expr>>::null_from(bits as i32),
                ArgEncoding::Color => Spanned::null_from(Expr::LitInt {
                    value: bits as i32,
                    hex: true,
                }),
                ArgEncoding::Float => <Spanned<Expr>>::null_from(f32::from_bits(bits)),
            }
        }).collect();

        Spanned::null_from(ast::Stmt {
            time: *time,
            labels: vec![this_instr_label],
            body: Spanned::from(ast::StmtBody::Expr(Spanned::from(Expr::Call { func: ins_ident, args }))),
        })
    }).collect();

    ast::Script {
        items: vec! [
            Spanned::from(ast::Item::Meta {
                keyword: ast::MetaKeyword::Meta,
                name: None,
                meta: std.to_meta(),
            }),
            Spanned::from(ast::Item::AnmScript {
                number: None,
                name: "main".parse().unwrap(),
                code: ast::Block(code),
            }),
        ],
    }
}

fn _compile_std(
    format: &dyn InstrFormat,
    script: &ast::Script,
    functions: &Functions,
) -> Result<StdFile, CompileError> {
    use ast::Item;

    let mut script = script.clone();

    let mut visitor = crate::passes::const_simplify::Visitor::new();
    crate::ast::walk_mut_script(&mut visitor, &mut script);
    visitor.finish()?;

    let (meta, main_sub) = {
        let (mut found_meta, mut found_main_sub) = (None, None);
        for item in script.items.iter() {
            match &item.value {
                Item::Meta { keyword: ast::MetaKeyword::Meta, name: None, meta } => {
                    if let Some(_) = found_meta.replace(meta) {
                        bail_nospan!("multiple 'meta's");
                    }
                    found_meta = Some(meta);
                },
                Item::Meta { keyword: ast::MetaKeyword::Meta, name: Some(name), .. } => bail_nospan!("unexpected named meta '{}' in STD file", name),
                Item::Meta { keyword, .. } => bail_nospan!("unexpected '{}' in STD file", keyword),
                Item::AnmScript { number: Some(_), .. } => bail_nospan!("unexpected numbered script in STD file"),
                Item::AnmScript { number: None, name, code } => {
                    if name != "main" {
                        bail_nospan!("STD entry point must be called 'main'");
                    }
                    if let Some(_) = found_main_sub {
                        bail_nospan!("multiple 'main' scripts");
                    }
                    found_main_sub = Some(code);
                },
                Item::FileList { .. } => bail_nospan!("unexpected file list in STD file"),
                Item::Func { .. } => bail_nospan!("unexpected function def in STD file"),
            }
        }
        match (found_meta, found_main_sub) {
            (Some(meta), Some(main)) => (meta, main),
            (None, _) => bail_nospan!("missing 'main' sub"),
            (Some(_), None) => bail_nospan!("missing 'meta' section"),
        }
    };

    let mut out = StdFile::from_meta(meta).map_err(|e| CompileError(vec![Diagnostic::error().with_message(format!("{}", e))]))?;
    out.script = _compile_main(format, &main_sub.0, functions)?;

    Ok(out)
}

fn _compile_main(
    format: &dyn InstrFormat,
    code: &[Spanned<ast::Stmt>],
    functions: &Functions,
) -> Result<Vec<Instr>, CompileError> {
    use crate::signature::ArgEncoding;

    let intrinsic_opcodes: HashMap<_, _> = format.intrinsic_opcode_pairs().into_iter().collect();

    let mut out = vec![];
    for stmt in code {
        for label in &stmt.labels {
            match &label.value {
                ast::StmtLabel::Label(ident) => out.push(InstrOrLabel::Label(ident.clone())),
                ast::StmtLabel::Difficulty { .. } => bail_span!(label, "difficulty labels not supported by STD"),
            }
        }

        match &stmt.body.value {
            ast::StmtBody::Jump(goto) => {
                let time_arg = match goto.time {
                    Some(time) => InstrArg::DwordBits(time as u32),
                    None => InstrArg::TimeOf(goto.destination.clone()),
                };
                out.push(InstrOrLabel::Instr(Instr {
                    time: stmt.time,
                    opcode: match intrinsic_opcodes.get(&IntrinsicInstrKind::Jmp) {
                        Some(&opcode) => opcode,
                        None => bail_span!(stmt, "'goto' not supported by current format"),
                    },
                    args: vec![InstrArg::Label(goto.destination.clone()), time_arg],
                }));
            },
            ast::StmtBody::Expr(e) => match &e.value {
                ast::Expr::Call { func, args } => {
                    let siggy = match functions.ins_signature(func) {
                        Some(siggy) => siggy,
                        None => bail_span!(stmt, "signature of {} is not known", func),
                    };
                    let opcode = match functions.resolve_aliases(func).as_ins() {
                        Some(opcode) => opcode,
                        None => bail_span!(stmt, "don't know how to compile function {} (not an instruction)", func),
                    };
                    let encodings = siggy.arg_encodings();
                    if encodings.len() != args.len() {
                        bail_span!(stmt, "wrong number of arguments (expected {}, got {})", encodings.len(), args.len())
                    }

                    out.push(InstrOrLabel::Instr(Instr {
                        time: stmt.time,
                        opcode: opcode as _,
                        args: encodings.iter().zip(args).enumerate().map(|(index, (enc, arg))| match enc {
                            ArgEncoding::Dword |
                            ArgEncoding::Color => match **arg {
                                ast::Expr::LitInt { value, .. } => Ok(InstrArg::DwordBits(value as u32)),
                                ast::Expr::LitFloat { .. } |
                                ast::Expr::LitString { .. } => bail_span!(arg, "expected an int for arg {} of {}", index+1, func),
                                _ => bail_span!(arg, "unsupported expression type in STD file"),
                            },
                            ArgEncoding::Float => match **arg {
                                ast::Expr::LitFloat { value, .. } => Ok(InstrArg::DwordBits(value.to_bits())),
                                ast::Expr::LitInt { .. } |
                                ast::Expr::LitString { .. } => bail_span!(arg, "expected a float for arg {} of {}", index+1, func),
                                _ => bail_span!(arg, "unsupported expression type in STD file"),
                            },
                        }).collect::<Result<_, _>>()?,
                    }));
                },
                _ => bail_span!(stmt, "unsupported expression type in STD file"),
            },
            _ => bail_span!(stmt, "unsupported statement type in STD file"),
        }
    }
    // And fix the labels
    encode_labels(format, 0, &mut out)?;

    Ok(out.into_iter().filter_map(|x| match x {
        InstrOrLabel::Instr(instr) => Some(instr),
        InstrOrLabel::Label(_) => None,
    }).collect())
}

struct RawLabelInfo {
    time: i32,
    offset: usize,
}
fn gather_label_info(
    format: &dyn InstrFormat,
    initial_offset: usize,
    code: &[InstrOrLabel]
) -> Result<HashMap<Spanned<Ident>, RawLabelInfo>, CompileError> {
    use std::collections::hash_map::Entry;

    let mut offset = initial_offset;
    let mut pending_labels = vec![];
    let mut out = HashMap::new();
    for thing in code {
        match thing {
            // can't insert labels until we see the time of the intructions they are labeling
            InstrOrLabel::Label(ident) => pending_labels.push(ident),
            InstrOrLabel::Instr(instr) => {
                for label in pending_labels.drain(..) {
                    match out.entry(label.clone()) {
                        Entry::Vacant(e) => {
                            e.insert(RawLabelInfo { time: instr.time, offset });
                        },
                        Entry::Occupied(e) => {
                            let old = e.key();
                            return Err(CompileError(vec![Diagnostic::error().with_labels(vec![
                                Label::primary(label.span.file_id, label.span).with_message("duplicate label"),
                                Label::secondary(old.span.file_id, old.span).with_message("previously defined here"),
                            ]).with_message(format!("label '{}' already defined", label))]));
                        },
                    }
                }
                offset += format.instr_size(instr);
            },
        }
    }
    assert!(pending_labels.is_empty(), "unexpected label after last instruction! (bug?)");
    Ok(out)
}

/// Eliminates all `InstrOrLabel::Label`s by replacing them with their dword values.
fn encode_labels(
    format: &dyn InstrFormat,
    initial_offset: usize,
    code: &mut [InstrOrLabel],
) -> Result<(), CompileError> {
    let label_info = gather_label_info(format, initial_offset, code)?;

    for thing in code {
        match thing {
            InstrOrLabel::Instr(instr) => for arg in &mut instr.args {
                match *arg {
                    | InstrArg::Label(ref label)
                    | InstrArg::TimeOf(ref label)
                    => match label_info.get(label) {
                        Some(info) => match arg {
                            InstrArg::Label(_) => *arg = InstrArg::DwordBits(format.encode_label(info.offset)),
                            InstrArg::TimeOf(_) => *arg = InstrArg::DwordBits(info.time as u32),
                            _ => unreachable!(),
                        },
                        // FIXME: gather multiple errors
                        None => bail_span!(label, "no such label"),
                    },
                    _ => {},
                }
            },
            InstrOrLabel::Label(_) => {},
        }
    }
    Ok(())
}

// =============================================================================

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntrinsicInstrKind {
    Jmp,
}

pub trait InstrFormat {
    /// Get the number of bytes in the binary encoding of an instruction.
    fn instr_size(&self, instr: &Instr) -> usize;

    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, u16)>;

    /// Read a single script instruction from an input stream.
    ///
    /// Should return `None` when it reaches the marker that indicates the end of the script.
    /// When this occurs, it may leave the `Cursor` in an indeterminate state.
    fn read_instr(&self, f: &mut Cursor<&[u8]>) -> Option<Instr>;

    /// Write a single script instruction into an output stream.
    fn write_instr(&self, f: &mut dyn Write, instr: &Instr) -> io::Result<()>;

    /// Write a marker that goes after the final instruction in a function or script.
    fn write_terminal_instr(&self, f: &mut dyn Write) -> io::Result<()>;

    // Most formats encode labels as offsets from the beginning of the script (in which case
    // these functions are trivial), but early STD is a special snowflake that writes the
    // instruction *index* instead.
    fn encode_label(&self, offset: usize) -> u32;
    fn decode_label(&self, bits: u32) -> usize;
}

pub trait WriteSeek: Write + Seek {
    fn as_mut_write(&mut self) -> &mut dyn Write;
}
impl<W: Write + Seek> WriteSeek for W {
    fn as_mut_write(&mut self) -> &mut dyn Write { self }
}

// =============================================================================

// FIXME clean up API, return Result
pub fn read_std(format: &dyn InstrFormat, bytes: &[u8]) -> StdFile {
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
    assert_eq!(num_quads, entries.iter().map(|x| x.quads.len()).sum::<usize>());
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
        while let Some(instr) = format.read_instr(&mut f) {
            script.push(instr);
        }
        script
    };
    StdFile { unknown, extra, entries, instances, script }
}

pub fn write_std(format: &dyn InstrFormat, f: &mut dyn WriteSeek, std: &StdFile) -> io::Result<()> {
    let start_pos = f.seek(io::SeekFrom::Current(0))?;

    f.write_u16::<Le>(std.entries.len() as u16)?;
    f.write_u16::<Le>(std.entries.iter().map(|x| x.quads.len()).sum::<usize>() as u16)?;

    let instances_offset_pos = f.seek(io::SeekFrom::Current(0))?;
    f.write_u32::<Le>(0)?;
    let script_offset_pos = f.seek(io::SeekFrom::Current(0))?;
    f.write_u32::<Le>(0)?;

    f.write_u32::<Le>(std.unknown)?;

    write_extra(f.as_mut_write(), &std.extra)?;

    let entry_offsets_pos = f.seek(io::SeekFrom::Current(0))?;
    for _ in &std.entries {
        f.write_u32::<Le>(0)?;
    }

    let mut entry_offsets = vec![];
    for entry in &std.entries {
        entry_offsets.push(f.seek(io::SeekFrom::Current(0))? - start_pos);
        write_entry(f.as_mut_write(), entry)?;
    }

    let instances_offset = f.seek(io::SeekFrom::Current(0))? - start_pos;
    for instance in &std.instances {
        write_instance(f.as_mut_write(), instance)?;
    }
    write_terminal_instance(f.as_mut_write())?;

    let script_offset = f.seek(io::SeekFrom::Current(0))? - start_pos;
    for instr in &std.script {
        format.write_instr(f.as_mut_write(), instr)?;
    }
    format.write_terminal_instr(f.as_mut_write())?;

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
    Some(StdExtra::Th10 { anm_path: read_string_128(f) })
}
fn write_extra(f: &mut dyn Write, x: &StdExtra) -> io::Result<()> {
    match x {
        StdExtra::Th10 { anm_path } => write_string_128(f, anm_path.as_bstr())?,
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
fn write_string_128(f: &mut dyn Write, s: &BStr) -> io::Result<()> {
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

fn write_vec2(f: &mut dyn Write, x: &[f32; 2]) -> io::Result<()> {
    f.write_f32::<Le>(x[0])?;
    f.write_f32::<Le>(x[1])?;
    Ok(())
}
fn write_vec3(f: &mut dyn Write, x: &[f32; 3]) -> io::Result<()> {
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

fn write_entry(f: &mut dyn Write, x: &Entry) -> io::Result<()> {
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

    let anm_script = f.read_u16::<Le>().expect("unexpected EOF");
    match f.read_u16::<Le>().expect("unexpected EOF") {
        0 => {},
        s => panic!("unexpected nonzero padding: {}", s),
    };

    let pos = read_vec3(f).expect("unexpected EOF");
    let size = read_vec2(f).expect("unexpected EOF");
    Some(Quad { unknown, anm_script, pos, size })
}

fn write_quad(f: &mut dyn Write, quad: &Quad) -> io::Result<()> {
    f.write_u16::<Le>(quad.unknown)?;
    f.write_u16::<Le>(0x1c)?; // size
    f.write_u16::<Le>(quad.anm_script)?;
    f.write_u16::<Le>(0)?;
    write_vec3(f, &quad.pos)?;
    write_vec2(f, &quad.size)?;
    Ok(())
}
fn write_terminal_quad(f: &mut dyn Write) -> io::Result<()> {
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

fn write_instance(f: &mut dyn Write, inst: &Instance) -> io::Result<()> {
    f.write_u16::<Le>(inst.object_id)?;
    f.write_u16::<Le>(inst.unknown)?;
    write_vec3(f, &inst.pos)?;
    Ok(())
}
fn write_terminal_instance(f: &mut dyn Write) -> io::Result<()> {
    for _ in 0..4 {
        f.write_i32::<Le>(-1)?;
    }
    Ok(())
}

pub struct InstrFormat10;
impl InstrFormat for InstrFormat10 {
    fn read_instr(&self, f: &mut Cursor<&[u8]>) -> Option<Instr> {
        let time = f.read_i32::<Le>().expect("unexpected EOF");
        let opcode = f.read_i16::<Le>().expect("unexpected EOF");
        let size = f.read_u16::<Le>().expect("unexpected EOF");
        if opcode == -1 {
            return None
        }

        assert_eq!(size % 4, 0);
        let nargs = (size - 8)/4;
        let args = (0..nargs).map(|_| {
            InstrArg::DwordBits(f.read_u32::<Le>().expect("unexpected EOF"))
        }).collect::<Vec<_>>();
        Some(Instr { time, opcode: opcode as u16, args })
    }

    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, u16)> {
        vec![(IntrinsicInstrKind::Jmp, 1)]
    }

    fn write_instr(&self, f: &mut dyn Write, instr: &Instr) -> io::Result<()> {
        f.write_i32::<Le>(instr.time)?;
        f.write_u16::<Le>(instr.opcode)?;
        f.write_u16::<Le>(8 + 4 * instr.args.len() as u16)?;
        for x in &instr.args {
            f.write_u32::<Le>(x.expect_dword())?;
        }
        Ok(())
    }

    fn write_terminal_instr(&self, f: &mut dyn Write) -> io::Result<()> {
        for _ in 0..5 {
            f.write_i32::<Le>(-1)?;
        }
        Ok(())
    }

    fn instr_size(&self, instr: &Instr) -> usize {
        instr.args.len() * 4 + 8
    }

    fn encode_label(&self, offset: usize) -> u32 { offset as u32 }
    fn decode_label(&self, bits: u32) -> usize { bits as usize }
}
