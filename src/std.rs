use std::io::{self, Read, Cursor, Write, Seek};
use std::collections::{HashMap};

use byteorder::{LittleEndian as Le, ReadBytesExt, WriteBytesExt};
use bstr::{BStr, BString, ByteSlice};
use crate::error::{Diagnostic, Label};

use crate::CompileError;
use crate::pos::{Spanned};
use crate::ast::{self, Expr};
use crate::ident::Ident;
use crate::signature::{Functions, Signature, ArgEncoding};
use crate::meta::{self, ToMeta, FromMeta, Meta, FromMetaError};
use crate::game::Game;

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
        stage_name: BString,
        bgm_names: [BString; 4],
        bgm_paths: [BString; 4],
    },
    Th10 {
        anm_path: BString,
    },
}

impl StdFile {
    pub fn decompile(&self, game: Game, functions: &Functions) -> ast::Script {
        _decompile_std(&*game_format(game), self, functions)
    }

    pub fn compile(game: Game, script: &ast::Script, functions: &Functions) -> Result<Self, CompileError> {
        _compile_std(&*game_format(game), script, functions)
    }
}

impl StdFile {
    fn init_from_meta<'m>(file_format: &dyn FileFormat, meta: &'m Meta) -> Result<Self, FromMetaError<'m>> {
        meta.parse_object(|m| Ok(StdFile {
            unknown: m.expect_field("unknown")?,
            entries: m.expect_field("objects")?,
            instances: m.expect_field("instances")?,
            script: vec![],
            extra: file_format.extra_from_meta(m)?,
        }))
    }

    fn make_meta(&self, file_format: &dyn FileFormat) -> Meta {
        Meta::make_object()
            .field("unknown", &self.unknown)
            .with_mut(|b| file_format.extra_to_meta(&self.extra, b))
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
        meta.parse_object(|m| Ok(Entry {
            id: m.expect_field::<i32>("id")? as u16,
            unknown: m.expect_field::<i32>("unknown")? as u16,
            pos: m.expect_field("pos")?,
            size: m.expect_field("size")?,
            quads: m.expect_field("quads")?,
        }))
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
    pub anm_script: u16,
    pub extra: QuadExtra,
}

#[derive(Debug, Clone, PartialEq)]
pub enum QuadExtra {
    /// Type 0 quad.
    Rect {
        pos: [f32; 3],
        size: [f32; 2],
    },
    /// Type 1 quad. Only available in IN and PoFV.
    Strip {
        start: [f32; 3],
        end: [f32; 3],
        width: f32,
    }
}

impl FromMeta for Quad {
    fn from_meta(meta: &Meta) -> Result<Self, FromMetaError<'_>> {
        meta.parse_variant()?
            .variant("rect", |m| Ok(Quad {
                anm_script: m.expect_field::<i32>("anm_script")? as u16,
                extra: QuadExtra::Rect {
                    pos: m.expect_field("pos")?,
                    size: m.expect_field("size")?,
                },
            }))
            .variant("strip", |m| Ok(Quad {
                anm_script: m.expect_field::<i32>("anm_script")? as u16,
                extra: QuadExtra::Strip {
                    start: m.expect_field("start")?,
                    end: m.expect_field("end")?,
                    width: m.expect_field("width")?,
                },
            }))
            .finish()
    }
}

impl ToMeta for Quad {
    fn to_meta(&self) -> Meta {
        let variant = match self.extra {
            QuadExtra::Rect { .. } => "rect",
            QuadExtra::Strip { .. } => "strip",
        };

        Meta::make_variant(variant)
            .field("anm_script", &(self.anm_script as i32))
            .with_mut(|b| match &self.extra {
                QuadExtra::Rect { pos, size } => {
                    b.field("pos", pos);
                    b.field("size", size);
                },
                QuadExtra::Strip { start, end, width } => {
                    b.field("start", start);
                    b.field("end", end);
                    b.field("width", width);
                },
            })
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
        meta.parse_object(|meta| Ok(Instance {
            object_id: meta.expect_field::<i32>("object")? as u16,
            unknown: meta.get_field::<i32>("unknown")?.unwrap_or(256) as u16,
            pos: meta.expect_field("pos")?,
        }))
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

fn _decompile_std(format: &dyn FileFormat, std: &StdFile, functions: &Functions) -> ast::Script {
    let instr_format = format.instr_format();

    let opcode_intrinsics: HashMap<_, _> = {
        instr_format.intrinsic_opcode_pairs().into_iter()
            .map(|(a, b)| (b, a)).collect()
    };

    let default_label = |offset: usize| {
        Spanned::null_from(format!("label_{}", offset).parse::<Ident>().unwrap())
    };

    let mut offset = 0;
    let code = std.script.iter().map(|instr| {
        // For now we give every instruction a label and strip the unused ones later.
        let this_instr_label = Spanned::null_from(ast::StmtLabel::Label(default_label(offset)));
        offset += instr_format.instr_size(instr);

        let Instr { time, opcode, args } = instr;

        match opcode_intrinsics.get(&opcode) {
            Some(IntrinsicInstrKind::Jmp) => {
                assert!(args.len() >= 2); // FIXME: print proper error
                assert!(args[2..].iter().all(|a| a.expect_dword() == 0), "unsupported data in padding of intrinsic");

                let dest_offset = instr_format.decode_label(args[0].expect_dword());
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

        Spanned::null_from(ast::Stmt {
            time: *time,
            labels: vec![this_instr_label],
            body: Spanned::from(ast::StmtBody::Expr(Spanned::from(Expr::Call {
                args: match functions.ins_signature(&ins_ident) {
                    Some(siggy) => decompile_args(args, siggy),
                    None => decompile_args(args, &crate::signature::Signature::auto(args.len())),
                },
                func: ins_ident,
            }))),
        })
    }).collect();

    let code = {
        use crate::passes::unused_labels;
        use crate::ast::VisitMut;

        let mut code = ast::Block(code);
        unused_labels::Visitor::new().visit_func_body(&mut code);
        code
    };

    ast::Script {
        items: vec! [
            Spanned::from(ast::Item::Meta {
                keyword: ast::MetaKeyword::Meta,
                name: None,
                meta: std.make_meta(format),
            }),
            Spanned::from(ast::Item::AnmScript {
                number: None,
                name: "main".parse().unwrap(),
                code,
            }),
        ],
    }
}

fn decompile_args(args: &[InstrArg], siggy: &Signature) -> Vec<Spanned<Expr>> {
    let encodings = siggy.arg_encodings();

    // FIXME this fails sometimes
    assert_eq!(args.len(), encodings.len()); // FIXME: return Error
    let mut out = encodings.iter().zip(args).map(|(enc, arg)| {
        let bits = arg.expect_dword();
        match enc {
            ArgEncoding::Dword => <Spanned<Expr>>::null_from(bits as i32),
            ArgEncoding::Padding => <Spanned<Expr>>::null_from(bits as i32),
            ArgEncoding::Color => Spanned::null_from(Expr::LitInt {
                value: bits as i32,
                hex: true,
            }),
            ArgEncoding::Float => <Spanned<Expr>>::null_from(f32::from_bits(bits)),
        }
    }).collect::<Vec<_>>();

    // drop early STD padding args from the end as long as they're zero
    for (enc, arg) in encodings.iter().zip(args).rev() {
        match (enc, arg) {
            (ArgEncoding::Padding, InstrArg::DwordBits(0)) => out.pop(),
            _ => break,
        };
    }
    out
}

fn _compile_std(
    format: &dyn FileFormat,
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

    let mut out = StdFile::init_from_meta(format, meta).map_err(|e| {
        CompileError(vec![Diagnostic::error().with_message(format!("{}", e))])
    })?;
    out.script = _compile_main(format.instr_format(), &main_sub.0, functions)?;

    Ok(out)
}

fn _compile_main(
    format: &dyn InstrFormat,
    code: &[Spanned<ast::Stmt>],
    functions: &Functions,
) -> Result<Vec<Instr>, CompileError> {
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
                    if !(siggy.min_args() <= args.len() && args.len() <= siggy.max_args()) {
                        bail_span!(stmt, "wrong number of arguments (expected {}, got {})", encodings.len(), args.len())
                    }

                    out.push(InstrOrLabel::Instr(Instr {
                        time: stmt.time,
                        opcode: opcode as _,
                        args: compile_args(func, args, &encodings)?,
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

fn compile_args(func: &Ident, args: &[Spanned<Expr>], encodings: &[ArgEncoding]) -> Result<Vec<InstrArg>, CompileError> {
    encodings.iter().zip(args).enumerate().map(|(index, (enc, arg))| match enc {
        ArgEncoding::Padding |
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
    }).collect::<Result<_, _>>()
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
pub fn read_std(game: Game, bytes: &[u8]) -> StdFile {
    let format = game_format(game);

    let mut f = Cursor::new(bytes);

    let num_entries = f.read_u16::<Le>().expect("incomplete header") as usize;
    let num_quads = f.read_u16::<Le>().expect("incomplete header") as usize;
    let instances_offset = f.read_u32::<Le>().expect("incomplete header") as usize;
    let script_offset = f.read_u32::<Le>().expect("incomplete header") as usize;
    let unknown = f.read_u32::<Le>().expect("incomplete header");
    let extra = format.read_extra(&mut f);
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

    let instr_format = format.instr_format();
    let script = {
        let mut f = Cursor::new(&bytes[script_offset..]);
        let mut script = vec![];
        while let Some(instr) = instr_format.read_instr(&mut f) {
            script.push(instr);
        }
        script
    };
    StdFile { unknown, extra, entries, instances, script }
}

pub fn write_std(game: Game, f: &mut dyn WriteSeek, std: &StdFile) -> io::Result<()> {
    let format = game_format(game);

    let start_pos = f.seek(io::SeekFrom::Current(0))?;

    f.write_u16::<Le>(std.entries.len() as u16)?;
    f.write_u16::<Le>(std.entries.iter().map(|x| x.quads.len()).sum::<usize>() as u16)?;

    let instances_offset_pos = f.seek(io::SeekFrom::Current(0))?;
    f.write_u32::<Le>(0)?;
    let script_offset_pos = f.seek(io::SeekFrom::Current(0))?;
    f.write_u32::<Le>(0)?;

    f.write_u32::<Le>(std.unknown)?;

    format.write_extra(f.as_mut_write(), &std.extra)?;

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

    let instr_format = format.instr_format();

    let script_offset = f.seek(io::SeekFrom::Current(0))? - start_pos;
    for instr in &std.script {
        instr_format.write_instr(f.as_mut_write(), instr)?;
    }
    instr_format.write_terminal_instr(f.as_mut_write())?;

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
    let kind = f.read_i16::<Le>().expect("unexpected EOF");
    let size = f.read_u16::<Le>().expect("unexpected EOF");
    match (kind, size) {
        (-1, 4) => return None, // no more quads
        (0, 0x1c) => false,
        (1, 0x24) => true,
        (-1, _) | (0, _) | (1, _) => {
            panic!("unexpected size for type {} quad: {:#x}", kind, size);
        },
        _ => panic!("unknown quad type: {}", kind),
    };

    let anm_script = f.read_u16::<Le>().expect("unexpected EOF");
    match f.read_u16::<Le>().expect("unexpected EOF") {
        0 => {},  // This word is zero in the file, and used to store an index in-game.
        s => panic!("unexpected data in quad index field: {:#04x}", s),
    };

    Some(Quad {
        anm_script,
        extra: match kind {
            0 => QuadExtra::Rect {
                pos: read_vec3(f).expect("unexpected EOF"),
                size: read_vec2(f).expect("unexpected EOF"),
            },
            1 => QuadExtra::Strip {
                start: read_vec3(f).expect("unexpected EOF"),
                end: read_vec3(f).expect("unexpected EOF"),
                width: f.read_f32::<Le>().expect("unexpected EOF"),
            },
            _ => unreachable!(),
        },
    })
}

fn write_quad(f: &mut dyn Write, quad: &Quad) -> io::Result<()> {
    let (kind, size) = match quad.extra {
        QuadExtra::Rect { .. } => (0, 0x1c),
        QuadExtra::Strip { .. } => (1, 0x24),
    };
    f.write_i16::<Le>(kind)?;
    f.write_u16::<Le>(size)?;
    f.write_u16::<Le>(quad.anm_script)?;
    f.write_u16::<Le>(0)?;
    match quad.extra {
        QuadExtra::Rect { pos, size } => {
            write_vec3(f, &pos)?;
            write_vec2(f, &size)?;
        },
        QuadExtra::Strip { start, end, width } => {
            write_vec3(f, &start)?;
            write_vec3(f, &end)?;
            f.write_f32::<Le>(width)?;
        },
    }
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

fn game_format(game: Game) -> Box<dyn FileFormat> {
    match game {
        Game::Th06
        => Box::new(FileFormat06 { instr_format: InstrFormat06 { has_jmp: false } }),

        g if (Game::Th07 <= g && g <= Game::Th09)
        => Box::new(FileFormat06 { instr_format: InstrFormat06 { has_jmp: true } }),

        _ => Box::new(FileFormat10),
    }
}

/// STD format, EoSD to PoFV.
struct FileFormat06 { instr_format: InstrFormat06 }
/// STD format, StB to present.
struct FileFormat10;

trait FileFormat {
    fn extra_from_meta<'m>(&self, meta: &mut meta::ParseObject<'m>) -> Result<StdExtra, FromMetaError<'m>>;
    fn extra_to_meta(&self, extra: &StdExtra, b: &mut meta::BuildObject);
    fn read_extra(&self, f: &mut Cursor<&[u8]>) -> StdExtra;
    fn write_extra(&self, f: &mut dyn Write, x: &StdExtra) -> io::Result<()>;
    fn instr_format(&self) -> &dyn InstrFormat;
}

impl FileFormat for FileFormat06 {
    fn extra_from_meta<'m>(&self, m: &mut meta::ParseObject<'m>) -> Result<StdExtra, FromMetaError<'m>> {
        Ok(StdExtra::Th06 {
            stage_name: m.expect_field("stage_name")?,
            bgm_names: m.expect_field("bgm_names")?,
            bgm_paths: m.expect_field("bgm_paths")?,
        })
    }

    fn extra_to_meta(&self, extra: &StdExtra, b: &mut meta::BuildObject) {
        match extra {
            StdExtra::Th10 { .. } => unreachable!(),
            StdExtra::Th06 { stage_name, bgm_names, bgm_paths } => {
                b.field("stage_name", stage_name);
                b.field("bgm_names", bgm_names);
                b.field("bgm_paths", bgm_paths);
            },
        }
    }

    fn read_extra(&self, f: &mut Cursor<&[u8]>) -> StdExtra {
        StdExtra::Th06 {
            stage_name: read_string_128(f),
            bgm_names: [
                read_string_128(f), read_string_128(f),
                read_string_128(f), read_string_128(f),
            ],
            bgm_paths: [
                read_string_128(f), read_string_128(f),
                read_string_128(f), read_string_128(f),
            ],
        }
    }

    fn write_extra(&self, f: &mut dyn Write, x: &StdExtra) -> io::Result<()> {
        match x {
            StdExtra::Th06 { stage_name, bgm_names, bgm_paths } => {
                write_string_128(f, stage_name.as_ref())?;
                for s in bgm_names.iter().chain(bgm_paths) {
                    write_string_128(f, s.as_ref())?;
                }
            },
            StdExtra::Th10 { .. } => unreachable!(),
        };
        Ok(())
    }

    fn instr_format(&self) -> &dyn InstrFormat { &self.instr_format }
}

impl FileFormat for FileFormat10 {
    fn extra_from_meta<'m>(&self, m: &mut meta::ParseObject<'m>) -> Result<StdExtra, FromMetaError<'m>> {
        Ok(StdExtra::Th10 {
            anm_path: m.expect_field("anm_file")?,
        })
    }

    fn extra_to_meta(&self, extra: &StdExtra, b: &mut meta::BuildObject) {
        match extra {
            StdExtra::Th10 { anm_path } => { b.field("anm_path", anm_path); },
            StdExtra::Th06 { .. } => unreachable!(),
        }
    }

    fn read_extra(&self, f: &mut Cursor<&[u8]>) -> StdExtra {
        StdExtra::Th10 { anm_path: read_string_128(f) }
    }

    fn write_extra(&self, f: &mut dyn Write, x: &StdExtra) -> io::Result<()> {
        match x {
            StdExtra::Th10 { anm_path } => write_string_128(f, anm_path.as_ref())?,
            StdExtra::Th06 { .. } => unreachable!(),
        };
        Ok(())
    }

    fn instr_format(&self) -> &dyn InstrFormat { &InstrFormat10 }
}

pub struct InstrFormat06 { has_jmp: bool }
pub struct InstrFormat10;
impl InstrFormat for InstrFormat06 {
    fn read_instr(&self, f: &mut Cursor<&[u8]>) -> Option<Instr> {
        let time = f.read_i32::<Le>().expect("unexpected EOF");
        let opcode = f.read_i16::<Le>().expect("unexpected EOF");
        let argsize = f.read_u16::<Le>().expect("unexpected EOF");
        if opcode == -1 {
            return None
        }

        assert_eq!(argsize, 12);
        let args = (0..3).map(|_| {
            InstrArg::DwordBits(f.read_u32::<Le>().expect("unexpected EOF"))
        }).collect::<Vec<_>>();
        Some(Instr { time, opcode: opcode as u16, args })
    }

    fn intrinsic_opcode_pairs(&self) -> Vec<(IntrinsicInstrKind, u16)> {
        match self.has_jmp {
            false => vec![],
            true => vec![(IntrinsicInstrKind::Jmp, 4)],
        }
    }

    fn write_instr(&self, f: &mut dyn Write, instr: &Instr) -> io::Result<()> {
        f.write_i32::<Le>(instr.time)?;
        f.write_u16::<Le>(instr.opcode)?;
        f.write_u16::<Le>(12)?;
        for arg in &instr.args {
            f.write_u32::<Le>(arg.expect_dword())?;
        }
        for _ in instr.args.len()..3 {
            f.write_u32::<Le>(0)?;  // padding
        }
        Ok(())
    }

    fn write_terminal_instr(&self, f: &mut dyn Write) -> io::Result<()> {
        for _ in 0..5 {
            f.write_i32::<Le>(-1)?;
        }
        Ok(())
    }

    fn instr_size(&self, _instr: &Instr) -> usize { 20 }

    fn encode_label(&self, offset: usize) -> u32 {
        assert_eq!(offset % 20, 0);
        (offset / 20) as u32
    }
    fn decode_label(&self, bits: u32) -> usize {
        (bits * 20) as usize
    }
}

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
