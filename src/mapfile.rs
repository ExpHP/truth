use std::collections::{BTreeMap};

use crate::resolve::IdMap;
use crate::pos::{Sp, FileId};
use crate::game::{Game, LanguageKey};
use crate::diagnostic::{RootEmitter, Emitter};
use crate::ident::Ident;
use crate::io::Fs;
use crate::parse::seqmap::{SeqmapRaw, SeqmapRawSection};
use crate::error::{ErrorReported, GatherErrorIteratorExt};

#[derive(Debug)]
pub struct Mapfile {
    pub language: LanguageKey,
    pub ins_names: Vec<(i32, Sp<Ident>)>,
    pub ins_signatures: Vec<(i32, Sp<String>)>,
    pub ins_rets: Vec<(i32, Sp<String>)>,
    pub gvar_names: Vec<(i32, Sp<Ident>)>,
    pub gvar_types: Vec<(i32, Sp<String>)>,
    pub ins_intrinsics: Vec<(i32, Sp<String>)>,
    /// For historic reasons, [`InstrLanguage::Timeline`] has dedicated sections.
    /// When these are seen in a file, they will always define things for timelines
    /// instead of [`Self::language`].
    pub timeline_ins_names: Vec<(i32, Sp<Ident>)>,
    pub timeline_ins_signatures: Vec<(i32, Sp<String>)>,
    pub difficulty_flags: Vec<(i32, Sp<String>)>,
    pub enums: IdMap<Sp<Ident>, Vec<(i32, Sp<Ident>)>>,

    /// Indicates that this mapfile contains builtin definitions.
    ///
    /// Core mapfiles are allowed to contain null spans, so care must be taken when using them
    /// in diagnostics.  (since core mapfiles can be trusted to contain valid definitions,
    /// this issue really only comes up when showing messages of the "expected X due to definition
    /// of Y located here in this mapfile" variety)
    pub is_core_mapfile: bool,
}

impl Mapfile {
    pub fn new_core_mapfile(language: LanguageKey) -> Self {
        Mapfile {
            language,
            ins_names: Default::default(),
            ins_signatures: Default::default(),
            ins_rets: Default::default(),
            gvar_names: Default::default(),
            gvar_types: Default::default(),
            timeline_ins_names: Default::default(),
            timeline_ins_signatures: Default::default(),
            difficulty_flags: Default::default(),
            ins_intrinsics: Default::default(),
            enums: Default::default(),
            is_core_mapfile: true,
        }
    }

    pub fn load(
        path: impl AsRef<std::path::Path>,
        game: Option<Game>,
        emitter: &RootEmitter,
        // Things gets a bit ugly because a map can refer to more maps
        mut read_file: impl FnMut(&std::path::Path) -> Result<(FileId, String), ErrorReported>,
    ) -> Result<Self, ErrorReported> {
        // canonicalize so paths in gamemaps can be interpreted relative to the gamemap path
        let path = path.as_ref();
        let fs = Fs::new(emitter);
        let path = fs.canonicalize(path).map_err(|e| emitter.emit(e))?;

        let (file_id, mut file_contents) = read_file(&path)?;
        let seqmap = SeqmapRaw::parse(file_id, &file_contents, emitter)?;

        // if the map is a gamemap, it points to another file; that's the one we really want.
        let seqmap = if seqmap.magic == "!gamemap" {
            let game = match game {
                Some(game) => game,
                None => return Err(emitter.emit(error!("can't use gamemap because no game was supplied!")))
            };
            let base_dir = path.parent().expect("filename must have parent");
            let game_specific_map_path = Self::handle_gamemap(base_dir, seqmap, game, emitter)?;
            let (file_id, new_file_contents) = read_file(&game_specific_map_path)?;
            file_contents = new_file_contents; // replace outer variable for longer lifetime
            SeqmapRaw::parse(file_id, &file_contents, emitter)?
        } else {
            seqmap
        };
        Self::from_seqmap(seqmap, emitter)
    }

    /// Check the default map directories for a file whose name is `any.{extension}`
    /// and return it if it exists.
    ///
    /// Intended to be used with `Option::or_else` on an optional map path during decompilation.
    pub fn decomp_map_file_from_env(extension: &'static str) -> Option<std::path::PathBuf> {
        std::env::var_os("TRUTH_MAP_PATH")
            .filter(|s| !s.is_empty())
            .into_iter().flat_map(|paths| {
                std::env::split_paths(&paths)
                    .map(|p| p.join(format!("any.{}", extension.trim_start_matches("."))))
                    .filter(|p| p.exists())
                    .take(1).collect::<Vec<_>>()  // stop borrowing
            }).next()
    }

    fn handle_gamemap(
        base_dir: &std::path::Path,
        seqmap: SeqmapRaw,
        game: Game,
        emitter: &impl Emitter,
    ) -> Result<std::path::PathBuf, ErrorReported> {
        let SeqmapRaw { magic, sections } = seqmap;
        let GatheredSeqmaps { mut maps, enum_maps } = gather_seqmaps(sections);

        let game_files_header = "game_files".to_string();

        let game_files = match maps.remove(&game_files_header) {
            Some(game_files) => mapify_section(&game_files_header, game_files, emitter)?,
            None => return Err(emitter.emit(error!(
                message("no !game_files section in gamemap"),
                primary(magic, "gamemap without !game_files section"),
            ))),
        };
        for (key, _) in maps.into_iter().chain(enum_maps) {
            emitter.emit(warning!(
                message("unrecognized section in gamemap: {:?}", key),
                primary(key, "unrecognized section"),
            )).ignore();
        }
        let rel_path = match game_files.get(&(game.as_number() as i32)) {
            Some(file) => file,
            None => return Err(emitter.emit(error!(
                message("no entry for {}", game.as_str()),
                primary(magic, "gamemap has no entry for {}", game.as_str()),
            ))),
        };

        Ok(base_dir.join(rel_path))
    }

    pub fn from_seqmap(seqmap: SeqmapRaw, emitter: &impl Emitter) -> Result<Mapfile, ErrorReported> {
        let SeqmapRaw { magic, sections } = seqmap;
        let GatheredSeqmaps { mut maps, enum_maps } = gather_seqmaps(sections);

        // NOTE: Experimental.  We have two options for deciding the language:
        //
        //   - Take the language as an argument to this function (since it should be known, anyways).
        //     (this could be better for Ending MSG)
        //   - Decide it from the magic.
        //     (this could facilitate the separation of "timelinemap"s out from eclmaps)
        //
        // Neither is a clear winner at this point in time, but deciding it from the magic is a smaller
        // diff so we do that for now.    - Exp
        let language = match &magic[..] {
            "!eclmap" => LanguageKey::Ecl,
            "!anmmap" => LanguageKey::Anm,
            "!stdmap" => LanguageKey::Std,
            "!msgmap" => LanguageKey::Msg,
            _ => return Err(emitter.emit(error!(
                message("bad magic: {:?}", magic),
                primary(magic, "bad magic"),
            ))),
        };

        let mut pop_map = |section: &str| maps.remove(&section.to_string()).unwrap_or_else(Vec::new);
        let parse_idents = |section: &str, m: Vec<(i32, Sp<String>)>| -> Result<Vec<(i32, Sp<Ident>)>, ErrorReported> {
            emitter.chain_with(|f| write!(f, "section !{}", section), |emitter| {
                m.into_iter().map(|(key, value)| {
                    let ident = Ident::new_user(&value).map_err(|e| emitter.emit(error!(
                        message("at key {}: {}", key, e),
                        primary(value, "bad identifier"),
                    )))?;
                    Ok((key, sp!(value.span => ident)))
                }).collect_with_recovery()
            })
        };
        macro_rules! pop_ident_map {
            ($name:literal) => { parse_idents($name, pop_map($name)) }
        }

        let enums = enum_maps.into_iter().map(|(enum_name, data)| {
            let enum_ident = Ident::new_user(&enum_name).map_err(|e| {
                emitter.emit(error!(
                    message("at enum {:?}: {}", enum_name, e),
                    primary(enum_name, "bad identifier"),
                ))
            })?;
            let new_data = parse_idents(&format!("{}{}{}", ENUM_SECT_START, enum_name, ENUM_SECT_END), data)?;
            Ok((sp!(enum_name.span => enum_ident), new_data))
        }).collect_with_recovery()?;

        let out = Mapfile {
            language,
            ins_names: pop_ident_map!("ins_names")?,
            ins_signatures: pop_map("ins_signatures"),
            ins_rets: pop_map("ins_rets"),
            gvar_names: pop_ident_map!("gvar_names")?,
            gvar_types: pop_map("gvar_types"),
            timeline_ins_names: pop_ident_map!("timeline_ins_names")?,
            timeline_ins_signatures: pop_map("timeline_ins_signatures"),
            ins_intrinsics: pop_map("ins_intrinsics"),
            difficulty_flags: pop_map("difficulty_flags"),
            enums,
            is_core_mapfile: false,
        };
        for (key, _) in maps {
            emitter.emit(warning!(
                message("unrecognized section in eclmap: {:?}", key),
                primary(key, "unrecognized section"),
            )).ignore();
        }

        Ok(out)
    }
}

const ENUM_SECT_START: &'static str = "enum(name=\"";
const ENUM_SECT_END: &'static str = "\")";

struct GatheredSeqmaps {
    maps: BTreeMap<Sp<String>, Vec<(i32, Sp<String>)>>,
    enum_maps: BTreeMap<Sp<String>, Vec<(i32, Sp<String>)>>,
}

fn gather_seqmaps(sections: Vec<SeqmapRawSection<'_>>) -> GatheredSeqmaps {
    let mut maps = BTreeMap::new();
    let mut enum_maps = BTreeMap::new();
    for section in sections {
        let cur_map = maps.entry(section.header.sp_map(ToString::to_string)).or_insert_with(Vec::new);
        for (number, value) in section.lines {
            cur_map.push((number.value, value.sp_map(ToString::to_string)));
        }
    }
    for key in maps.keys().cloned().collect::<Vec<_>>() {
        if key.starts_with(ENUM_SECT_START) && key.ends_with(ENUM_SECT_END) {
            let map = maps.remove(&key).unwrap();
            let enum_name = sp!(key.span => key[ENUM_SECT_START.len()..key.len()-ENUM_SECT_END.len()].to_string());
            enum_maps.insert(enum_name, map);
        }
    }
    GatheredSeqmaps { maps, enum_maps }
}

fn mapify_section(header: &str, section: Vec<(i32, Sp<String>)>, emitter: &impl Emitter) -> Result<BTreeMap<i32, Sp<String>>, ErrorReported> {
    let mut out = BTreeMap::new();
    for (number, value) in section {
        if let Some(previous) = out.insert(number, value.clone()) {
            return Err(emitter.emit(error!(
                message("in section '{}': duplicate key error for id {}", header, number),
                primary(value, "redefinition"),
                secondary(previous, "previous definition"),
            )));
        }
    }
    Ok(out)
}
