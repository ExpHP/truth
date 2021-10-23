use std::collections::{BTreeMap};

use crate::pos::{Sp, FileId};
use crate::game::{Game, InstrLanguage};
use crate::diagnostic::{RootEmitter, Emitter};
use crate::ident::Ident;
use crate::io::Fs;
use crate::parse::seqmap::{SeqmapRaw, SeqmapRawSection};
use crate::error::{ErrorReported, GatherErrorIteratorExt};

/// FIXME: Rename to Mapfile, how have I not done this already?!  - Exp
#[derive(Debug)]
pub struct Eclmap {
    pub language: InstrLanguage,
    pub ins_names: BTreeMap<i32, Sp<Ident>>,
    pub ins_signatures: BTreeMap<i32, Sp<String>>,
    pub ins_rets: BTreeMap<i32, Sp<String>>,
    pub gvar_names: BTreeMap<i32, Sp<Ident>>,
    pub gvar_types: BTreeMap<i32, Sp<String>>,
    /// For historic reasons, [`InstrLanguage::Timeline`] has dedicated sections.
    /// When these are seen in a file, they will always define things for timelines
    /// instead of [`Self::language`].
    pub timeline_ins_names: BTreeMap<i32, Sp<Ident>>,
    pub timeline_ins_signatures: BTreeMap<i32, Sp<String>>,
}

impl Eclmap {
    pub fn new(language: InstrLanguage) -> Self {
        Eclmap {
            language,
            ins_names: Default::default(),
            ins_signatures: Default::default(),
            ins_rets: Default::default(),
            gvar_names: Default::default(),
            gvar_types: Default::default(),
            /// Legacy `timeline` sections. These will always apply to [`InstrLanguage::Timeline`] instead of [`Self::language`].
            timeline_ins_names: Default::default(),
            timeline_ins_signatures: Default::default(),
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

        let (file_id, file_contents) = read_file(&path)?;
        let mut seqmap = SeqmapRaw::parse(file_id, &file_contents, emitter)?;
        if seqmap.magic == "!gamemap" {
            let game = match game {
                Some(game) => game,
                None => return Err(emitter.emit(error!("can't use gamemap because no game was supplied!")))
            };
            let base_dir = path.parent().expect("filename must have parent");
            let game_specific_map_path = Self::resolve_gamemap(base_dir, seqmap, game, emitter)?;
            let (file_id, file_contents) = read_file(&game_specific_map_path)?;
            seqmap = SeqmapRaw::parse(file_id, &file_contents, emitter)?;
            Self::from_seqmap(seqmap, emitter)
        } else {
            // had to put this in an else to satisfy borrow checker _/o\_
            // hope it doesn't code gen twice?
            Self::from_seqmap(seqmap, emitter)
        }
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

    fn resolve_gamemap(
        base_dir: &std::path::Path,
        seqmap: SeqmapRaw,
        game: Game,
        emitter: &impl Emitter,
    ) -> Result<std::path::PathBuf, ErrorReported> {
        let SeqmapRaw { magic, sections } = seqmap;
        let mut maps = gather_seqmaps(sections, emitter)?;

        let game_files = match maps.remove(&"game_files".to_string()) {
            Some(game_files) => game_files,
            None => return Err(emitter.emit(error!(
                message("no !game_files section in gamemap"),
                primary(magic, "gamemap without !game_files section"),
            ))),
        };
        for (key, _) in maps {
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

    pub fn from_seqmap(seqmap: SeqmapRaw, emitter: &impl Emitter) -> Result<Eclmap, ErrorReported> {
        let SeqmapRaw { magic, sections } = seqmap;

        let mut maps = gather_seqmaps(sections, emitter)?;

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
            "!eclmap" => InstrLanguage::Ecl,
            "!anmmap" => InstrLanguage::Anm,
            "!stdmap" => InstrLanguage::Std,
            "!msgmap" => InstrLanguage::Msg,
            _ => return Err(emitter.emit(error!(
                message("bad magic: {:?}", magic),
                primary(magic, "bad magic"),
            ))),
        };

        let mut pop_map = |section: &str| maps.remove(&section.to_string()).unwrap_or_else(BTreeMap::new);
        let parse_idents = |section: &str, m: BTreeMap<i32, Sp<String>>| -> Result<BTreeMap<i32, Sp<Ident>>, ErrorReported> {
            emitter.chain_with(|f| write!(f, "section !{}", section), |emitter| {
                m.into_iter().map(|(key, value)| {
                    let ident = value.parse::<Ident>().map_err(|e| emitter.emit(error!(
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

        let out = Eclmap {
            language,
            ins_names: pop_ident_map!("ins_names")?,
            ins_signatures: pop_map("ins_signatures"),
            ins_rets: pop_map("ins_rets"),
            gvar_names: pop_ident_map!("gvar_names")?,
            gvar_types: pop_map("gvar_types"),
            timeline_ins_names: pop_ident_map!("timeline_ins_names")?,
            timeline_ins_signatures: pop_map("timeline_ins_signatures"),
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

type GatheredSeqmaps = BTreeMap<Sp<String>, BTreeMap<i32, Sp<String>>>;

fn gather_seqmaps(sections: Vec<SeqmapRawSection<'_>>, emitter: &impl Emitter) -> Result<GatheredSeqmaps, ErrorReported> {
    let mut maps = BTreeMap::new();
    for section in sections {
        let cur_map = maps.entry(section.header.sp_map(ToString::to_string)).or_insert_with(BTreeMap::new);

        for (number, value) in section.lines {
            if let Some(previous) = cur_map.insert(number.value, value.sp_map(ToString::to_string)) {
                // FIXME: Technically we should allow this and keep both as aliases.
                //        https://github.com/ExpHP/truth/issues/49
                return Err(emitter.emit(error!(
                    message("in section '{}': duplicate key error for id {}", section.header, number),
                    primary(value, "redefinition"),
                    secondary(previous, "previous definition"),
                )));
            }
        }
    }
    Ok(maps)
}
