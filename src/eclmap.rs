use std::collections::{BTreeMap};
use regex::Regex;
use lazy_static::lazy_static;

use crate::Game;
use crate::diagnostic::{RootEmitter, Emitter};
use crate::ident::Ident;
use crate::io::Fs;
use crate::error::{ErrorReported, GatherErrorIteratorExt};

pub struct Eclmap {
    pub magic: Magic,
    pub ins_names: BTreeMap<i32, Ident>,
    pub ins_signatures: BTreeMap<i32, String>,
    pub ins_rets: BTreeMap<i32, String>,
    pub gvar_names: BTreeMap<i32, Ident>,
    pub gvar_types: BTreeMap<i32, String>,
    pub timeline_ins_names: BTreeMap<i32, Ident>,
    pub timeline_ins_signatures: BTreeMap<i32, String>,
}

impl Eclmap {
    pub fn load(path: impl AsRef<std::path::Path>, game: Option<Game>, root_emitter: &RootEmitter) -> Result<Self, ErrorReported> {
        // canonicalize so paths in gamemaps can be interpreted relative to the gamemap path
        let path = path.as_ref();
        let emitter = root_emitter.while_reading(path);
        let fs = Fs::new(root_emitter);

        let path = fs.canonicalize(path).map_err(|e| root_emitter.emit(e))?;
        let text = fs.read_to_string(&path)?;

        let mut seqmap = parse_seqmap(&text, &emitter)?;
        if seqmap.magic == "!gamemap" {
            let game = match game {
                Some(game) => game,
                None => return Err(emitter.emit(error!("can't use gamemap because no game was supplied!")))
            };
            let base_dir = path.parent().expect("filename must have parent");
            seqmap = Self::resolve_gamemap(base_dir, seqmap, game, &emitter, root_emitter, &fs)?;
            // FIXME: following Self::from_seqmap should use emitter for resolved path but we
            //        don't have it in this function
        }
        Self::from_seqmap(seqmap, &emitter)
    }

    pub fn parse(text: &str, root_emitter: &RootEmitter) -> Result<Self, ErrorReported> {
        let emitter = root_emitter.get_chained("in mapfile");
        Self::from_seqmap(parse_seqmap(text, &emitter)?, &emitter)
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
                    .collect::<Vec<_>>()  // stop borrowing
            }).next()
    }

    fn resolve_gamemap(
        base_dir: &std::path::Path,
        mut seqmap: SeqMap,
        game: Game,
        gamemap_emitter: &impl Emitter,
        root_emitter: &RootEmitter,
        fs: &Fs,
    ) -> Result<SeqMap, ErrorReported> {
        let game_files = match seqmap.maps.remove("game_files") {
            Some(game_files) => game_files,
            None => return Err(gamemap_emitter.emit(error!("no !game_files section in gamemap"))),
        };
        for (key, _) in seqmap.maps {
            gamemap_emitter.emit(warning!("unrecognized section: {:?}", key)).ignore();
        }
        let rel_path = match game_files.get(&(game.as_number() as i32)) {
            Some(file) => file,
            None => return Err(gamemap_emitter.emit(error!("no entry for {}", game.as_str()))),
        };

        let final_path = base_dir.join(rel_path);
        let mapfile_emitter = root_emitter.while_reading(&final_path);
        let text = fs.read_to_string(&final_path)?;
        parse_seqmap(&text, &mapfile_emitter)
    }

    fn from_seqmap(seqmap: SeqMap, emitter: &impl Emitter) -> Result<Eclmap, ErrorReported> {
        let SeqMap { magic, mut maps } = seqmap;
        let magic = match &magic[..] {
            "!eclmap" => Magic::Eclmap,
            "!anmmap" => Magic::Anmmap,
            "!stdmap" => Magic::Stdmap,
            "!msgmap" => Magic::Stdmap,
            _ => return Err(emitter.emit(error!("bad magic: {:?}", magic))),
        };

        let mut pop_map = |section: &str| maps.remove(section).unwrap_or_else(BTreeMap::new);
        let parse_idents = |section: &str, m: BTreeMap<i32, String>| -> Result<BTreeMap<i32, Ident>, ErrorReported> {
            emitter.chain_with(|f| write!(f, "section !{}", section), |emitter| {
                m.into_iter().map(|(key, value)| {
                    let ident = value.parse::<Ident>().map_err(|e| emitter.emit(error!("at key {}: {}", key, e)))?;
                    Ok((key, ident))
                }).collect_with_recovery()
            })
        };
        macro_rules! pop_ident_map {
            ($name:literal) => { parse_idents($name, pop_map($name)) }
        }

        let out = Eclmap {
            magic,
            ins_names: pop_ident_map!("ins_names")?,
            ins_signatures: pop_map("ins_signatures"),
            ins_rets: pop_map("ins_rets"),
            gvar_names: pop_ident_map!("gvar_names")?,
            gvar_types: pop_map("gvar_types"),
            timeline_ins_names: pop_ident_map!("timeline_ins_names")?,
            timeline_ins_signatures: pop_map("timeline_ins_signatures"),
        };
        for (key, _) in maps {
            emitter.emit(warning!("unrecognized section in eclmap: {:?}", key)).ignore();
        }

        Ok(out)
    }
}

lazy_static! {
    static ref SEQMAP_START_RE: Regex = Regex::new(r"^!([_a-zA-Z][_a-zA-Z0-9]*)$").unwrap();
    static ref SEQMAP_ITEM_RE: Regex = Regex::new(r"^(-?[0-9]+)\s*(\S*)$").unwrap();
}

pub enum Magic {
    Anmmap,
    Eclmap,
    Stdmap,
}

struct SeqMap {
    magic: String,
    maps: BTreeMap<String, BTreeMap<i32, String>>,
}

fn parse_seqmap(text: &str, emitter: &impl Emitter) -> Result<SeqMap, ErrorReported> {
    let mut maps = BTreeMap::new();
    let mut cur_section = None;
    let mut cur_map = None;
    let mut lines = text.lines();

    macro_rules! bail {
        ($($args:tt)+) => { return Err(emitter.emit(error!($($args)+))) }
    }

    let magic = match lines.next() {
        Some(magic) => {
            if magic.chars().next() != Some('!') {
                bail!("this doesn't look like a seqmap file!");
            }
            magic.trim().to_string()
        },
        None => bail!("file is empty"),
    };

    for mut line in lines {
        if let Some(hash) = line.find("#") {
            line = &line[..hash];
        }
        line = line.trim();

        if line.is_empty() {
            continue;
        } else if line.starts_with("!") {
            let name = match SEQMAP_START_RE.captures(line) {
                Some(captures) => captures[1].to_string(),
                None => bail!("bad section start: {:?}", line),
            };
            cur_section = Some(name.clone());
            cur_map = Some(maps.entry(name).or_insert_with(BTreeMap::new));
        } else {
            match SEQMAP_ITEM_RE.captures(line) {
                None => bail!("parse error at line: {:?}", line),
                Some(captures) => {
                    let number = captures[1].parse().unwrap();
                    let value = captures[2].to_string();

                    let cur_map = match &mut cur_map {
                        None => bail!("missing section header"),
                        Some(cur_map) => cur_map,
                    };
                    if let Some(_) = cur_map.insert(number, value) {
                        let section_name = cur_section.as_ref().expect("can't be None if cur_map is Some");
                        bail!("in section '{}': duplicate key error for id {}", section_name, number);
                    }
                }
            }
        }
    }
    Ok(SeqMap { magic, maps })
}
