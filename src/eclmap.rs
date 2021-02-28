use std::collections::{BTreeMap};
use regex::Regex;
use lazy_static::lazy_static;
use anyhow::{bail, Context};
use crate::Game;
use crate::ident::Ident;
use crate::error::SimpleError;

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
    pub fn load(path: impl AsRef<std::path::Path>, game: Option<Game>) -> Result<Self, SimpleError> {
        // canonicalize so paths in gamemaps can be interpreted relative to the gamemap path
        let path = path.as_ref().canonicalize().with_context(|| format!("while resolving '{}'", path.as_ref().display()))?;
        let text = std::fs::read_to_string(&path).with_context(|| format!("while reading '{}'", path.display()))?;

        crate::error::group_anyhow(|| {
            let mut seqmap = parse_seqmap(&text)?;
            if seqmap.magic == "!gamemap" {
                let game = match game {
                    Some(game) => game,
                    None => bail!("can't use gamemap because no game was supplied!")
                };
                let base_dir = path.parent().expect("filename must have parent");
                seqmap = Self::resolve_gamemap(base_dir, seqmap, game)?;
            }
            Self::from_seqmap(seqmap)
        }).with_context(|| format!("while parsing '{}'", path.display()))
    }

    pub fn parse(text: &str) -> Result<Self, SimpleError> {
        Self::from_seqmap(parse_seqmap(text)?)
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

    fn resolve_gamemap(base_dir: &std::path::Path, mut seqmap: SeqMap, game: Game) -> Result<SeqMap, SimpleError> {
        let game_files = match seqmap.maps.remove("game_files") {
            Some(game_files) => game_files,
            None => bail!("no !game_files section in gamemap")
        };
        for (key, _) in seqmap.maps {
            fast_warning!("unrecognized section in gamemap: {:?}", key);
        }
        let rel_path = match game_files.get(&(game.as_number() as i32)) {
            Some(file) => file,
            None => bail!("no entry in gamemap for {}", game.as_str()),
        };
        let final_path = base_dir.join(rel_path);

        let text = std::fs::read_to_string(&final_path).with_context(|| format!("while reading '{}'", final_path.display()))?;
        parse_seqmap(&text)
    }

    fn from_seqmap(seqmap: SeqMap) -> Result<Eclmap, SimpleError> {
        let SeqMap { magic, mut maps } = seqmap;
        let magic = match &magic[..] {
            "!eclmap" => Magic::Eclmap,
            "!anmmap" => Magic::Anmmap,
            "!stdmap" => Magic::Stdmap,
            "!msgmap" => Magic::Stdmap,
            _ => bail!("{:?}: bad magic", magic),
        };

        let mut pop_map = |s:&str| maps.remove(s).unwrap_or_else(BTreeMap::new);
        let parse_idents = |m:BTreeMap<i32, String>| -> Result<BTreeMap<i32, Ident>, SimpleError> {
            m.into_iter().map(|(key, s)| {
                Ok((key, s.parse::<Ident>()?))
            }).collect()
        };
        let out = Eclmap {
            magic,
            ins_names: parse_idents(pop_map("ins_names"))?,
            ins_signatures: pop_map("ins_signatures"),
            ins_rets: pop_map("ins_rets"),
            gvar_names: parse_idents(pop_map("gvar_names"))?,
            gvar_types: pop_map("gvar_types"),
            timeline_ins_names: parse_idents(pop_map("timeline_ins_names"))?,
            timeline_ins_signatures: pop_map("timeline_ins_signatures"),
        };
        for (key, _) in maps {
            fast_warning!("unrecognized section in eclmap: {:?}", key);
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

fn parse_seqmap(text: &str) -> Result<SeqMap, SimpleError> {
    let mut maps = BTreeMap::new();
    let mut cur_section = None;
    let mut cur_map = None;
    let mut lines = text.lines();
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
                        bail!("duplicate key error for id {} in section '{}'", number, section_name);
                    }
                }
            }
        }
    }
    Ok(SeqMap { magic, maps })
}
