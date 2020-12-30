use std::collections::{HashMap};
use regex::Regex;
use lazy_static::lazy_static;
use thiserror::Error;
use crate::ident::Ident;

pub struct Eclmap {
    pub magic: Magic,
    pub ins_names: HashMap<i32, Ident>,
    pub ins_signatures: HashMap<i32, String>,
    pub ins_rets: HashMap<i32, String>,
    pub gvar_names: HashMap<i32, Ident>,
    pub gvar_types: HashMap<i32, String>,
    pub timeline_ins_names: HashMap<i32, Ident>,
    pub timeline_ins_signatures: HashMap<i32, String>,
}

#[derive(Debug, Error)]
pub enum Error {}

impl std::str::FromStr for Eclmap {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> { Ok(parse(s)) }
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

fn parse(text: &str) -> Eclmap {
    let mut maps = HashMap::new();
    let mut cur_map = None;
    let mut lines = text.lines();
    let magic = match lines.next() {
        Some(magic) => match magic.trim_end() {
            "!eclmap" => Magic::Eclmap,
            "!anmmap" => Magic::Anmmap,
            "!stdmap" => Magic::Stdmap,
            s => panic!("{:?}: bad magic", s), // FIXME return Error
        },
        None => panic!("empty file?"), // FIXME return Error
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
                None => panic!("parse error"), // FIXME return Error
            };
            cur_map = Some(maps.entry(name).or_insert_with(HashMap::new));
        } else {
            match SEQMAP_ITEM_RE.captures(line) {
                None => panic!("parse error"), // FIXME return Error
                Some(captures) => {
                    let number = captures[1].parse().unwrap();
                    let value = captures[2].to_string();
                    if let Some(_) = cur_map.as_mut().expect("missing section header").insert(number, value) { // FIXME return error
                        panic!("duplicate key error"); // FIXME return Error
                    }
                }
            }
        }
    }

    let mut pop_map = |s:&str| maps.remove(s).unwrap_or_else(HashMap::new);
    let parse_idents = |m:HashMap<i32, String>| -> HashMap<i32, Ident> {
        m.into_iter().map(|(key, s)| {
            let ident: Ident = s.parse().expect("invalid identifier"); // FIXME return Error
            if let Some(_) = ident.as_ins() {
                panic!("invalid identifier (clashes with instruction)"); // FIXME return Error
            }
            (key, ident)
        }).collect()
    };
    let out = Eclmap {
        magic,
        ins_names: parse_idents(pop_map("ins_names")),
        ins_signatures: pop_map("ins_signatures"),
        ins_rets: pop_map("ins_rets"),
        gvar_names: parse_idents(pop_map("gvar_names")),
        gvar_types: pop_map("gvar_types"),
        timeline_ins_names: parse_idents(pop_map("timeline_ins_names")),
        timeline_ins_signatures: pop_map("timeline_ins_signatures"),
    };
    if !maps.is_empty() {
        panic!("unrecognized sections: {:?}", maps.keys().collect::<Vec<_>>()); // FIXME return Error
    }

    out
}
