use std::fmt;

use crate::diagnostic::Diagnostic;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Game {
    Th06, Th07, Th08, Th09, Th095, Th10, Alcostg, Th11, Th12,
    Th125, Th128, Th13, Th14, Th143, Th15, Th16, Th165, Th17, Th18,
    Th185, Th19, Th20
}
macro_rules! max_game_str { () => { "th20" }; }

impl std::str::FromStr for Game {
    type Err = Diagnostic;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s == "alcostg" {
            return Ok(Game::Alcostg);
        }

        let err_suffix = concat!("(valid games are th06 to ", max_game_str!(), ", or alcostg.  Point titles are written as e.g. th095)");
        let invalid_game = || error!("game not invalid: {} {}", s, err_suffix);
        let unsupported_pc98 = || error!("game not supported (PC-98): {} {}", s, err_suffix);
        let unsupported_fighter = || error!("game not supported (fighter): {} {}", s, err_suffix);
        let unknown_game = || error!("unknown game: {} {}", s, err_suffix);

        let s = s.strip_prefix("th").unwrap_or(s);
        match s.parse::<u32>().map_err(|_| invalid_game())? {
            1 | 2 | 3 | 4 | 5 => Err(unsupported_pc98()),
            75 | 105 | 135 | 145 | 155 | 175 => Err(unsupported_fighter()),
            6 => Ok(Game::Th06),
            7 => Ok(Game::Th07),
            8 => Ok(Game::Th08),
            9 => Ok(Game::Th09),
            95 => Ok(Game::Th095),
            10 => Ok(Game::Th10),
            103 => Ok(Game::Alcostg),
            11 => Ok(Game::Th11),
            12 => Ok(Game::Th12),
            125 => Ok(Game::Th125),
            128 => Ok(Game::Th128),
            13 => Ok(Game::Th13),
            14 => Ok(Game::Th14),
            143 => Ok(Game::Th143),
            15 => Ok(Game::Th15),
            16 => Ok(Game::Th16),
            165 => Ok(Game::Th165),
            17 => Ok(Game::Th17),
            18 => Ok(Game::Th18),
            185 => Ok(Game::Th185),
            19 => Ok(Game::Th19),
            20 => Ok(Game::Th20),
            _ => Err(unknown_game()),
        }
    }
}

impl Game {
    pub fn abbr(self) -> &'static str {
        match self {
            Game::Alcostg => "AlcoSTG",
            Game::Th06 => "EoSD",
            Game::Th07 => "PCB",
            Game::Th08 => "IN",
            Game::Th09 => "PoFV",
            Game::Th095 => "StB",
            Game::Th10 => "MoF",
            Game::Th11 => "SA",
            Game::Th12 => "UFO",
            Game::Th125 => "DS",
            Game::Th128 => "GFW",
            Game::Th13 => "TD",
            Game::Th14 => "DDC",
            Game::Th143 => "ISC",
            Game::Th15 => "LoLK",
            Game::Th16 => "HSiFS",
            Game::Th165 => "VD",
            Game::Th17 => "WBaWC",
            Game::Th18 => "UM",
            Game::Th185 => "HBM",
            Game::Th19 => "UDoALG",
            Game::Th20 => "FW",
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Game::Alcostg => "alcostg",
            Game::Th06 => "th06",
            Game::Th07 => "th07",
            Game::Th08 => "th08",
            Game::Th09 => "th09",
            Game::Th095 => "th095",
            Game::Th10 => "th10",
            Game::Th11 => "th11",
            Game::Th12 => "th12",
            Game::Th125 => "th125",
            Game::Th128 => "th128",
            Game::Th13 => "th13",
            Game::Th14 => "th14",
            Game::Th143 => "th143",
            Game::Th15 => "th15",
            Game::Th16 => "th16",
            Game::Th165 => "th165",
            Game::Th17 => "th17",
            Game::Th18 => "th18",
            Game::Th185 => "th185",
            Game::Th19 => "th19",
            Game::Th20 => "th20",
        }
    }

    pub fn as_number(self) -> u32 {
        match self {
            Game::Alcostg => 103,
            Game::Th06 => 6,
            Game::Th07 => 7,
            Game::Th08 => 8,
            Game::Th09 => 9,
            Game::Th095 => 95,
            Game::Th10 => 10,
            Game::Th11 => 11,
            Game::Th12 => 12,
            Game::Th125 => 125,
            Game::Th128 => 128,
            Game::Th13 => 13,
            Game::Th14 => 14,
            Game::Th143 => 143,
            Game::Th15 => 15,
            Game::Th16 => 16,
            Game::Th165 => 165,
            Game::Th17 => 17,
            Game::Th18 => 18,
            Game::Th185 => 185,
            Game::Th19 => 19,
            Game::Th20 => 20,
        }
    }
}

impl fmt::Display for Game {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

/// Indicates a distinct instruction set that may appear in a game.
///
/// Used as part of the key for e.g. opcode signatures.
///
/// This does not correspond 1-1 with truth's filetypes.  For instance, [`Self::Ecl`] and [`Self::Timeline`]
/// are two distinct instruction sets that both appear in `.ecl` files, while "mission" files (`mission.msg`)
/// do not have any instruction sets at all.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[derive(enum_map::Enum)]
pub enum LanguageKey {
    Ecl, Anm, Msg, End, Std, Timeline,
    Dummy, // used in unit tests
}

impl LanguageKey {
    /// A human-readable name for the language, in title case. (`"ECL"`, `"Stage MSG"`...)
    pub fn descr(&self) -> &'static str {
        match self {
            Self::Ecl => "ECL",
            Self::Timeline => "ECL Timeline",
            Self::Anm => "ANM",
            Self::Std => "STD",
            Self::Msg => "Stage MSG",
            Self::End => "Ending MSG",
            Self::Dummy => "Dummy Test Language",
        }
    }
}
