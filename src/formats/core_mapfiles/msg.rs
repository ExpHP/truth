use super::CoreSignatures;
use crate::Game::{self, *};

pub fn core_signatures(game: Game) -> &'static CoreSignatures {
    match game {
        | Th095 | Th125
        => EMPTY,

        | Th06 | Th07 | Th08 | Th09 | Th10 | Alcostg | Th11 | Th12
        | Th128 | Th13 | Th14 | Th143 | Th15 | Th16 | Th165 | Th17
        => MSG,
    }
}

// Bunkachou titles have no true MSG scripts. (only "title" MSG files)
static EMPTY: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[],
    var: &[],
};

static MSG: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        (Th06, 0, ""),
        (Th06, 1, "ss"),
        (Th06, 2, "ss"),  // note: 2nd word is technically an anm sprite
        (Th06, 3, "ssz"),
        (Th06, 4, "S"),
        (Th06, 5, "ss"),
        (Th06, 6, ""),
        (Th06, 7, "S"),
        (Th06, 8, "ssz"),
        (Th06, 9, "S"),  // arg looks unused
        (Th06, 10, ""),
        (Th06, 11, ""),
        (Th06, 12, ""),
        (Th06, 13, "S"),

        (Th07, 14, ""),

        (Th08, 3, "ssm"),
        (Th08, 8, "ssm"),
        (Th08, 15, "SSSSS"),  // SnSSS
        (Th08, 16, "m"),
        (Th08, 17, "SS"),  // Sn
        (Th08, 18, "S"),
        (Th08, 19, "m"),
        (Th08, 20, "m"),
        (Th08, 21, "S"),
        (Th08, 22, ""),
    ],
    var: &[],
};
