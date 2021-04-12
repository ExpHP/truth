use super::CoreSignatures;
use crate::Game::{self, *};

pub fn core_signatures(game: Game) -> &'static CoreSignatures {
    match game {
        | Th06
        => STD_06,

        | Th07 | Th08 | Th09
        => STD_07_09,

        | Th095 | Th10 | Alcostg | Th11 | Th12 | Th125 | Th128
        | Th13 | Th14 | Th143 | Th15 | Th16 | Th165 | Th17
        => STD_095_17
    }
}

static STD_06: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        (Th06, 0, "fff"),
        (Th06, 1, "Cff"),
        (Th06, 2, "fff"),
        (Th06, 3, "S__"),
        (Th06, 4, "S__"),
        (Th06, 5, "___"),
    ],
    var: &[],
};

static STD_07_09: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        (Th07, 0, "fff"),
        (Th07, 1, "Cff"),
        (Th07, 2, "S__"),
        (Th07, 3, "___"),
        (Th07, 4, "ot_"),
        (Th07, 5, "fff"),
        (Th07, 6, "SS_"),
        (Th07, 7, "fff"),
        (Th07, 8, "SS_"),
        (Th07, 9, "fff"),
        (Th07, 10, "SS_"),
        (Th07, 11, "f__"),
        (Th07, 12, "SS_"),
        (Th07, 13, "C__"),
        (Th07, 14, "fff"),
        (Th07, 15, "fff"),
        (Th07, 16, "fff"),
        (Th07, 17, "fff"),
        (Th07, 18, "S__"),
        (Th07, 19, "fff"),
        (Th07, 20, "fff"),
        (Th07, 21, "fff"),
        (Th07, 22, "fff"),
        (Th07, 23, "S__"),
        (Th07, 24, "fff"),
        (Th07, 25, "fff"),
        (Th07, 26, "fff"),
        (Th07, 27, "fff"),
        (Th07, 28, "S__"),
        (Th07, 29, "S__"),  // anm script
        (Th07, 30, "S__"),  // anm script
        (Th07, 31, "S__"),

        (Th08, 32, "fff"),
        (Th08, 33, "S__"),
        (Th08, 34, "S__"),  // anm script
    ],
    var: &[],
};

static STD_095_17: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        (Th095, 0, ""),
        (Th095, 1, "ot"),
        (Th095, 2, "fff"),
        (Th095, 3, "SSfff"),
        (Th095, 4, "fff"),
        (Th095, 5, "SSfff"),
        (Th095, 6, "fff"),
        (Th095, 7, "f"),
        (Th095, 8, "Cff"),
        (Th095, 9, "SSCff"),
        (Th095, 10, "SSfffffffff"),
        (Th095, 11, "SSfffffffff"),
        (Th095, 12, "S"),
        (Th095, 13, "C"),
        (Th095, 14, "SS"),  // SN
        // 15 appears to be a nop (i.e. it's not in the jumptable).
        //    However, no game ever uses it

        (Th11, 16, "S"),
        (Th11, 17, "S"),

        (Th12, 18, "SSfff"),

        (Th14, 14, "SSS"),  // SNS. 'layer' argument added
        (Th14, 19, "S"),
        (Th14, 20, "f"),

        (Th17, 21, "SSf"),
    ],
    var: &[],
};
