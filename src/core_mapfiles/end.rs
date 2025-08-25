use super::CoreSignatures;
use crate::Game::{self, *};

pub(super) fn core_signatures(game: Game) -> &'static CoreSignatures {
    match game {
        | Th095 | Alcostg | Th125 | Th143 | Th165 | Th185
        => EMPTY,

        | Th06 | Th07 | Th08 | Th09
        => END_06_09,

        | Th10 | Th11 | Th12 | Th128 | Th13
        | Th14 | Th15 | Th16 | Th17 | Th18 | Th19 | Th20
        => END_10_20,
    }
}

// Bunkachou titles have no true END scripts.
static EMPTY: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[],
    var: &[],
};

static END_06_09: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    // TODO
    ins: &[],
    var: &[],
};

static END_10_20: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        (Th10, 0, Some(("", None))),
        (Th10, 1, None),
        (Th10, 2, None),
        (Th10, 3, Some(("m(bs=4;mask=0x77,7,16)", None))),
        (Th10, 4, Some(("", None))),
        (Th10, 5, Some(("S", None))),
        (Th10, 6, Some(("S", None))),
        (Th10, 7, Some(("Sz(bs=4)", None))),
        (Th10, 8, Some(("SSN", None))),
        (Th10, 9, Some(("C", None))),
        (Th10, 10, Some(("z(bs=4)", None))),
        (Th10, 11, Some(("", None))),
        (Th10, 12, Some(("z(bs=4)", None))),
        (Th10, 13, Some(("S", None))),
        (Th10, 14, Some(("S", None))),
        (Th10, 15, Some(("SSN", None))),
        (Th10, 16, Some(("SSN", None))),
        (Th10, 17, Some(("SSN", None))),

        (Th20, 3, Some(("m(bs=4;mask=0x77,7,16;furibug)", None))),
        (Th20, 9, Some(("CC", None))),
    ],
    var: &[],
};
