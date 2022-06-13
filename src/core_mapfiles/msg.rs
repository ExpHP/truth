use super::CoreSignatures;
use crate::Game::{self, *};

pub(super) fn core_signatures(game: Game) -> &'static CoreSignatures {
    match game {
        | Th095 | Th125
        => EMPTY,

        | Th06 | Th07 | Th08 | Th09
        => MSG_06_09,

        | Th10 | Alcostg | Th11 | Th12 | Th128 | Th13
        | Th14 | Th143 | Th15 | Th16 | Th165 | Th17 | Th18
        => MSG_10_18,
    }
}

// Bunkachou titles have no true MSG scripts. (only "title" MSG files)
static EMPTY: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[],
    var: &[],
};

static MSG_06_09: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        (Th06, 0, Some(("", None))),
        (Th06, 1, Some(("ss", None))),
        (Th06, 2, Some(("ss", None))),  // note: 2nd word is technically an anm sprite
        (Th06, 3, Some(("ssz(bs=4)", None))),
        (Th06, 4, Some(("S", None))),
        (Th06, 5, Some(("ss", None))),
        (Th06, 6, Some(("", None))),
        (Th06, 7, Some(("S", None))),
        (Th06, 8, Some(("ssz(bs=4)", None))),
        (Th06, 9, Some(("S", None))),  // arg looks unused
        (Th06, 10, Some(("", None))),
        (Th06, 11, Some(("", None))),
        (Th06, 12, Some(("", None))),
        (Th06, 13, Some(("S", None))),

        (Th07, 14, Some(("", None))),

        (Th08, 3, Some(("ssm(bs=4;mask=0x77,0,0)", None))),
        (Th08, 8, Some(("ssm(bs=4;mask=0x77,0,0)", None))),
        (Th08, 15, Some(("SSSSS", None))),  // Snnnn
        (Th08, 16, Some(("m(bs=4;mask=0x77,0,0)", None))),
        (Th08, 17, Some(("SS", None))),  // Sn
        (Th08, 18, Some(("S", None))),
        (Th08, 19, Some(("m(bs=4;mask=0x77,0,0)", None))),
        (Th08, 20, Some(("m(bs=4;mask=0x77,0,0)", None))),
        (Th08, 21, Some(("S", None))),
        (Th08, 22, Some(("", None))),

        (Th09, 3, Some(("ssm(bs=4;mask=0x77,7,16)", None))),
        (Th09, 8, Some(("", None))),
        (Th09, 15, Some(("SSS", None))),
        (Th09, 16, Some(("m(bs=4;mask=0x77,7,16)", None))),
        (Th09, 19, None),  // removed from jumptable
        (Th09, 20, None),
        (Th09, 21, None),
        (Th09, 22, None),
        (Th09, 23, Some(("S", None))),
        (Th09, 24, Some(("", None))),
        (Th09, 25, Some(("", None))),
        (Th09, 26, Some(("S", None))),
        // 27 is not in the jumptable; could be a nop, but it's never used
        (Th09, 28, Some(("S", None))),
    ],
    var: &[],
};
static MSG_10_18: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        (Th10, 0, Some(("", None))),
        (Th10, 1, Some(("S", None))),  // arg is unused
        (Th10, 2, Some(("S", None))),  // arg is unused
        (Th10, 3, Some(("", None))),
        (Th10, 4, Some(("", None))),
        (Th10, 5, Some(("", None))),
        (Th10, 6, Some(("", None))),
        (Th10, 7, Some(("", None))),
        (Th10, 8, Some(("", None))),
        (Th10, 9, Some(("S", None))),
        (Th10, 10, Some(("S", None))),
        (Th10, 11, Some(("", None))),
        (Th10, 12, Some(("S", None))),
        (Th10, 13, Some(("S", None))),
        (Th10, 14, Some(("m(bs=4;mask=0x77,7,16)", None))),
        (Th10, 15, Some(("m(bs=4;mask=0x77,7,16)", None))),
        (Th10, 16, Some(("m(bs=4;mask=0x77,7,16)", None))),
        (Th10, 17, Some(("", None))),
        (Th10, 18, Some(("", None))),
        (Th10, 19, Some(("", None))),
        (Th10, 20, Some(("", None))),
        (Th10, 21, Some(("", None))),
        (Th10, 22, Some(("", None))),
        (Th10, 23, Some(("", None))),

        // th11 inserts one in the middle :(
        (Th11, 9, Some(("", None))),   // new
        (Th11, 10, Some(("S", None))), // 10...24 are TH10's 9...23
        (Th11, 11, Some(("S", None))),
        (Th11, 12, Some(("", None))),
        (Th11, 13, Some(("S", None))),
        (Th11, 14, Some(("S", None))),
        (Th11, 15, Some(("m(bs=4;mask=0x77,7,16)", None))),
        (Th11, 16, Some(("m(bs=4;mask=0x77,7,16)", None))),
        (Th11, 17, Some(("m(bs=4;mask=0x77,7,16)", None))),
        (Th11, 18, Some(("", None))),
        (Th11, 19, Some(("", None))),
        (Th11, 20, Some(("", None))),
        (Th11, 21, Some(("", None))),
        (Th11, 22, Some(("", None))),
        (Th11, 23, Some(("", None))),
        (Th11, 24, Some(("", None))),
        (Th11, 25, Some(("S", None))), // new
        (Th11, 26, Some(("", None))),  // new

        (Th12, 15, Some(("m(bs=4;mask=0x77,7,16;furibug)", None))), // enable furibug
        (Th12, 16, Some(("m(bs=4;mask=0x77,7,16;furibug)", None))),
        (Th12, 17, Some(("m(bs=4;mask=0x77,7,16;furibug)", None))),
        (Th12, 27, Some(("f", None))), // new

        (Th128, 28, Some(("ff", None))),
        (Th128, 29, Some(("S", None))),
        (Th128, 30, Some(("", None))),

        (Th13, 31, Some(("S", None))),

        (Th14, 5, Some(("S", None))),
        (Th14, 8, Some(("S", None))),
        (Th14, 14, Some(("SS", None))),
        (Th14, 20, Some(("S", None))),
        (Th14, 32, Some(("S", None))),

        (Th143, 33, Some(("S", None))),

        (Th15, 33, None), // removed

        (Th16, 33, Some(("SS", None))), // replaced with something totally different (but unused)
        (Th16, 34, Some(("SS", None))),
        (Th16, 35, Some(("", None))),

        (Th165, 33, Some(("S", None))), // 165 MSG is identical to 143
        (Th165, 34, None),
        (Th165, 35, None),

        (Th17, 33, Some(("SS", None))), // 17 is like 16 again
        (Th17, 34, Some(("SS", None))),
        (Th17, 35, Some(("", None))),

        (Th18, 4, Some(("S", None))),
        (Th18, 7, Some(("S", None))),
        (Th18, 13, Some(("SS", None))),
        (Th18, 36, Some(("", None))),
    ],
    var: &[],
};
