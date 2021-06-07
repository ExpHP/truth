use super::CoreSignatures;
use crate::Game::{self, *};

pub fn core_signatures(game: Game) -> &'static CoreSignatures {
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
        (Th06, 0, Some("")),
        (Th06, 1, Some("ss")),
        (Th06, 2, Some("ss")),  // note: 2nd word is technically an anm sprite
        (Th06, 3, Some("ssz(bs=4)")),
        (Th06, 4, Some("S")),
        (Th06, 5, Some("ss")),
        (Th06, 6, Some("")),
        (Th06, 7, Some("S")),
        (Th06, 8, Some("ssz(bs=4)")),
        (Th06, 9, Some("S")),  // arg looks unused
        (Th06, 10, Some("")),
        (Th06, 11, Some("")),
        (Th06, 12, Some("")),
        (Th06, 13, Some("S")),

        (Th07, 14, Some("")),

        (Th08, 3, Some("ssm(bs=4;mask=0x77,0,0)")),
        (Th08, 8, Some("ssm(bs=4;mask=0x77,0,0)")),
        (Th08, 15, Some("SSSSS")),  // Snnnn
        (Th08, 16, Some("m(bs=4;mask=0x77,0,0)")),
        (Th08, 17, Some("SS")),  // Sn
        (Th08, 18, Some("S")),
        (Th08, 19, Some("m(bs=4;mask=0x77,0,0)")),
        (Th08, 20, Some("m(bs=4;mask=0x77,0,0)")),
        (Th08, 21, Some("S")),
        (Th08, 22, Some("")),

        (Th09, 3, Some("ssm(bs=4;mask=0x77,7,16)")),
        (Th09, 8, Some("")),
        (Th09, 15, Some("SSS")),
        (Th09, 16, Some("m(bs=4;mask=0x77,7,16)")),
        (Th09, 19, None),  // removed from jumptable
        (Th09, 20, None),
        (Th09, 21, None),
        (Th09, 22, None),
        (Th09, 23, Some("S")),
        (Th09, 24, Some("")),
        (Th09, 25, Some("")),
        (Th09, 26, Some("S")),
        // 27 is not in the jumptable; could be a nop, but it's never used
        (Th09, 28, Some("S")),
    ],
    var: &[],
};
static MSG_10_18: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        (Th10, 0, Some("")),
        (Th10, 1, Some("S")),  // arg is unused
        (Th10, 2, Some("S")),  // arg is unused
        (Th10, 3, Some("")),
        (Th10, 4, Some("")),
        (Th10, 5, Some("")),
        (Th10, 6, Some("")),
        (Th10, 7, Some("")),
        (Th10, 8, Some("")),
        (Th10, 9, Some("S")),
        (Th10, 10, Some("S")),
        (Th10, 11, Some("")),
        (Th10, 12, Some("S")),
        (Th10, 13, Some("S")),
        (Th10, 14, Some("m(bs=4;mask=0x77,7,16)")),
        (Th10, 15, Some("m(bs=4;mask=0x77,7,16)")),
        (Th10, 16, Some("m(bs=4;mask=0x77,7,16)")),
        (Th10, 17, Some("")),
        (Th10, 18, Some("")),
        (Th10, 19, Some("")),
        (Th10, 20, Some("")),
        (Th10, 21, Some("")),
        (Th10, 22, Some("")),
        (Th10, 23, Some("")),

        // th11 inserts one in the middle :(
        (Th11, 9, Some("")),   // new
        (Th11, 10, Some("S")), // 10...24 are TH10's 9...23
        (Th11, 11, Some("S")),
        (Th11, 12, Some("")),
        (Th11, 13, Some("S")),
        (Th11, 14, Some("S")),
        (Th11, 15, Some("m(bs=4;mask=0x77,7,16)")),
        (Th11, 16, Some("m(bs=4;mask=0x77,7,16)")),
        (Th11, 17, Some("m(bs=4;mask=0x77,7,16)")),
        (Th11, 18, Some("")),
        (Th11, 19, Some("")),
        (Th11, 20, Some("")),
        (Th11, 21, Some("")),
        (Th11, 22, Some("")),
        (Th11, 23, Some("")),
        (Th11, 24, Some("")),
        (Th11, 25, Some("S")), // new
        (Th11, 26, Some("")),  // new

        (Th12, 15, Some("m(bs=4;mask=0x77,7,16;furibug)")), // enable furibug
        (Th12, 16, Some("m(bs=4;mask=0x77,7,16;furibug)")),
        (Th12, 17, Some("m(bs=4;mask=0x77,7,16;furibug)")),
        (Th12, 27, Some("f")), // new

        (Th128, 28, Some("ff")),
        (Th128, 29, Some("S")),
        (Th128, 30, Some("")),

        (Th13, 31, Some("S")),

        (Th14, 5, Some("S")),
        (Th14, 8, Some("S")),
        (Th14, 14, Some("SS")),
        (Th14, 20, Some("S")),
        (Th14, 32, Some("S")),

        (Th143, 33, Some("S")),

        (Th15, 33, None), // removed

        (Th16, 33, Some("SS")), // replaced with something totally different (but unused)
        (Th16, 34, Some("SS")),
        (Th16, 35, Some("")),

        (Th165, 33, Some("S")), // 165 MSG is identical to 143
        (Th165, 34, None),
        (Th165, 35, None),

        (Th17, 33, Some("SS")), // 17 is like 16 again
        (Th17, 34, Some("SS")),
        (Th17, 35, Some("")),

        (Th18, 4, Some("S")),
        (Th18, 7, Some("S")),
        (Th18, 13, Some("SS")),
        (Th18, 36, Some("")),
    ],
    var: &[],
};
