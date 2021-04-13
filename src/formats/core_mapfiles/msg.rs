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
        (Th06, 3, "ssz(bs=4)"),
        (Th06, 4, "S"),
        (Th06, 5, "ss"),
        (Th06, 6, ""),
        (Th06, 7, "S"),
        (Th06, 8, "ssz(bs=4)"),
        (Th06, 9, "S"),  // arg looks unused
        (Th06, 10, ""),
        (Th06, 11, ""),
        (Th06, 12, ""),
        (Th06, 13, "S"),

        (Th07, 14, ""),

        (Th08, 3, "ssm(bs=4;mask=0x77,0,0)"),
        (Th08, 8, "ssm(bs=4;mask=0x77,0,0)"),
        (Th08, 15, "SSSSS"),  // SnSSS
        (Th08, 16, "m(bs=4;mask=0x77,0,0)"),
        (Th08, 17, "SS"),  // Sn
        (Th08, 18, "S"),
        (Th08, 19, "m(bs=4;mask=0x77,0,0)"),
        (Th08, 20, "m(bs=4;mask=0x77,0,0)"),
        (Th08, 21, "S"),
        (Th08, 22, ""),

        // =========================================
        // FIXME: Everything beyond this point is copied from thtk,
        //        which has a track record for being wrong about unused instructions
        //        and arguments that are always zero in vanilla files.
        //
        //        I'll reverse MSG in these games at some point...  - ExpHP

        (Th09, 3, "ssm(bs=4;mask=0x77,7,16)"),
        (Th09, 8, ""),
        (Th09, 15, "SSS"),
        (Th09, 16, "m(bs=4;mask=0x77,7,16)"),
        (Th09, 18, "m(bs=4;mask=0x77,7,16)"),
        (Th09, 19, "m(bs=4;mask=0x77,7,16)"),
        (Th09, 23, "S"),
        (Th09, 24, ""),
        (Th09, 25, ""),
        (Th09, 28, "S"),

        // (FIXME: this many changed signatures looks suspicious, don't it?
        //         This is probably a rewrite of the format, and should be broken
        //         into a new CoreSignatures if that's the case)
        (Th10, 1, "S"),
        (Th10, 2, "S"),
        (Th10, 3, ""),
        (Th10, 4, ""),
        (Th10, 5, ""),
        (Th10, 7, ""),
        (Th10, 10, "S"),
        (Th10, 12, "S"),
        (Th10, 14, "S"),
        (Th10, 17, "m(bs=4;mask=0x77,7,16)"),
        (Th10, 18, ""),
        (Th10, 19, ""),
        (Th10, 20, ""),
        (Th10, 21, ""),
        (Th10, 22, ""),
        (Th10, 23, ""),
        (Th10, 25, "S"),

        (Th11, 9, ""),
        (Th11, 10, "S"),
        (Th11, 11, "S"),
        (Th11, 12, ""),

        (Th12, 27, "f"),

        (Th128, 28, "ff"),
        (Th128, 29, "S"),
        (Th128, 30, ""),

        (Th13, 31, "S"),

        (Th14, 5, "S"),
        (Th14, 8, "S"),
        (Th14, 14, "SS"),
        (Th14, 20, "S"),
        (Th14, 32, "S"),

        (Th143, 33, "S"),

        (Th16, 34, "SS"),
        (Th16, 35, ""),
        // =========================================
    ],
    var: &[],
};
