use super::CoreSignatures;
use crate::Game::{self, *};

pub(super) fn core_signatures(game: Game) -> &'static CoreSignatures {
    match game {
        | Th095 | Th125 | Th143 | Th165 | Th185
        => EMPTY, // These don't have .end files.

        | Th06 | Th07 | Th08 | Th09
        => EMPTY, // These are an entirely different format.

        | Th10 | Alcostg | Th11 | Th12 | Th128 | Th13
        | Th14 | Th15 | Th16 | Th17 | Th18
        => END_10_20,
    }
}

static EMPTY: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[],
    var: &[],
};

static END_10_20: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        (Th10, 0,  Some(("", None))),
        (Th10, 3,  Some(("z(bs=4;mask=0x77,7,16)", None))),
        (Th10, 4,  Some(("", None))),
        (Th10, 5,  Some(("S", None))),
        (Th10, 6,  Some(("S", None))),
        // FIXME: Add auto enums for these
        // (Th10, 7,  Some((r#"S(enum="AnmIndex")z(bs=4)"#, None))),
        // (Th10, 8,  Some((r#"S(enum="AnmSlotIndex")S(enum="AnmIndex")N"#, None))),
        (Th10, 7,  Some((r#"Sz(bs=4)"#, None))),
        (Th10, 8,  Some((r#"SSS"#, None))),
        (Th10, 9,  Some(("C", None))),
        (Th10, 10, Some(("z(bs=4)", None))),
        (Th10, 11, Some(("", None))),
        (Th10, 12, Some(("z(bs=4)", None))),
        (Th10, 13, Some(("S", None))),
        (Th10, 14, Some(("S", None))),
        // FIXME: Add auto enums for S(enum="AnmSlot")S(enum="AnmIndex")N
        //(Th10, 15, Some((r#"S(enum="AnmSlotIndex")S(enum="AnmIndex")N"#, None))),
        (Th10, 15, Some((r#"SSS"#, None))),
        (Th10, 16, Some((r#"SSS"#, None))),
        (Th10, 17, Some((r#"SSS"#, None))),

        // This happens eventually
        // (Th20, 3,  Some(("z(bs=4;mask=0x77,7,16;furibug)", None))),
        // (Th20, 9,  Some(("CC", None))),
    ],
    var: &[],
};
