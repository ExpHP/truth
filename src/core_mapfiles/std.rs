use super::CoreSignatures;
use crate::Game::{self, *};

pub(super) fn core_signatures(game: Game) -> &'static CoreSignatures {
    match game {
        | Th06
        => STD_06,

        | Th07 | Th08 | Th09
        => STD_07_09,

        | Th095 | Th10 | Alcostg | Th11 | Th12 | Th125 | Th128
        | Th13 | Th14 | Th143 | Th15 | Th16 | Th165 | Th17 | Th18
        => STD_095_18
    }
}

static STD_06: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        (Th06, 0, Some("fff")),
        (Th06, 1, Some("Cff")),
        (Th06, 2, Some("fff")),
        (Th06, 3, Some("S__")),
        (Th06, 4, Some("S__")),
        (Th06, 5, Some("___")),
    ],
    var: &[],
};

static STD_07_09: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        (Th07, 0, Some("fff")),
        (Th07, 1, Some("Cff")),
        (Th07, 2, Some("S__")),
        (Th07, 3, Some("___")),
        (Th07, 4, Some("ot_")),
        (Th07, 5, Some("fff")),
        (Th07, 6, Some("SS_")),
        (Th07, 7, Some("fff")),
        (Th07, 8, Some("SS_")),
        (Th07, 9, Some("fff")),
        (Th07, 10, Some("SS_")),
        (Th07, 11, Some("f__")),
        (Th07, 12, Some("SS_")),
        (Th07, 13, Some("C__")),
        (Th07, 14, Some("fff")),
        (Th07, 15, Some("fff")),
        (Th07, 16, Some("fff")),
        (Th07, 17, Some("fff")),
        (Th07, 18, Some("S__")),
        (Th07, 19, Some("fff")),
        (Th07, 20, Some("fff")),
        (Th07, 21, Some("fff")),
        (Th07, 22, Some("fff")),
        (Th07, 23, Some("S__")),
        (Th07, 24, Some("fff")),
        (Th07, 25, Some("fff")),
        (Th07, 26, Some("fff")),
        (Th07, 27, Some("fff")),
        (Th07, 28, Some("S__")),
        (Th07, 29, Some("S__")),  // anm script
        (Th07, 30, Some("S__")),  // anm script
        (Th07, 31, Some("S__")),

        (Th08, 32, Some("fff")),
        (Th08, 33, Some("S__")),
        (Th08, 34, Some("S__")),  // anm script
    ],
    var: &[],
};

static STD_095_18: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        (Th095, 0, Some("")),
        (Th095, 1, Some("ot")),
        (Th095, 2, Some("fff")),
        (Th095, 3, Some("SSfff")),
        (Th095, 4, Some("fff")),
        (Th095, 5, Some("SSfff")),
        (Th095, 6, Some("fff")),
        (Th095, 7, Some("f")),
        (Th095, 8, Some("Cff")),
        (Th095, 9, Some("SSCff")),
        (Th095, 10, Some("SSfffffffff")),
        (Th095, 11, Some("SSfffffffff")),
        (Th095, 12, Some("S")),
        (Th095, 13, Some("C")),
        (Th095, 14, Some("SS")),  // SN
        // 15 appears to be a nop (i.e. it's not in the jumptable).
        //    However, no game ever uses it

        (Th11, 16, Some("S")),
        (Th11, 17, Some("S")),

        (Th12, 18, Some("SSfff")),

        (Th14, 14, Some("SSS")),  // SNS. 'layer' argument added
        (Th14, 19, Some("S")),
        (Th14, 20, Some("f")),

        (Th17, 21, Some("SSf")),
    ],
    var: &[],
};
