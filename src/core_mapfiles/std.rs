use super::CoreSignatures;
use crate::Game::{self, *};
use crate::llir::IntrinsicInstrKind as IKind;

pub(super) fn core_signatures(game: Game) -> &'static CoreSignatures {
    match game {
        | Th06
        => STD_06,

        | Th07 | Th08 | Th09
        => STD_07_09,

        | Th095 | Th10 | Alcostg | Th11 | Th12 | Th125 | Th128
        | Th13 | Th14 | Th143 | Th15 | Th16 | Th165 | Th17 | Th18 | Th185 | Th19 | Th20
        => STD_095_20
    }
}

static STD_06: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        (Th06, 0, Some(("fff", None))),
        (Th06, 1, Some(("Cff", None))),
        (Th06, 2, Some(("fff", None))),
        (Th06, 3, Some(("S__", None))),
        (Th06, 4, Some(("S__", None))),
        (Th06, 5, Some(("___", None))),
    ],
    var: &[],
};

static STD_07_09: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        (Th07, 0, Some(("fff", None))),
        (Th07, 1, Some(("Cff", None))),
        (Th07, 2, Some(("S__", None))),
        (Th07, 3, Some(("___", None))),
        (Th07, 4, Some(("ot_", Some(IKind::Jmp)))),
        (Th07, 5, Some(("fff", None))),
        (Th07, 6, Some(("SS_", None))),
        (Th07, 7, Some(("fff", None))),
        (Th07, 8, Some(("SS_", None))),
        (Th07, 9, Some(("fff", None))),
        (Th07, 10, Some(("SS_", None))),
        (Th07, 11, Some(("f__", None))),
        (Th07, 12, Some(("SS_", None))),
        (Th07, 13, Some(("C__", None))),
        (Th07, 14, Some(("fff", None))),
        (Th07, 15, Some(("fff", None))),
        (Th07, 16, Some(("fff", None))),
        (Th07, 17, Some(("fff", None))),
        (Th07, 18, Some(("S__", None))),
        (Th07, 19, Some(("fff", None))),
        (Th07, 20, Some(("fff", None))),
        (Th07, 21, Some(("fff", None))),
        (Th07, 22, Some(("fff", None))),
        (Th07, 23, Some(("S__", None))),
        (Th07, 24, Some(("fff", None))),
        (Th07, 25, Some(("fff", None))),
        (Th07, 26, Some(("fff", None))),
        (Th07, 27, Some(("fff", None))),
        (Th07, 28, Some(("S__", None))),
        (Th07, 29, Some(("N__", None))),
        (Th07, 30, Some(("N__", None))),
        (Th07, 31, Some(("S__", Some(IKind::InterruptLabel)))),

        (Th08, 32, Some(("fff", None))),
        (Th08, 33, Some(("b---__", None))),
        (Th08, 34, Some(("N__", None))),
    ],
    var: &[],
};

static STD_095_20: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        (Th095, 0, Some(("", None))),
        (Th095, 1, Some(("ot", Some(IKind::Jmp)))),
        (Th095, 2, Some(("fff", None))),
        (Th095, 3, Some(("Sbb--fff", None))),
        (Th095, 4, Some(("fff", None))),
        (Th095, 5, Some(("Sbb--fff", None))),
        (Th095, 6, Some(("fff", None))),
        (Th095, 7, Some(("f", None))),
        (Th095, 8, Some(("Cff", None))),
        (Th095, 9, Some(("Sbb--Cff", None))),
        (Th095, 10, Some(("SUfffffffff", None))), // Technically S_fffffffff since MoF
        (Th095, 11, Some(("SUfffffffff", None))), // Technically S_fffffffff since MoF
        (Th095, 12, Some(("b---", None))),
        (Th095, 13, Some(("C", None))),
        (Th095, 14, Some(("SN", None))),
        // 15 appears to be a nop (i.e. it's not in the jumptable).
        //    However, no game ever uses it

        (Th10, 3, Some(("SUfff", None))),
        (Th10, 5, Some(("SUfff", None))),
        (Th10, 9, Some(("SUCff", None))), // Technically the C arg is split into 4 individual byte reads. But why tho

        (Alcostg, 16, Some(("S(imm)", Some(IKind::InterruptLabel)))),

        (Th11, 17, Some(("S", None))),

        (Th12, 18, Some(("SUfff", None))),

        (Th14, 14, Some(("SNS", None))),  // 'layer' argument added
        (Th14, 19, Some(("S", None))),
        (Th14, 20, Some(("f", None))),

        (Th17, 21, Some(("SSf", None))),

        (Th20, 22, Some(("S", None))),
    ],
    var: &[],
};
