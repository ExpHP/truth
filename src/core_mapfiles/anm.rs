use super::CoreSignatures;
use crate::Game::{self, *};
use crate::llir::IntrinsicInstrKind as IKind;
use crate::ast::AssignOpKind as A;
use crate::ast::BinOpKind as B;
use crate::ast::UnOpKind as U;
use crate::value::ScalarType as Ty;

pub(super) fn core_signatures(game: Game) -> &'static CoreSignatures {
    match game {
        Th06 => {
            static OUT: &CoreSignatures = &CoreSignatures {
                inherit: &[ANM_INS_06, ANM_VAR],
                ins: &[], var: &[],
            };
            OUT
        },

        Th07 | Th08 | Th09 => {
            static OUT: &CoreSignatures = &CoreSignatures {
                inherit: &[ANM_INS_07_09, ANM_VAR],
                ins: &[], var: &[],
            };
            OUT
        },

        Th095 | Th10 | Alcostg | Th11 | Th12 | Th125 | Th128 => {
            static OUT: &CoreSignatures = &CoreSignatures {
                inherit: &[ANM_INS_095_128, ANM_VAR],
                ins: &[], var: &[],
            };
            OUT
        },

        Th13 | Th14 | Th143 | Th15 | Th16 | Th165 | Th17 | Th18 | Th185 | Th19 | Th20 => {
            static OUT: &CoreSignatures = &CoreSignatures {
                inherit: &[ANM_INS_13_20, ANM_VAR],
                ins: &[], var: &[],
            };
            OUT
        },
    }
}

// v0
static ANM_INS_06: &'static CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        (Th06, 0, Some(("", None))),
        (Th06, 1, Some(("n", None))),
        (Th06, 2, Some(("ff", None))),
        (Th06, 3, Some(("b(hex)---", None))),
        (Th06, 4, Some(("b(hex)b(hex)b(hex)-", None))),
        (Th06, 5, Some(("o", Some(IKind::Jmp)))),
        (Th06, 6, Some(("", None))),
        (Th06, 7, Some(("", None))),
        (Th06, 8, Some(("", None))),
        (Th06, 9, Some(("fff", None))),
        (Th06, 10, Some(("fff", None))),
        (Th06, 11, Some(("ff", None))),
        (Th06, 12, Some(("b(hex)---s--", None))),
        (Th06, 13, Some(("", None))),
        (Th06, 14, Some(("", None))),
        (Th06, 15, Some(("", None))),
        (Th06, 16, Some(("nu--", None))),
        (Th06, 17, Some(("fff", None))),
        (Th06, 18, Some(("fffs--", None))),
        (Th06, 19, Some(("fffs--", None))),
        (Th06, 20, Some(("fffs--", None))),
        (Th06, 21, Some(("", None))),
        (Th06, 22, Some(("S", Some(IKind::InterruptLabel)))),
        (Th06, 23, Some(("", None))),
        (Th06, 24, Some(("", None))),
        (Th06, 25, Some((r#"U(enum="bool")"#, None))), // zero: U(enum="BitBool")
        (Th06, 26, Some(("s--", None))),
        (Th06, 27, Some(("f", None))),
        (Th06, 28, Some(("f", None))),
        (Th06, 29, Some((r#"U(enum="bool")"#, None))), // zero: U(enum="BitBool")
        (Th06, 30, Some(("ffs--", None))),
        (Th06, 31, Some((r#"U(enum="bool")"#, None))), // zero: U(enum="BitBool")
    ],
    var: &[],
};

// v2/v3
static ANM_INS_07_09: &'static CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        // v2 (PCB)
        (Th07, 0, Some(("", None))),
        (Th07, 1, Some(("", None))),
        (Th07, 2, Some(("", None))),
        (Th07, 3, Some(("n", None))),
        (Th07, 4, Some(("ot", Some(IKind::Jmp)))),
        (Th07, 5, Some(("Sot", Some(IKind::CountJmp(B::Gt))))),
        (Th07, 6, Some(("fff", None))),
        (Th07, 7, Some(("ff", None))),
        (Th07, 8, Some(("b(imm;hex)---", None))),
        (Th07, 9, Some(("b(imm;hex)b(imm;hex)b(imm;hex)-", None))),
        (Th07, 10, Some(("", None))),
        (Th07, 11, Some(("", None))),
        (Th07, 12, Some(("fff", None))),
        (Th07, 13, Some(("fff", None))),
        (Th07, 14, Some(("ff", None))),
        (Th07, 15, Some(("b(imm;hex)---S", None))),
        (Th07, 16, Some(("U(imm)", None))),
        (Th07, 17, Some(("fffS", None))),
        (Th07, 18, Some(("fffS", None))),
        (Th07, 19, Some(("fffS", None))),
        (Th07, 20, Some(("", None))),
        (Th07, 21, Some(("S(imm)", Some(IKind::InterruptLabel)))),
        (Th07, 22, Some(("", None))),
        (Th07, 23, Some(("", None))),
        (Th07, 24, Some((r#"U(imm;enum="bool")"#, None))), // zero: U(imm;enum="BitBool")
        (Th07, 25, Some(("s(imm)--", None))),
        (Th07, 26, Some(("f", None))),
        (Th07, 27, Some(("f", None))),
        (Th07, 28, Some((r#"U(imm;enum="bool")"#, None))), // zero: U(imm;enum="BitBool")
        (Th07, 29, Some(("ffS", None))),
        (Th07, 30, Some((r#"U(imm;enum="bool")"#, None))), // zero: U(imm;enum="BitBool")
        (Th07, 31, Some((r#"U(imm;enum="bool")"#, None))), // zero: U(imm;enum="BitBool")
        (Th07, 32, Some(("Sb(imm)---fff", None))),
        (Th07, 33, Some(("Sb(imm)---b(imm;hex)b(imm;hex)b(imm;hex)-", None))),
        (Th07, 34, Some(("Sb(imm)---b(imm;hex)---", None))),
        (Th07, 35, Some(("Sb(imm)---fff", None))),
        (Th07, 36, Some(("Sb(imm)---ff", None))),
        (Th07, 37, Some(("SS", Some(IKind::AssignOp(A::Assign, Ty::Int))))),
        (Th07, 38, Some(("ff", Some(IKind::AssignOp(A::Assign, Ty::Float))))),
        (Th07, 39, Some(("SS", Some(IKind::AssignOp(A::Add, Ty::Int))))),
        (Th07, 40, Some(("ff", Some(IKind::AssignOp(A::Add, Ty::Float))))),
        (Th07, 41, Some(("SS", Some(IKind::AssignOp(A::Sub, Ty::Int))))),
        (Th07, 42, Some(("ff", Some(IKind::AssignOp(A::Sub, Ty::Float))))),
        (Th07, 43, Some(("SS", Some(IKind::AssignOp(A::Mul, Ty::Int))))),
        (Th07, 44, Some(("ff", Some(IKind::AssignOp(A::Mul, Ty::Float))))),
        (Th07, 45, Some(("SS", Some(IKind::AssignOp(A::Div, Ty::Int))))),
        (Th07, 46, Some(("ff", Some(IKind::AssignOp(A::Div, Ty::Float))))),
        (Th07, 47, Some(("SS", Some(IKind::AssignOp(A::Rem, Ty::Int))))),
        (Th07, 48, Some(("ff", Some(IKind::AssignOp(A::Rem, Ty::Float))))),
        (Th07, 49, Some(("SSS", Some(IKind::BinOp(B::Add, Ty::Int))))),
        (Th07, 50, Some(("fff", Some(IKind::BinOp(B::Add, Ty::Float))))),
        (Th07, 51, Some(("SSS", Some(IKind::BinOp(B::Sub, Ty::Int))))),
        (Th07, 52, Some(("fff", Some(IKind::BinOp(B::Sub, Ty::Float))))),
        (Th07, 53, Some(("SSS", Some(IKind::BinOp(B::Mul, Ty::Int))))),
        (Th07, 54, Some(("fff", Some(IKind::BinOp(B::Mul, Ty::Float))))),
        (Th07, 55, Some(("SSS", Some(IKind::BinOp(B::Div, Ty::Int))))),
        (Th07, 56, Some(("fff", Some(IKind::BinOp(B::Div, Ty::Float))))),
        (Th07, 57, Some(("SSS", Some(IKind::BinOp(B::Rem, Ty::Int))))),
        (Th07, 58, Some(("fff", Some(IKind::BinOp(B::Rem, Ty::Float))))),
        (Th07, 59, Some(("SU", None))),
        (Th07, 60, Some(("ff", None))),
        (Th07, 61, Some(("ff", Some(IKind::UnOp(U::Sin, Ty::Float))))),
        (Th07, 62, Some(("ff", Some(IKind::UnOp(U::Cos, Ty::Float))))),
        (Th07, 63, Some(("ff", Some(IKind::UnOp(U::Tan, Ty::Float))))),
        (Th07, 64, Some(("ff", Some(IKind::UnOp(U::Acos, Ty::Float))))),
        (Th07, 65, Some(("ff", Some(IKind::UnOp(U::Atan, Ty::Float))))),
        (Th07, 66, Some(("f", None))),
        (Th07, 67, Some(("SSot", Some(IKind::CondJmp(B::Eq, Ty::Int))))),
        (Th07, 68, Some(("ffot", Some(IKind::CondJmp(B::Eq, Ty::Float))))),
        (Th07, 69, Some(("SSot", Some(IKind::CondJmp(B::Ne, Ty::Int))))),
        (Th07, 70, Some(("ffot", Some(IKind::CondJmp(B::Ne, Ty::Float))))),
        (Th07, 71, Some(("SSot", Some(IKind::CondJmp(B::Lt, Ty::Int))))),
        (Th07, 72, Some(("ffot", Some(IKind::CondJmp(B::Lt, Ty::Float))))),
        (Th07, 73, Some(("SSot", Some(IKind::CondJmp(B::Le, Ty::Int))))),
        (Th07, 74, Some(("ffot", Some(IKind::CondJmp(B::Le, Ty::Float))))),
        (Th07, 75, Some(("SSot", Some(IKind::CondJmp(B::Gt, Ty::Int))))),
        (Th07, 76, Some(("ffot", Some(IKind::CondJmp(B::Gt, Ty::Float))))),
        (Th07, 77, Some(("SSot", Some(IKind::CondJmp(B::Ge, Ty::Int))))),
        (Th07, 78, Some(("ffot", Some(IKind::CondJmp(B::Ge, Ty::Float))))),
        (Th07, 79, Some(("S", None))),
        (Th07, 80, Some(("f", None))),
        (Th07, 81, Some(("f", None))),

        // v3, v3b (IN, PoFV)
        // alpha/color/alphaTime/colorTime instructions changed to take dword variables
        // alphaTimeLinear not updated
        (Th08, 8, Some(("C", None))),
        (Th08, 9, Some(("CCC", None))),
        (Th08, 16, Some((r#"U(imm;enum="bool")"#, None))),
        (Th08, 33, Some(("Sb(imm)---CCC", None))),
        (Th08, 34, Some(("Sb(imm)---C", None))),
        // new instructions
        (Th08, 82, Some(("U(imm)", None))),
        (Th08, 83, Some(("S(imm)", None))),
        (Th08, 84, Some(("CCC", None))),
        (Th08, 85, Some(("C", None))),
        (Th08, 86, Some(("Sb(imm)---CCC", None))),
        (Th08, 87, Some(("Sb(imm)---C", None))),
        (Th08, 88, Some(("-b(imm)--", None))),
        (Th08, 89, Some(("", None))),
    ],
    var: &[],
};

// v4/v7
static ANM_INS_095_128: &'static CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        // v4 (StB)
        (Th095, 0, Some(("", None))),
        (Th095, 1, Some(("", None))),
        (Th095, 2, Some(("", None))),
        (Th095, 3, Some(("n", None))),
        (Th095, 4, Some(("ot", Some(IKind::Jmp)))),
        (Th095, 5, Some(("Sot", Some(IKind::CountJmp(B::Ne))))),
        (Th095, 6, Some(("SS", Some(IKind::AssignOp(A::Assign, Ty::Int))))),
        (Th095, 7, Some(("ff", Some(IKind::AssignOp(A::Assign, Ty::Float))))),
        (Th095, 8, Some(("SS", Some(IKind::AssignOp(A::Add, Ty::Int))))),
        (Th095, 9, Some(("ff", Some(IKind::AssignOp(A::Add, Ty::Float))))),
        (Th095, 10, Some(("SS", Some(IKind::AssignOp(A::Sub, Ty::Int))))),
        (Th095, 11, Some(("ff", Some(IKind::AssignOp(A::Sub, Ty::Float))))),
        (Th095, 12, Some(("SS", Some(IKind::AssignOp(A::Mul, Ty::Int))))),
        (Th095, 13, Some(("ff", Some(IKind::AssignOp(A::Mul, Ty::Float))))),
        (Th095, 14, Some(("SS", Some(IKind::AssignOp(A::Div, Ty::Int))))),
        (Th095, 15, Some(("ff", Some(IKind::AssignOp(A::Div, Ty::Float))))),
        (Th095, 16, Some(("SS", Some(IKind::AssignOp(A::Rem, Ty::Int))))),
        (Th095, 17, Some(("ff", Some(IKind::AssignOp(A::Rem, Ty::Float))))),
        (Th095, 18, Some(("SSS", Some(IKind::BinOp(B::Add, Ty::Int))))),
        (Th095, 19, Some(("fff", Some(IKind::BinOp(B::Add, Ty::Float))))),
        (Th095, 20, Some(("SSS", Some(IKind::BinOp(B::Sub, Ty::Int))))),
        (Th095, 21, Some(("fff", Some(IKind::BinOp(B::Sub, Ty::Float))))),
        (Th095, 22, Some(("SSS", Some(IKind::BinOp(B::Mul, Ty::Int))))),
        (Th095, 23, Some(("fff", Some(IKind::BinOp(B::Mul, Ty::Float))))),
        (Th095, 24, Some(("SSS", Some(IKind::BinOp(B::Div, Ty::Int))))),
        (Th095, 25, Some(("fff", Some(IKind::BinOp(B::Div, Ty::Float))))),
        (Th095, 26, Some(("SSS", Some(IKind::BinOp(B::Rem, Ty::Int))))),
        (Th095, 27, Some(("fff", Some(IKind::BinOp(B::Rem, Ty::Float))))),
        (Th095, 28, Some(("SSot", Some(IKind::CondJmp(B::Eq, Ty::Int))))),
        (Th095, 29, Some(("ffot", Some(IKind::CondJmp(B::Eq, Ty::Float))))),
        (Th095, 30, Some(("SSot", Some(IKind::CondJmp(B::Ne, Ty::Int))))),
        (Th095, 31, Some(("ffot", Some(IKind::CondJmp(B::Ne, Ty::Float))))),
        (Th095, 32, Some(("SSot", Some(IKind::CondJmp(B::Lt, Ty::Int))))),
        (Th095, 33, Some(("ffot", Some(IKind::CondJmp(B::Lt, Ty::Float))))),
        (Th095, 34, Some(("SSot", Some(IKind::CondJmp(B::Le, Ty::Int))))),
        (Th095, 35, Some(("ffot", Some(IKind::CondJmp(B::Le, Ty::Float))))),
        (Th095, 36, Some(("SSot", Some(IKind::CondJmp(B::Gt, Ty::Int))))),
        (Th095, 37, Some(("ffot", Some(IKind::CondJmp(B::Gt, Ty::Float))))),
        (Th095, 38, Some(("SSot", Some(IKind::CondJmp(B::Ge, Ty::Int))))),
        (Th095, 39, Some(("ffot", Some(IKind::CondJmp(B::Ge, Ty::Float))))),
        (Th095, 40, Some(("SS", None))),
        (Th095, 41, Some(("ff", None))),
        (Th095, 42, Some(("ff", Some(IKind::UnOp(U::Sin, Ty::Float))))),
        (Th095, 43, Some(("ff", Some(IKind::UnOp(U::Cos, Ty::Float))))),
        (Th095, 44, Some(("ff", Some(IKind::UnOp(U::Tan, Ty::Float))))),
        (Th095, 45, Some(("ff", Some(IKind::UnOp(U::Acos, Ty::Float))))),
        (Th095, 46, Some(("ff", Some(IKind::UnOp(U::Atan, Ty::Float))))),
        (Th095, 47, Some(("f", None))),
        (Th095, 48, Some(("fff", None))),
        (Th095, 49, Some(("fff", None))),
        (Th095, 50, Some(("ff", None))),
        (Th095, 51, Some(("C", None))),
        (Th095, 52, Some(("CCC", None))),
        (Th095, 53, Some(("fff", None))),
        (Th095, 54, Some(("ff", None))),
        (Th095, 55, Some(("b(imm;hex)---S", None))),
        (Th095, 56, Some(("Sb(imm)---fff", None))),
        (Th095, 57, Some(("Sb(imm)---CCC", None))),
        (Th095, 58, Some(("Sb(imm)---C", None))),
        (Th095, 59, Some(("Sb(imm)---fff", None))),
        (Th095, 60, Some(("Sb(imm)---ff", None))),
        (Th095, 61, Some(("", None))),
        (Th095, 62, Some(("", None))),
        (Th095, 63, Some(("", None))),
        (Th095, 64, Some(("S(imm)", Some(IKind::InterruptLabel)))),
        (Th095, 65, Some(("u(imm)u(imm)", None))),
        (Th095, 66, Some(("U(imm)", None))),
        (Th095, 67, Some(("U(imm)", None))),
        (Th095, 68, Some(("b(imm)---", None))),
        (Th095, 69, Some(("", None))),
        (Th095, 70, Some(("f", None))),
        (Th095, 71, Some(("f", None))),
        (Th095, 72, Some((r#"U(imm;enum="bool")"#, None))), // zero: U(imm;enum="BitBool")
        (Th095, 73, Some((r#"U(imm;enum="bool")"#, None))), // zero: U(imm;enum="BitBool")
        (Th095, 74, Some((r#"U(imm;enum="bool")"#, None))), // zero: U(imm;enum="BitBool")
        (Th095, 75, Some(("S", None))),
        (Th095, 76, Some(("CCC", None))),
        (Th095, 77, Some(("C", None))),
        (Th095, 78, Some(("Sb(imm)---CCC", None))),
        (Th095, 79, Some(("Sb(imm)---C", None))),
        (Th095, 80, Some(("b(imm)---", None))),
        (Th095, 81, Some(("", None))),
        (Th095, 82, Some((r#"b(imm;enum="bool")---"#, None))), // zero: b(imm;enum="BitBool")---
        (Th095, 83, Some(("", None))),
        (Th095, 84, Some(("S", None))),
        (Th095, 85, Some((r#"b(imm;enum="bool")---"#, None))), // zero: b(imm;enum="BitBool")---
        (Th095, 86, Some((r#"U(enum="bool")"#, None))), // zero: U(enum="BitBool")
        (Th095, 87, Some(("b(imm)---", None))),

        // v4b (MoF, alcostg)
        // For some reason only a few of the interp instructions
        // were updated to use a 32 bit mode
        (Th10, 56, Some(("SU(imm)fff", None))),
        (Th10, 59, Some(("SU(imm)fff", None))),
        (Th10, 88, Some(("N", None))),
        (Th10, 89, Some((r#"U(imm;enum="bool")"#, None))), // zero: U(imm;enum="BitBool")
        (Th10, 90, Some(("N", None))),
        (Th10, 91, Some(("N", None))),
        (Th10, 92, Some(("N", None))),

        // v4c (SA)
        (Th11, 93, Some(("SU(imm)f", None))),
        (Th11, 94, Some(("SU(imm)f", None))),
        (Th11, 95, Some(("N", None))),
        (Th11, 96, Some(("Nff", None))),
        (Th11, 97, Some(("Nff", None))),
        (Th11, 98, Some(("", None))),
        (Th11, 99, Some((r#"U(enum="bool")"#, None))), // zero: U(enum="BitBool")
        (Th11, 100, Some(("Sfffffffff", None))),
        (Th11, 101, Some(("S", None))),
        (Th11, 102, Some(("nU", None))),

        // v4d (UFO)
        (Th12, 103, Some(("ff", None))),
        (Th12, 104, Some(("fS", None))),
        (Th12, 105, Some(("fS", None))),
        (Th12, 106, Some(("ff", None))),
        (Th12, 107, Some(("Sb(imm)---ff", None))),
        (Th12, 108, Some(("ff", None))),
        (Th12, 109, Some(("ff", None))),
        (Th12, 110, Some(("ff", None))),

        (Th125, 111, Some(("S", None))),
        (Th125, 112, Some(("S", None))),

        (Th128, 113, Some(("SSf", None))),
        (Th128, 114, Some(("S", None))),
    ],
    var: &[],
};

// v8
static ANM_INS_13_20: &CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[
        // Section A
        (Th13, 0, Some(("", None))),
        (Th13, 1, Some(("", None))),
        (Th13, 2, Some(("", None))),
        (Th13, 3, Some(("", None))),
        (Th13, 4, Some(("", None))),
        (Th13, 5, Some(("S", Some(IKind::InterruptLabel)))),
        (Th13, 6, Some(("S", None))),
        (Th13, 7, Some(("", None))),
        
        // Section B
        (Th13, 100, Some(("SS", Some(IKind::AssignOp(A::Assign, Ty::Int))))),
        (Th13, 101, Some(("ff", Some(IKind::AssignOp(A::Assign, Ty::Float))))),
        (Th13, 102, Some(("SS", Some(IKind::AssignOp(A::Add, Ty::Int))))),
        (Th13, 103, Some(("ff", Some(IKind::AssignOp(A::Add, Ty::Float))))),
        (Th13, 104, Some(("SS", Some(IKind::AssignOp(A::Sub, Ty::Int))))),
        (Th13, 105, Some(("ff", Some(IKind::AssignOp(A::Sub, Ty::Float))))),
        (Th13, 106, Some(("SS", Some(IKind::AssignOp(A::Mul, Ty::Int))))),
        (Th13, 107, Some(("ff", Some(IKind::AssignOp(A::Mul, Ty::Float))))),
        (Th13, 108, Some(("SS", Some(IKind::AssignOp(A::Div, Ty::Int))))),
        (Th13, 109, Some(("ff", Some(IKind::AssignOp(A::Div, Ty::Float))))),
        (Th13, 110, Some(("SS", Some(IKind::AssignOp(A::Rem, Ty::Int))))),
        (Th13, 111, Some(("ff", Some(IKind::AssignOp(A::Rem, Ty::Float))))),
        (Th13, 112, Some(("SSS", Some(IKind::BinOp(B::Add, Ty::Int))))),
        (Th13, 113, Some(("fff", Some(IKind::BinOp(B::Add, Ty::Float))))),
        (Th13, 114, Some(("SSS", Some(IKind::BinOp(B::Sub, Ty::Int))))),
        (Th13, 115, Some(("fff", Some(IKind::BinOp(B::Sub, Ty::Float))))),
        (Th13, 116, Some(("SSS", Some(IKind::BinOp(B::Mul, Ty::Int))))),
        (Th13, 117, Some(("fff", Some(IKind::BinOp(B::Mul, Ty::Float))))),
        (Th13, 118, Some(("SSS", Some(IKind::BinOp(B::Div, Ty::Int))))),
        (Th13, 119, Some(("fff", Some(IKind::BinOp(B::Div, Ty::Float))))),
        (Th13, 120, Some(("SSS", Some(IKind::BinOp(B::Rem, Ty::Int))))),
        (Th13, 121, Some(("fff", Some(IKind::BinOp(B::Rem, Ty::Float))))),
        (Th13, 122, Some(("SS", None))),
        (Th13, 123, Some(("ff", None))),
        (Th13, 124, Some(("ff", Some(IKind::UnOp(U::Sin, Ty::Float))))),
        (Th13, 125, Some(("ff", Some(IKind::UnOp(U::Cos, Ty::Float))))),
        (Th13, 126, Some(("ff", Some(IKind::UnOp(U::Tan, Ty::Float))))),
        (Th13, 127, Some(("ff", Some(IKind::UnOp(U::Acos, Ty::Float))))),
        (Th13, 128, Some(("ff", Some(IKind::UnOp(U::Atan, Ty::Float))))),
        (Th13, 129, Some(("f", None))),
        (Th13, 130, Some(("ffff", None))),
        (Th13, 131, Some(("ffff", None))),
        
        // Section C
        (Th13, 200, Some(("ot", Some(IKind::Jmp)))),
        (Th13, 201, Some(("Sot", Some(IKind::CountJmp(B::Ne))))),
        (Th13, 202, Some(("SSot", Some(IKind::CondJmp(B::Eq, Ty::Int))))),
        (Th13, 203, Some(("ffot", Some(IKind::CondJmp(B::Eq, Ty::Float))))),
        (Th13, 204, Some(("SSot", Some(IKind::CondJmp(B::Ne, Ty::Int))))),
        (Th13, 205, Some(("ffot", Some(IKind::CondJmp(B::Ne, Ty::Float))))),
        (Th13, 206, Some(("SSot", Some(IKind::CondJmp(B::Lt, Ty::Int))))),
        (Th13, 207, Some(("ffot", Some(IKind::CondJmp(B::Lt, Ty::Float))))),
        (Th13, 208, Some(("SSot", Some(IKind::CondJmp(B::Le, Ty::Int))))),
        (Th13, 209, Some(("ffot", Some(IKind::CondJmp(B::Le, Ty::Float))))),
        (Th13, 210, Some(("SSot", Some(IKind::CondJmp(B::Gt, Ty::Int))))),
        (Th13, 211, Some(("ffot", Some(IKind::CondJmp(B::Gt, Ty::Float))))),
        (Th13, 212, Some(("SSot", Some(IKind::CondJmp(B::Ge, Ty::Int))))),
        (Th13, 213, Some(("ffot", Some(IKind::CondJmp(B::Ge, Ty::Float))))),
        
        // Section D
        (Th13, 300, Some(("n", None))),
        (Th13, 301, Some(("nS", None))),
        (Th13, 302, Some(("S", None))),
        (Th13, 303, Some(("S", None))),
        (Th13, 304, Some(("S", None))),
        (Th13, 305, Some(("S", None))),
        (Th13, 306, Some(("S", None))),
        (Th13, 307, Some(("S", None))),
        (Th13, 308, Some(("", None))),
        (Th13, 309, Some(("", None))),
        (Th13, 310, Some(("S", None))),
        (Th13, 311, Some(("S", None))),
        (Th13, 312, Some(("SS", None))),
        
        (Th14, 313, Some(("S", None))),
        (Th14, 314, Some(("S", None))),
        (Th14, 315, Some(("S", None))),
        
        (Th143, 316, Some(("", None))),
        (Th143, 317, Some(("", None))),
        
        (Th19, 318, Some((r#"b(imm;enum="bool")---"#, None))), // zero: b(imm;enum="BitBool")---
        (Th19, 319, Some(("nnnn", None))),
        
        // Section E
        (Th13, 400, Some(("fff", None))),
        (Th13, 401, Some(("fff", None))),
        (Th13, 402, Some(("ff", None))),
        (Th13, 403, Some(("S", None))),
        (Th13, 404, Some(("SSS", None))),
        (Th13, 405, Some(("S", None))),
        (Th13, 406, Some(("SSS", None))),
        (Th13, 407, Some(("SSfff", None))),
        (Th13, 408, Some(("SSSSS", None))),
        (Th13, 409, Some(("SSS", None))),
        (Th13, 410, Some(("SSfff", None))),
        (Th13, 411, Some(("SSf", None))),
        (Th13, 412, Some(("SSff", None))),
        (Th13, 413, Some(("SSSSS", None))),
        (Th13, 414, Some(("SSS", None))),
        (Th13, 415, Some(("fff", None))),
        (Th13, 416, Some(("ff", None))),
        (Th13, 417, Some(("SS", None))),
        (Th13, 418, Some(("", None))),
        (Th13, 419, Some(("S", None))),
        (Th13, 420, Some(("Sfffffffff", None))),
        (Th13, 421, Some(("ss", None))),
        (Th13, 422, Some(("", None))),
        (Th13, 423, Some(("S", None))),
        (Th13, 424, Some(("S", None))),
        (Th13, 425, Some(("f", None))),
        (Th13, 426, Some(("f", None))),
        (Th13, 427, Some(("SSf", None))),
        (Th13, 428, Some(("SSf", None))),
        (Th13, 429, Some(("ff", None))),
        (Th13, 430, Some(("SSff", None))),
        (Th13, 431, Some(("S", None))),
        (Th13, 432, Some(("S", None))),
        (Th13, 433, Some(("SSff", None))),
        (Th13, 434, Some(("ff", None))),
        (Th13, 435, Some(("SSff", None))),
        (Th13, 436, Some(("ff", None))),
        (Th13, 437, Some(("S", None))),
        (Th13, 438, Some(("S", None))),
        
        (Th165, 439, Some(("S", None))),  // files use this, but it's not in the jumptable!

        (Th17, 439, None),  // ... TH17 doesn't use it ...

        (Th18, 439, Some(("Sff", None))),  // ...and TH18 demo reused its ID for something else!
        
        (Th185, 440, Some(("", None))),
        
        // Section F
        (Th13, 500, Some(("N", None))),
        (Th13, 501, Some(("N", None))),
        (Th13, 502, Some(("N", None))),
        (Th13, 503, Some(("N", None))),
        (Th13, 504, Some(("N", None))),
        (Th13, 505, Some(("Nff", None))),
        (Th13, 506, Some(("Nff", None))),
        (Th13, 507, Some(("S", None))),
        (Th13, 508, Some(("S", None))),
        
        (Th14, 509, Some(("", None))),
        
        (Th19, 510, Some(("Nff", None))),
        
        // Section G
        (Th13, 600, Some(("S", None))),
        (Th13, 601, Some(("S", None))),
        (Th13, 602, Some(("S", None))),
        (Th13, 603, Some(("ff", None))),
        (Th13, 604, Some(("fS", None))),
        (Th13, 605, Some(("fS", None))),
        (Th13, 606, Some(("ff", None))),
        (Th13, 607, Some(("ff", None))),
        (Th13, 608, Some(("ff", None))),

        (Th14, 609, Some(("S", None))),
        (Th14, 610, Some(("S", None))),

        (Th143, 611, Some(("ffS", None))),

        (Th16, 612, Some(("ff", None))),
        (Th16, 613, Some(("ff", None))),

        (Th18, 614, Some(("ff", None))),
        
        (Th19, 615, Some(("ffS", None))),
        (Th19, 616, Some(("ffS", None))),
        (Th19, 617, Some(("fS", None))),
        (Th19, 618, Some(("", None))),
        (Th19, 619, Some(("fS", None))),
        (Th19, 620, Some(("ffS", None))),
        (Th19, 621, Some(("ffS", None))),
        (Th19, 622, Some(("ffS", None))),
        (Th19, 623, Some(("fffS", None))),
        (Th19, 624, Some(("fffS", None))),
        (Th19, 625, Some(("ffffS", None))),
        (Th19, 626, Some(("ffffS", None))),
        (Th19, 627, Some(("ffffS", None))),
        (Th19, 628, Some(("fS", None))),
        (Th19, 629, Some(("fS", None))),
        (Th19, 630, Some(("ffS", None))),
        (Th19, 631, Some(("ffS", None))),
        (Th19, 632, Some(("ffS", None))),
    ],
    var: &[],
};

// All versions
static ANM_VAR: &'static CoreSignatures = &CoreSignatures {
    inherit: &[],
    ins: &[],
    var: &[
        // v2, v3 (PCB, IN)
        (Th07, 10000, Some("$")),
        (Th07, 10001, Some("$")),
        (Th07, 10002, Some("$")),
        (Th07, 10003, Some("$")),
        (Th07, 10004, Some("%")),
        (Th07, 10005, Some("%")),
        (Th07, 10006, Some("%")),
        (Th07, 10007, Some("%")),
        (Th07, 10008, Some("$")),
        (Th07, 10009, Some("$")),

        // v3b (PoFV)
        (Th09, 10010, Some("%")),
        (Th09, 10011, Some("%")),
        (Th09, 10012, Some("%")),

        // v4 (StB)
        (Th095, 10013, Some("%")),
        (Th095, 10014, Some("%")),
        (Th095, 10015, Some("%")),

        // v4b (MoF, alcostg)
        (Th10, 10016, Some("%")),
        (Th10, 10017, Some("%")),
        (Th10, 10018, Some("%")),
        (Th10, 10019, Some("%")),
        (Th10, 10020, Some("%")),
        (Th10, 10021, Some("%")),

        // v4c (SA)
        (Th11, 10022, Some("$")),

        // v4d (UFO)
        (Th12, 10023, Some("%")),
        (Th12, 10024, Some("%")),
        (Th12, 10025, Some("%")),

        (Th13, 10026, Some("%")),
        (Th13, 10027, Some("%")),
        (Th13, 10028, Some("%")),
        (Th13, 10029, Some("$")),
        (Th13, 10030, Some("%")),
        (Th13, 10031, Some("%")),
        (Th13, 10032, Some("%")),

        (Th14, 10033, Some("%")),
        (Th14, 10034, Some("%")),
        (Th14, 10035, Some("%")),
    ],
};
