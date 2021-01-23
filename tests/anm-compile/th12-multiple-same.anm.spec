// This file tests that metadata can be grabbed from multiple entries with the
// same path; they are matched by order in the file.

#pragma image_source "./tests/anm-compile/th12-multiple-same-source.anm"

entry {
    path: "@R",
    has_data: false,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}


script script0 {
    ins_1();
}


entry {
    path: "@R",
    has_data: false,
    sprites: {sprite1: {id: 1, x: 2.0, y: 2.0, w: 222.0, h: 220.0}},
}


script script1 {
    ins_2();
}

