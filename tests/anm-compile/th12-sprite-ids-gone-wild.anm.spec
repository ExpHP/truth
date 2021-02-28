// This is the first written test of const vars that depend on other const vars.
// (sprite IDs were the first const vars implemented in the compiler, even before
//  const var items!)

#pragma image_source "./tests/anm-compile/th12-multiple-match-source.anm"

entry {
    path: "subdir/file1.png",
    has_data: false,
    sprites: {
        valueA: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: valueC + 2 - valueC},
        valueB: {x: 0.0, y: 0.0, w: 0.0, h: 0.0},
        valueC: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: 26 * 2 + 1},
        valueD: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: valueE - 1},
    },
}


entry {
    path: "subdir/file2.png",
    has_data: false,
    sprites: {
        valueE: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: 401},
        valueF: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: _S(%valueE + 2.4) + 1},
    },
}


script script0 {
    ins_1();
}

