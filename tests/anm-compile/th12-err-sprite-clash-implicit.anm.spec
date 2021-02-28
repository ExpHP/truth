// Variant of th12-err-sprite-clash where one of the dupes has an implicit ID.
// (so we can check the spans in this case)

#pragma image_source "./tests/anm-compile/th12-multiple-match-source.anm"

entry {
    path: "subdir/file1.png",
    has_data: false,
    sprites: {my_sprite: {x: 1.0, y: 1.0, w: 111.0, h: 111.0, id: 1}},
}


entry {
    path: "subdir/file2.png",
    has_data: false,
    sprites: {my_sprite: {x: 2.0, y: 2.0, w: 222.0, h: 220.0}},
}


script script0 {
    ins_1();
}

