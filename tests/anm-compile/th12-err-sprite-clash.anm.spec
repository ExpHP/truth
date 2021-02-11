// It is okay for two sprites to have the same name (this occurs in decompiled output),
// but they must also have the same ID.

#pragma image_source "./tests/anm-compile/th12-multiple-match-source.anm"

entry {
    path: "subdir/file1.png",
    has_data: false,
    sprites: {my_sprite: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}


entry {
    path: "subdir/file2.png",
    has_data: false,
    sprites: {my_sprite: {id: 1, x: 2.0, y: 2.0, w: 222.0, h: 220.0}},
}


script script0 {
    ins_1();
}

