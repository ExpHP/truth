// This input is like "no-source-required.anm.spec" but it is missing some metadata.

#pragma mapfile "map/any.anmm"

entry {
    path: "subdir/file.png",
    has_data: false,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 512.0, h: 480.0}},
}


script -45 script0 {
    delete();
}
