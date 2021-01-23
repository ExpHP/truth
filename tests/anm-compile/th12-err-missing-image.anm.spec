// This input is identical to "no-source-required.anm.spec" except with has_data: true, so it will fail.

#pragma mapfile "map/any.anmm"

entry {
    path: "subdir/file.png",
    has_data: true,
    width: 512,
    height: 512,
    offset_x: 0,
    offset_y: 0,
    format: 3,
    colorkey: 0,
    memory_priority: 0,
    low_res_scale: false,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 512.0, h: 480.0}},
}


script -45 script0 {
    delete();
}
