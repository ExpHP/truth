// NOTE: This file shows what was compiled to produce `th12-multiple-match-source.anm`.
//       It is mostly here for explanatory purposes.
//       Since it is not tested, it may fall out of date with the latest compiler syntax.

entry {
    path: "subdir/file1.png",
    has_data: false,
    rt_width: 1024,
    rt_height: 1024,
    offset_x: 0,
    offset_y: 0,
    img_format: 3,
    colorkey: 0,
    memory_priority: 0,
    low_res_scale: false,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}


script script0 {
    ins_1();
}


entry {
    path: "subdir/file2.png",
    has_data: false,
    rt_width: 2048,
    rt_height: 2048,
    offset_x: 0,
    offset_y: 0,
    img_format: 3,
    colorkey: 0,
    memory_priority: 0,
    low_res_scale: false,
    sprites: {sprite1: {id: 1, x: 2.0, y: 2.0, w: 222.0, h: 220.0}},
}


script script1 {
    ins_2();
}

