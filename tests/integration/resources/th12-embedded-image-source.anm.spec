// NOTE: This file shows what was compiled to produce `th12-embedded-image-source.anm`. (minus the image)
//       It is mostly here for explanatory purposes.
//       Since it is not tested, it may fall out of date with the latest compiler syntax.

#pragma mapfile "map/any.anmm"

entry {
    path: "lmao.png",
    has_data: true,
    img_width: 105,
    img_height: 100,
    img_format: 3,
    buf_width: 128,
    buf_height: 128,
    offset_x: 0,
    offset_y: 0,
    colorkey: 0,
    memory_priority: 0,
    low_res_scale: false,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 40.0, h: 60.0}},
}


script -45 script0 {
    ins_1();
}


// an image with an offset
entry {
    path: "subdir/hi-10x18+105+9.png",  // the image from resources/dir-with-images
    has_data: true,
    img_width: 10,
    img_height: 18,
    img_format: 1,
    offset_x: 105,
    offset_y: 9,
    buf_width: 16,
    buf_height: 32,
    colorkey: 0,
    memory_priority: 0,
    low_res_scale: false,
    sprites: {sprite1: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 18.0}},
}
