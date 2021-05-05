// NOTE: This file shows what was compiled to produce `th12-embedded-weird-format-source.anm`. (minus the image)
//       It is mostly here for explanatory purposes.
//       Since it is not tested, it may fall out of date with the latest compiler syntax.

#pragma mapfile "map/any.anmm"

entry {
    path: "teeny.png",
    has_data: true,
    img_width: 27,
    img_height: 25,
    // this was compiled with img_format: 7 then modified to 8 in a hex editor
    img_format: 8,
    buf_width: 128,
    buf_height: 128,
    offset_x: 0,
    offset_y: 0,
    colorkey: 0,
    memory_priority: 0,
    low_res_scale: false,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 40.0, h: 60.0}},
}

script script0 {}
