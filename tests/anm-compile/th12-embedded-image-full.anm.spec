// This input gathers its image from an existing anm file.

#pragma mapfile "map/any.anmm"
#pragma image_source "./tests/anm-compile/th12-embedded-image-source.anm"

entry {
    path: "lmao.png",
    has_data: true,
    width: 128,
    height: 128,
    offset_x: 200,  // overridden from image source
    offset_y: 0,
    format: 3,
    colorkey: 0,
    memory_priority: 0,
    low_res_scale: false,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 40.0, h: 60.0}},
}


script -45 script0 {
    delete();
}
