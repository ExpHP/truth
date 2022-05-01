// NOTE: This file shows what was compiled to produce `th12-embedded-image-source.anm`. (minus the image)
//       It is mostly here for explanatory purposes.
//       Since it is not tested, it may fall out of date with the latest compiler syntax.

#pragma mapfile "map/any.anmm"

entry {
    path: "lmao.png",
    has_data: true,
    img_format: FORMAT_RGB_565,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 40.0, h: 60.0}},
}


script -45 script0 {
    ins_1();
}


// an image with a marker suitable for testing transcoding
entry {
    path: "subdir/hai-10x18.png",  // the image from resources/dir-with-images
    img_format: FORMAT_ARGB_8888,
    sprites: {sprite1: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 18.0}},
}


// an image with an offset
entry {
    path: "subdir/hai-10x18+105+9.png",  // the image from resources/dir-with-images
    img_format: FORMAT_ARGB_8888,
    offset_x: 105,
    offset_y: 9,
    sprites: {sprite1: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 18.0}},
}


// an image that differs between two image sources.
entry {
    path: "subdir/modified-size.png",  // the image from resources/dir-with-images
    has_data: true,
    img_format: FORMAT_ARGB_8888,
    sprites: {sprite1: {id: 0, x: 0.0, y: 0.0, w: 2.0, h: 2.0}},
}
