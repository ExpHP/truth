// NOTE: This file shows what was compiled to produce `th12-embedded-bad-image-source.anm`. (minus the image)
//       It is mostly here for explanatory purposes.
//       Since it is not tested, it may fall out of date with the latest compiler syntax.

#pragma image_source "./tests/integration/resources/dir-with-bad-images"
#pragma mapfile "map/any.anmm"

// a fairly mundane image  (resized in this "bad" version)
entry {
    path: "subdir/hi-32x16.png",
    img_format: FORMAT_ARGB_8888,
    img_height: 12,  // differs from the one in th12-embedded-image-source.anm
    sprites: {sprite1: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 18.0}},
}


// an image with an offset  (missing in this "bad" version)
entry {
    path: "subdir/hai-10x18+105+9.png",
    img_format: FORMAT_ARGB_8888,
    offset_x: 0,  // differs from the one in th12-embedded-image-source.anm
    offset_y: 0,  // differs from the one in th12-embedded-image-source.anm
    sprites: {sprite1: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 18.0}},
}
