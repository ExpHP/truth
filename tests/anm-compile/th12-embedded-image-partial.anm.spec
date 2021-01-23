// This input gathers both an image and its metadata from an existing anm file.
//
// It also overrides sprites and scripts.

#pragma mapfile "map/any.anmm"
#pragma image_source "./tests/anm-compile/th12-embedded-image-source.anm"

entry {
    path: "lmao.png",
    has_data: true,
    // overridden from image source
    sprites: {sprite0: {id: 0, x: 12.0, y: 0.0, w: 40.0, h: 60.0}},
}

// also overridden
script -45 script0 {
    static();
}

script script1 {
    static();
}
