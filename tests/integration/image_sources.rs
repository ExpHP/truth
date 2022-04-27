use truth::sp;

#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

// =============================================================================
// ANM file image sources

source_test!(
    ANM_10, image_source_does_not_exist,
    items: r#"
        #pragma image_source "this/is/a/bad/path"
    "#,
    expect_error: "while resolving",
);

// Tests that copy an embedded image
mod embedded_image {
    use super::*;

    // These tests are based on "th12-embedded-image-source.anm",
    //  whose original source can be seen at "th12-embedded-image-source.anm.spec"

    // This input gathers its image from an existing anm file.
    source_test!(
        ANM_12, full,
        full_source: r#"
#pragma mapfile "map/any.anmm"
#pragma image_source "./tests/integration/resources/th12-embedded-image-source.anm"

entry {
    path: "lmao.png",
    has_data: true,
    rt_width: 256,  // overriden from image source
    rt_height: 128,
    offset_x: 200,  // overridden from image source
    offset_y: 0,
    rt_format: FORMAT_RGB_565,
    colorkey: 0,
    memory_priority: 0,
    low_res_scale: false,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 40.0, h: 60.0}},
}


script -45 script0 {
    delete();
}
"#,
        check_compiled: |output, format| {
            let anm = output.read_anm(format);
            assert_eq!(anm.entries[0].specs.offset_x, Some(200));
            // the image has unnatural dimensions; make sure they are copied correctly
            assert_eq!(anm.entries[0].specs.img_width, Some(sp!(105)));
            assert_eq!(anm.entries[0].specs.img_height, Some(sp!(100)));
            assert_eq!(anm.entries[0].specs.rt_width, Some(sp!(256)));
            assert_eq!(anm.entries[0].specs.rt_height, Some(sp!(128)));
        },
    );

    // This input gathers both an image and its metadata from an existing anm file.
    //
    // It also overrides sprites and scripts.
    source_test!(
        ANM_12, partial,
        full_source: r#"
#pragma mapfile "map/any.anmm"
#pragma image_source "./tests/integration/resources/th12-embedded-image-source.anm"

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
"#,
        check_compiled: |output, format| {
            let anm = output.read_anm(format);
            // can't check img_* because they're not saved
            // assert_eq!(anm.entries[0].specs.img_width, Some(sp!(105)));
            // assert_eq!(anm.entries[0].specs.img_height, Some(sp!(100)));
            assert_eq!(anm.entries[0].specs.rt_width, Some(sp!(128)));
            assert_eq!(anm.entries[0].specs.rt_height, Some(sp!(128)));
            assert_eq!(anm.entries[0].sprites[0].offset, [12.0, 0.0]);
            assert_eq!(anm.entries[0].scripts.len(), 2);
            assert_eq!(anm.entries[0].scripts[0].instrs[0].opcode, 2);
        },
    );

    // This embedded image has an offset.
    //
    // This is to ensure that the code that subtracts offsets from PNG dimensions doesn't
    // also accidentally apply to embedded images.
    source_test!(
        ANM_12, offset,
        full_source: r#"
#pragma mapfile "map/any.anmm"
#pragma image_source "./tests/integration/resources/th12-embedded-image-source.anm"

entry {
    path: "subdir/hai-10x18+105+9.png",
    has_data: true,
    sprites: {},
}"#,
        check_compiled: |output, format| {
            let anm = output.read_anm(format);
            let specs = anm.entries[0].specs.fill_defaults(format.game);
            assert_eq!(specs.img_width, Some(sp!(10)));
            assert_eq!(specs.img_height, Some(sp!(18)));
            assert_eq!(specs.rt_width, Some(sp!(16)));
            assert_eq!(specs.rt_height, Some(sp!(32)));
            check_data_for_hai_10_18_argb_8888(&anm.entries[0].texture.as_ref().unwrap().data);
        },
    );

    // This reads embedded image metadata to generate dummy data.
    source_test!(
        ANM_12, dummy,
        full_source: r#"
#pragma mapfile "map/any.anmm"
#pragma image_source "./tests/integration/resources/th12-embedded-image-source.anm"

entry {
    path: "subdir/hai-10x18+105+9.png",
    has_data: "dummy",
    sprites: {},
}"#,
        check_compiled: |output, format| {
            let anm = output.read_anm(format);
            let data = &anm.entries[0].texture.as_ref().unwrap().data;
            assert_eq!(data.len(), 4 * 10 * 18);
            assert_eq!(&data[..4], &data[4..8]); // all pixels are the same (unlike the original "hai" image)
        },
    );
}

// Tests with no image source.
mod no_source {
    use super::*;

    // Test that it is possible to compile ANM scripts that require no image source.
    source_test!(
        ANM_12, okay,
        full_source: r#"
#pragma mapfile "map/any.anmm"

entry {
    path: "subdir/file.png",
    has_data: false,
    rt_width: 512,
    rt_height: 512,
    rt_format: 3,
    offset_x: 0,
    offset_y: 0,
    colorkey: 0,
    memory_priority: 0,
    low_res_scale: false,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 512.0, h: 480.0}},
}"#,
        check_compiled: |output, format| {
            assert!(output.read_anm(format).entries[0].texture.is_none());
        }
    );

    // Test defaulted fields.
    source_test!(
        ANM_12, default_fields,
        full_source: r#"
#pragma mapfile "map/any.anmm"

entry {
    path: "subdir/file.png",
    has_data: false,
    img_width: 512,  // use img_ here to test defaulting of buf_ from img_
    img_height: 512,
    img_format: 3,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 512.0, h: 480.0}},
}"#,
        check_compiled: |output, format| {
            let anm = output.read_anm(format);
            let specs = anm.entries[0].specs.fill_defaults(format.game);

            assert_eq!(specs.offset_x, Some(0));
            assert_eq!(specs.offset_y, Some(0));
            assert_eq!(specs.colorkey, Some(0));
            assert_eq!(specs.memory_priority, Some(10));
            assert_eq!(specs.low_res_scale, Some(false));
        }
    );

    // This input is like 'okay' but it is missing some metadata.
    source_test!(
        ANM_12, err_missing_metadata,
        full_source: r#"
#pragma mapfile "map/any.anmm"

entry {
    path: "subdir/file.png",
    has_data: false,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 512.0, h: 480.0}},
}"#,
        expect_error: "required field",
    );

    // This input is identical to 'okay' except with 'has_data: true', so it will fail.
    source_test!(
        ANM_12, err_missing_image,
        full_source: r#"
#pragma mapfile "map/any.anmm"

entry {
    path: "subdir/file.png",
    has_data: true,
    rt_width: 512,
    rt_height: 512,
    offset_x: 0,
    offset_y: 0,
    rt_format: 3,
    colorkey: 0,
    memory_priority: 0,
    low_res_scale: false,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 512.0, h: 480.0}},
}"#,
        expect_error: "no bitmap data",
    );
}

// This file tests that metadata is grabbed from the entry with the matching name
// even when out of order.
source_test!(
    ANM_12, multiple_match,
    // Note for all_files_tested(): image source based on "th12-multiple-match-source.anm.spec"
    full_source: r#"
#pragma image_source "./tests/integration/resources/th12-multiple-match-source.anm"

entry {
    path: "subdir/file2.png",
    has_data: false,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}

script script0 {
    ins_1();
}

entry {
    path: "subdir/file1.png",
    has_data: false,
    sprites: {sprite1: {id: 1, x: 2.0, y: 2.0, w: 222.0, h: 220.0}},
}

script script1 {
    ins_2();
}
    "#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        assert_eq!(anm.entries[0].specs.rt_width, Some(sp!(2048)));  // pulled from file1
        assert_eq!(anm.entries[0].sprites[0].size, [111.0, 111.0]);
        assert_eq!(anm.entries[0].scripts[0].instrs[0].opcode, 1);
        assert_eq!(anm.entries[1].specs.rt_width, Some(sp!(1024)));  // pulled from file2
        assert_eq!(anm.entries[1].sprites[0].size, [222.0, 220.0]);
        assert_eq!(anm.entries[1].scripts[0].instrs[0].opcode, 2);
    },
);

// This file tests that metadata can be grabbed from multiple entries with the
// same path; they are matched by order in the file.
source_test!(
    ANM_12, multiple_same,
    // Note for all_files_tested(): image source based on "th12-multiple-same-source.anm.spec"
    full_source: r#"
#pragma image_source "./tests/integration/resources/th12-multiple-same-source.anm"

entry {
    path: "@R",
    has_data: false,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}

script script0 {
    ins_1();
}

entry {
    path: "@R",
    has_data: false,
    sprites: {sprite1: {id: 1, x: 2.0, y: 2.0, w: 222.0, h: 220.0}},
}

script script1 {
    ins_2();
}
    "#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);

        assert_eq!(anm.entries[0].specs.rt_width, Some(sp!(1024)));
        assert_eq!(anm.entries[0].sprites[0].size, [111.0, 111.0]);
        assert_eq!(anm.entries[0].scripts[0].instrs[0].opcode, 1);
        assert_eq!(anm.entries[1].specs.rt_width, Some(sp!(2048)));
        assert_eq!(anm.entries[1].sprites[0].size, [222.0, 220.0]);
        assert_eq!(anm.entries[1].scripts[0].instrs[0].opcode, 2);
    },
);

source_test!(
    ANM_12, copy_meta_with_anm_source,
    full_source: r#"
#pragma image_source "./tests/integration/resources/th12-multiple-match-source.anm"

entry {
    path: "subdir/file2.png",
    has_data: false,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}"#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let specs = anm.entries[0].specs.fill_defaults(format.game);
        // assert_eq!(specs.img_width, Some(sp!(2000)));  // not saved in anm file...
        assert_eq!(specs.rt_width, Some(sp!(2048)));
        assert!(anm.entries[0].texture.is_none());
    },
);

source_test!(
    // has_data: "dummy" should be able to set image dimensions that conflict with an
    //  existing entry in an image source
    ANM_12, dummy_overriding_anm,
    full_source: r#"
#pragma image_source "./tests/integration/resources/th12-embedded-image-source.anm"

entry {
    path: "subdir/hai-10x18.png",
    has_data: "dummy",
    img_width: 8,  // set different dimensions that conflict with the original
    img_height: 16,
    img_format: FORMAT_GRAY_8,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 10.0}},
}"#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let data = &anm.entries[0].texture.as_ref().unwrap().data;
        assert_eq!(data.len(), 1 * 8 * 16);  // use dimensions from script
        assert!(data.iter().all(|&byte| byte == data[0])); // all pixels are the same
    },
);

source_test!(
    ANM_12, dummy_overrides_directory,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hi-32x16.png",
    has_data: "dummy",
    img_width: 8,  // set different dimensions that conflict with the original
    img_height: 16,
    img_format: FORMAT_GRAY_8,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 10.0}},
}"#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let data = &anm.entries[0].texture.as_ref().unwrap().data;
        assert_eq!(data.len(), 1 * 8 * 16);  // use dimensions from script
        assert!(data.iter().all(|&byte| byte == data[0])); // all pixels are the same
    },
);

// Dimensions of 'subdir/modified-size.png' in the ANM file source versus the directory source.
const MODIFIED_WIDTH_IN_ANM: u32 = 4;
const MODIFIED_HEIGHT_IN_ANM: u32 = 8;
const MODIFIED_WIDTH_IN_DIR: u32 = 12;
const MODIFIED_HEIGHT_IN_DIR: u32 = 6;

source_test!(
    ANM_12, conflicting_directory_over_anm,
    full_source: r#"
#pragma image_source "./tests/integration/resources/th12-embedded-image-source.anm"
#pragma image_source "./tests/integration/resources/dir-with-images"  // <-- takes priority

entry {
    path: "subdir/modified-size.png",
    img_format: FORMAT_GRAY_8,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 10.0}},
}"#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let entry = &anm.entries[0];
        assert_eq!(entry.specs.img_width, Some(sp!(MODIFIED_WIDTH_IN_DIR)));
        assert_eq!(entry.specs.img_height, Some(sp!(MODIFIED_HEIGHT_IN_DIR)));

        let data = &anm.entries[0].texture.as_ref().unwrap().data;
        assert_eq!(data.len(), (1 * MODIFIED_WIDTH_IN_DIR * MODIFIED_HEIGHT_IN_DIR) as usize);
        assert!(data.iter().all(|&byte| byte == data[0])); // all pixels are the same
    },
);

source_test!(
    ANM_12, conflicting_anm_over_directory,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"
#pragma image_source "./tests/integration/resources/th12-embedded-image-source.anm"  // <-- takes priority

entry {
    path: "subdir/modified-size.png",
    img_format: FORMAT_GRAY_8,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 10.0}},
}"#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let entry = &anm.entries[0];
        assert_eq!(entry.specs.img_width, Some(sp!(MODIFIED_WIDTH_IN_ANM)));
        assert_eq!(entry.specs.img_height, Some(sp!(MODIFIED_HEIGHT_IN_ANM)));

        let data = &anm.entries[0].texture.as_ref().unwrap().data;
        assert_eq!(data.len(), (1 * MODIFIED_WIDTH_IN_ANM * MODIFIED_HEIGHT_IN_ANM) as usize);
        assert!(data.iter().all(|&byte| byte == data[0])); // all pixels are the same
    },
);

source_test!(
    ANM_12, cli_overrides_pragmas,
    compile_args: &["-i", "./tests/integration/resources/dir-with-images"],   // <-- takes priority
    full_source: r#"
#pragma image_source "./tests/integration/resources/th12-embedded-image-source.anm"

entry {
    path: "subdir/modified-size.png",
    img_format: FORMAT_GRAY_8,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 10.0}},
}"#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let entry = &anm.entries[0];
        assert_eq!(entry.specs.img_width, Some(sp!(MODIFIED_WIDTH_IN_DIR)));
        assert_eq!(entry.specs.img_height, Some(sp!(MODIFIED_HEIGHT_IN_DIR)));
    },
);

source_test!(
    ANM_12, cli_precedence,
    compile_args: &[
        "-i./tests/integration/resources/th12-embedded-image-source.anm",
        "-i./tests/integration/resources/dir-with-images",  // <-- takes priority
    ],
    full_source: r#"
entry {
    path: "subdir/modified-size.png",
    img_format: FORMAT_GRAY_8,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 10.0}},
}"#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let entry = &anm.entries[0];
        assert_eq!(entry.specs.img_width, Some(sp!(MODIFIED_WIDTH_IN_DIR)));
        assert_eq!(entry.specs.img_height, Some(sp!(MODIFIED_HEIGHT_IN_DIR)));
    },
);

mod color_formats {
    use super::*;

    // This one is okay because it requires no conversion.
    source_test!(
        // Note for all_files_tested(): image source based on "th12-embedded-weird-format-source.anm.spec"
        ANM_12, weird_identity_ok,
        full_source: r#"
// This file has an image with img_format: 8
#pragma image_source "./tests/integration/resources/th12-embedded-weird-format-source.anm"

entry {
    path: "teeny.png",
    has_data: true,
    img_format: 8,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 10.0}},
}
        "#,
        check_compiled: |output, format| {
            let anm = output.read_anm(format);
            assert_eq!(anm.entries[0].specs.img_format, Some(sp!(8)));
            assert!(anm.entries[0].texture.is_some());
        },
    );

    source_test!(
        ANM_12, transcode_ok,
        full_source: r#"
// This file has an image with img_format: 8
#pragma image_source "./tests/integration/resources/th12-embedded-image-source.anm"

entry {
    path: "subdir/hai-10x18+105+9.png",
    has_data: true,
    img_format: FORMAT_GRAY_8,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 10.0}},
}"#,
        check_compiled: |output, format| {
            let anm = output.read_anm(format);
            assert_eq!(anm.entries[0].specs.img_format, Some(sp!(7)));
            check_data_for_hai_10_18_gray_8(&anm.entries[0].texture.as_ref().unwrap().data);
        },
    );

    source_test!(
        ANM_12, bad_transcode_from,
        full_source: r#"
// This file has an image with img_format: 8
#pragma image_source "./tests/integration/resources/th12-embedded-weird-format-source.anm"

entry {
    path: "teeny.png",
    has_data: true,
    img_format: FORMAT_GRAY_8,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 10.0}},
}"#,
        expect_error: "from unknown color format",
    );

    source_test!(
        ANM_12, bad_transcode_into,
        full_source: r#"
// This file has an image with img_format: 8
#pragma image_source "./tests/integration/resources/th12-embedded-image-source.anm"

entry {
    path: "lmao.png",
    has_data: true,
    img_format: 8,   //~ ERROR into unknown color format
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 10.0}},
}"#,
    );

    source_test!(
        ANM_12, dummy_ok,
        full_source: r#"
entry {
    path: "i-dont-exist.png",
    has_data: "dummy",
    img_width: 27,
    img_height: 25,
    img_format: FORMAT_GRAY_8,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 10.0}},
}"#,
        check_compiled: |output, format| {
            let anm = output.read_anm(format);
            let data = &anm.entries[0].texture.as_ref().unwrap().data;
            assert_eq!(data.len(), 1 * 27 * 25);
            assert_eq!(&data[..1], &data[1..2]); // all pixels are the same
        },
    );

    source_test!(
        ANM_12, bad_dummy,
        full_source: r#"
entry {
    path: "i-dont-exist.png",
    has_data: "dummy",
    img_width: 27,
    img_height: 25,
    img_format: 8,   //~ ERROR unknown color format
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 10.0}},
}"#,
    );

    source_test!(
        ANM_12, image_ok,
        full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hai-10x18.png",
    has_data: true,
    img_format: FORMAT_GRAY_8,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 10.0}},
}"#,
        check_compiled: |output, format| {
            let anm = output.read_anm(format);
            assert_eq!(anm.entries[0].specs.img_format, Some(sp!(7)));
            check_data_for_hai_10_18_gray_8(&anm.entries[0].texture.as_ref().unwrap().data);
        },
    );

    source_test!(
        ANM_12, bad_image,
        full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hi-7x20.png",
    has_data: true,
    img_format: 8,  //~ ERROR into unknown color format
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 10.0, h: 10.0}},
}"#,
    );
}

// FIXME somehow group these image_source tests so that new formats are automatically tested?
source_test!(
    STD_08, image_source_in_std,
    items: r#"
        #pragma image_source "tests/integration/resources/th12-embedded-image-source.anm"
        //~^ ERROR unexpected image_source
    "#,
);
source_test!(
    MSG_06, image_source_in_msg,
    items: r#"
        #pragma image_source "tests/integration/resources/th12-embedded-image-source.anm"
        //~^ ERROR unexpected image_source
    "#,
);
source_test!(
    ECL_06, image_source_in_olde_ecl,
    items: r#"
        #pragma image_source "tests/integration/resources/th12-embedded-image-source.anm"
        //~^ ERROR unexpected image_source
    "#,
);
// FIXME: modern ECL test when it exists

// =============================================================================
// Directory image sources

source_test!(
    ANM_12, png_import_32x16,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hi-32x16.png",
    has_data: true,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}"#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let specs = anm.entries[0].specs.fill_defaults(format.game);
        assert_eq!(specs.img_width, Some(sp!(32)));
        assert_eq!(specs.img_height, Some(sp!(16)));
        assert_eq!(specs.img_format, Some(sp!(1)));
        assert_eq!(specs.rt_width, Some(sp!(32)));
        assert_eq!(specs.rt_height, Some(sp!(16)));
        assert_eq!(specs.rt_format, Some(sp!(1)));
        assert!(anm.entries[0].texture.is_some());
        assert_eq!(anm.entries[0].sprites.len(), 1);
    },
);

source_test!(
    ANM_12, png_import_7x20,  // non powers of 2
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hi-7x20.png",
    has_data: true,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}"#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let specs = anm.entries[0].specs.fill_defaults(format.game);
        assert_eq!(specs.img_width, Some(sp!(7)));
        assert_eq!(specs.img_height, Some(sp!(20)));
        assert_eq!(specs.img_format, Some(sp!(1)));
        assert_eq!(specs.rt_width, Some(sp!(8)));
        assert_eq!(specs.rt_height, Some(sp!(32)));
        assert_eq!(specs.rt_format, Some(sp!(1)));
        assert!(anm.entries[0].texture.is_some());
        assert_eq!(anm.entries[0].sprites.len(), 1);
    },
);

source_test!(
    ANM_12, png_import_with_offset,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hai-10x18+105+9.png",
    offset_x: 105,
    offset_y: 9,
    has_data: true,
    img_format: FORMAT_ARGB_8888,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}"#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let specs = anm.entries[0].specs.fill_defaults(format.game);
        assert_eq!(specs.img_width, Some(sp!(10)));
        assert_eq!(specs.img_height, Some(sp!(18)));
        assert_eq!(specs.rt_width, Some(sp!(16)));
        assert_eq!(specs.rt_height, Some(sp!(32)));
        check_data_for_hai_10_18_argb_8888(&anm.entries[0].texture.as_ref().unwrap().data);
    },
);

// The test image "subdir/hai-10x18.png" has a special 2x2 marker in the top left:
//             gray-128  gray-192
//             gray-48   gray-0
// This can be used to check that the proper region was extracted.
fn check_data_for_hai_10_18_argb_8888(data: &[u8]) {
    let pixel_size = 4;
    let row_size = pixel_size * 10;
    assert_eq!(data.len(), row_size * 18);
    assert_eq!(
        &data[..2 * pixel_size],
        &[0x80, 0x80, 0x80, 0xFF, 0xC0, 0xC0, 0xC0, 0xFF],
    );
    assert_eq!(
        &data[row_size..row_size + 2 * pixel_size],
        &[0x40, 0x40, 0x40, 0xFF, 0x00, 0x00, 0x00, 0xFF],
    );
}

fn check_data_for_hai_10_18_gray_8(data: &[u8]) {
    let pixel_size = 1;
    let row_size = pixel_size * 10;
    assert_eq!(data.len(), row_size * 18);
    assert_eq!(
        &data[..2 * pixel_size],
        &[0x80, 0xC0],
    );
    assert_eq!(
        &data[row_size..row_size + 2 * pixel_size],
        &[0x40, 0x00],
    );
}

source_test!(
    ANM_12, png_import_meta_32x16,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hi-32x16.png",
    has_data: false,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}"#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let specs = anm.entries[0].specs.fill_defaults(format.game);
        assert_eq!(specs.rt_width, Some(sp!(32)));
        assert_eq!(specs.rt_height, Some(sp!(16)));
        assert_eq!(specs.rt_format, Some(sp!(1)));
        assert!(anm.entries[0].texture.is_none());
        assert_eq!(anm.entries[0].sprites.len(), 1);
    },
);

source_test!(
    ANM_12, png_import_meta_7x20,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hi-7x20.png",
    has_data: false,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}"#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let specs = anm.entries[0].specs.fill_defaults(format.game);
        assert_eq!(specs.rt_width, Some(sp!(8)));
        assert_eq!(specs.rt_height, Some(sp!(32)));
        assert_eq!(specs.rt_format, Some(sp!(1)));
        assert!(anm.entries[0].texture.is_none());
        assert_eq!(anm.entries[0].sprites.len(), 1);
    },
);

source_test!(
    ANM_12, png_import_meta_with_offset,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hai-10x18+105+9.png",
    offset_x: 105,
    offset_y: 9,
    has_data: false,
    img_format: FORMAT_ARGB_8888,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}"#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let specs = anm.entries[0].specs.fill_defaults(format.game);

        // buffer should be appropriately sized for the region WITHOUT the offset padding
        assert_eq!(specs.rt_width, Some(sp!(16)));
        assert_eq!(specs.rt_height, Some(sp!(32)));
        assert_eq!(specs.rt_format, Some(sp!(1)));
        assert!(anm.entries[0].texture.is_none());
    },
);

source_test!(
    ANM_12, png_import_with_buf_props,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hi-32x16.png",
    has_data: true,
    rt_width: 128,
    rt_height: 256,
    rt_format: 3,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}"#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let specs = anm.entries[0].specs.fill_defaults(format.game);
        assert_eq!(specs.img_width, Some(sp!(32)));
        assert_eq!(specs.img_height, Some(sp!(16)));
        assert_eq!(specs.img_format, Some(sp!(1)));
        assert_eq!(specs.rt_width, Some(sp!(128)));
        assert_eq!(specs.rt_height, Some(sp!(256)));
        assert_eq!(specs.rt_format, Some(sp!(3)));
        let pixel_size = 4; // bytes per pixel for format 1, the default
        assert_eq!(anm.entries[0].texture.as_ref().unwrap().data.len(), pixel_size * 32 * 16);
        assert_eq!(anm.entries[0].sprites.len(), 1);
    },
);

source_test!(
    ANM_12, png_import_explicit_img_format,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hi-32x16.png",
    has_data: true,
    img_format: 3,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}"#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let specs = anm.entries[0].specs.fill_defaults(format.game);
        assert_eq!(specs.img_width, Some(sp!(32)));
        assert_eq!(specs.img_height, Some(sp!(16)));
        assert_eq!(specs.img_format, Some(sp!(3)));
        assert_eq!(specs.rt_width, Some(sp!(32)));
        assert_eq!(specs.rt_height, Some(sp!(16)));
        assert_eq!(specs.rt_format, Some(sp!(3)));
        let pixel_size = 2; // bytes per pixel for format 3
        assert_eq!(anm.entries[0].texture.as_ref().unwrap().data.len(), pixel_size * 32 * 16);
        assert_eq!(anm.entries[0].sprites.len(), 1);
    },
);

// FIXME NEEDSTEST: explicit_img_format equivalent for ANM file sources (i.e. transcode the THTX data)

source_test!(
    ANM_12, png_import_multiple_dirs,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-nothing-really"
#pragma image_source "./tests/integration/resources/dir-with-images"
#pragma image_source "./tests/integration/resources/dir-with-nothing-really"

entry {
    path: "subdir/hi-32x16.png",
    has_data: false,
    img_format: 3,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}"#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let specs = anm.entries[0].specs.fill_defaults(format.game);
        assert_eq!(specs.rt_width, Some(sp!(32)));
        assert_eq!(specs.rt_height, Some(sp!(16)));
        assert!(anm.entries[0].texture.is_none());
        assert_eq!(anm.entries[0].sprites.len(), 1);
    },
);

// FIXME NEEDSTEST:
//        Should have a test where both a .anm and a directory have the same image path,
//        but currently the order of image-source application isn't specified beyond
//        "things in file take precedence over CLI"

source_test!(
    ANM_12, png_import_wrong_img_height,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hi-32x16.png",
    has_data: false,
    img_format: 3,
    img_width: 32,
    img_height: 32,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}"#,
    expect_error: "wrong image dimensions",
);

source_test!(
    ANM_12, png_import_with_offset_too_big,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hai-10x18+105+9.png",
    offset_x: 1050,
    offset_y: 90,
    has_data: true,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}"#,
    expect_error: "image too small",
);

source_test!(
    ANM_12, png_import_buf_not_power_2,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hi-7x20.png",
    has_data: false,
    rt_width: 7,     //~ WARNING not a power of two
    rt_height: 21,   //~ WARNING not a power of two
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}"#,
);

source_test!(
    ANM_12, png_import_buf_too_small,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hi-32x16.png",
    has_data: false,
    rt_height: 16,
    rt_width: 16,   //~ WARNING too small for
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}"#,
);
