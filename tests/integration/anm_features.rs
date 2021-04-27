use truth::sp;

use crate::integration_impl::formats::*;
use crate::integration_impl::{TestFile, expected};

// =============================================================================
// ANM file image sources

source_test!(
    ANM_10, image_source_does_not_exist,
    items: r#"
        #pragma image_source "this/is/a/bad/path"
    "#,
    expect_fail: "reading file",
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
    source: "copy",
    buf_width: 128,
    buf_height: 128,
    offset_x: 200,  // overridden from image source
    offset_y: 0,
    buf_format: 3,
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
    source: "copy",
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
            assert_eq!(anm.entries[0].sprites[0].offset, [12.0, 0.0]);
            assert_eq!(anm.entries[0].scripts.len(), 2);
            assert_eq!(anm.entries[0].scripts[0].instrs[0].opcode, 2);
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
    source: "none",
    buf_width: 512,  // "none" requires buf_*.  Defaulting from img_* will be tested later
    buf_height: 512,
    buf_format: 3,
    offset_x: 0,
    offset_y: 0,
    colorkey: 0,
    memory_priority: 0,
    low_res_scale: false,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 512.0, h: 480.0}},
}


script -45 script0 {
    delete();
}
"#,
        check_compiled: |output, format| {
            assert!(output.read_anm(format).entries[0].texture.is_none());
        }
    );

    // This test uses "dummy" instead of "none".
    source_test!(
        ANM_12, dummy,
        full_source: r#"
#pragma mapfile "map/any.anmm"

entry {
    path: "subdir/file.png",
    source: "dummy",
    img_width: 512,
    img_height: 512,
    img_format: 3,
    offset_x: 0,
    offset_y: 0,
    colorkey: 0,
    memory_priority: 0,
    low_res_scale: false,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 512.0, h: 480.0}},
}


script -45 script0 {
    delete();
}
"#,
        check_compiled: |output, format| {
            assert!(output.read_anm(format).entries[0].texture.is_some());
        }
    );

    // Test defaulted fields.
    source_test!(
        ANM_12, default_fields,
        full_source: r#"
#pragma mapfile "map/any.anmm"

entry {
    path: "subdir/file.png",
    source: "none",
    img_width: 512,  // use img_ here to test defaulting of buf_ from img_
    img_height: 512,
    img_format: 3,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 512.0, h: 480.0}},
}


script -45 script0 {
    delete();
}
"#,
        check_compiled: |output, format| {
            let anm = output.read_anm(format);
            assert_eq!(anm.entries[0].specs.offset_x, Some(0));
            assert_eq!(anm.entries[0].specs.offset_y, Some(0));
            assert_eq!(anm.entries[0].specs.colorkey, Some(0));
            assert_eq!(anm.entries[0].specs.memory_priority, Some(10));
            assert_eq!(anm.entries[0].specs.low_res_scale, Some(false));
        }
    );

    // This input is like 'okay' but it is missing some metadata.
    source_test!(
        ANM_12, err_missing_metadata,
        full_source: r#"
#pragma mapfile "map/any.anmm"

entry {
    path: "subdir/file.png",
    source: "none",
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 512.0, h: 480.0}},
}

script -45 script0 {
    delete();
}
        "#,
        expect_fail: "required field",
    );

    // This input is identical to 'okay' except with source: "copy", so it will fail.
    source_test!(
        ANM_12, err_missing_image,
        full_source: r#"
#pragma mapfile "map/any.anmm"

entry {
    path: "subdir/file.png",
    source: "copy",
    buf_width: 512,
    buf_height: 512,
    offset_x: 0,
    offset_y: 0,
    buf_format: 3,
    colorkey: 0,
    memory_priority: 0,
    low_res_scale: false,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 512.0, h: 480.0}},
}

script -45 script0 {
    delete();
}
        "#,
        expect_fail: "no bitmap data",
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
    source: "none",
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}

script script0 {
    ins_1();
}

entry {
    path: "subdir/file1.png",
    source: "none",
    sprites: {sprite1: {id: 1, x: 2.0, y: 2.0, w: 222.0, h: 220.0}},
}

script script1 {
    ins_2();
}
    "#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        assert_eq!(anm.entries[0].specs.buf_width, Some(sp!(2000)));  // pulled from file1
        assert_eq!(anm.entries[0].sprites[0].size, [111.0, 111.0]);
        assert_eq!(anm.entries[0].scripts[0].instrs[0].opcode, 1);
        assert_eq!(anm.entries[1].specs.buf_width, Some(sp!(1000)));  // pulled from file2
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
    source: "none",
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}

script script0 {
    ins_1();
}

entry {
    path: "@R",
    source: "none",
    sprites: {sprite1: {id: 1, x: 2.0, y: 2.0, w: 222.0, h: 220.0}},
}

script script1 {
    ins_2();
}
    "#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        assert_eq!(anm.entries[0].specs.buf_width, Some(sp!(1000)));
        assert_eq!(anm.entries[0].sprites[0].size, [111.0, 111.0]);
        assert_eq!(anm.entries[0].scripts[0].instrs[0].opcode, 1);
        assert_eq!(anm.entries[1].specs.buf_width, Some(sp!(2000)));
        assert_eq!(anm.entries[1].sprites[0].size, [222.0, 220.0]);
        assert_eq!(anm.entries[1].scripts[0].instrs[0].opcode, 2);
    },
);

// FIXME somehow group these image_source tests so that new formats are automatically tested?
source_test!(
    STD_08, image_source_in_std,
    items: r#"
        #pragma image_source "tests/integration/resources/th12-embedded-image-source.anm"
    "#,
    expect_fail: "unexpected image_source",
);
source_test!(
    MSG_06, image_source_in_msg,
    items: r#"
        #pragma image_source "tests/integration/resources/th12-embedded-image-source.anm"
    "#,
    expect_fail: "unexpected image_source",
);
source_test!(
    ECL_08, image_source_in_ecl,
    items: r#"
        #pragma image_source "tests/integration/resources/th12-embedded-image-source.anm"
    "#,
    expect_fail: "unexpected image_source",
);

// =============================================================================
// Directory image sources

source_test!(
    ANM_12, png_import_32x16,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hi-32x16.png",
    source: "copy",
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}
    "#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let specs = anm.entries[0].specs.fill_defaults(format.game);
        assert_eq!(specs.img_width, Some(sp!(32)));
        assert_eq!(specs.img_height, Some(sp!(16)));
        assert_eq!(specs.img_format, Some(sp!(1)));
        assert_eq!(specs.buf_width, Some(sp!(32)));
        assert_eq!(specs.buf_height, Some(sp!(16)));
        assert_eq!(specs.buf_format, Some(sp!(1)));
        assert!(anm.entries[0].texture.unwrap().data.is_some());
        assert_eq!(anm.entries[0].sprites.len(), 1);
    },
);

source_test!(
    ANM_12, png_import_7x20,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hi-7x20.png",
    source: "copy",
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}
    "#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let specs = anm.entries[0].specs.fill_defaults(format.game);
        assert_eq!(specs.img_width, Some(sp!(7)));
        assert_eq!(specs.img_height, Some(sp!(20)));
        assert_eq!(specs.img_format, Some(sp!(1)));
        assert_eq!(specs.buf_width, Some(sp!(16)));
        assert_eq!(specs.buf_height, Some(sp!(32)));
        assert_eq!(specs.buf_format, Some(sp!(1)));
        assert!(anm.entries[0].texture.unwrap().data.is_some());
        assert_eq!(anm.entries[0].sprites.len(), 1);
    },
);

source_test!(
    ANM_12, png_import_with_buf_props,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hi-32x16.png",
    source: "copy",
    buf_width: 128,
    buf_height: 256,
    buf_format: 3,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}
    "#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let specs = anm.entries[0].specs.fill_defaults(format.game);
        assert_eq!(specs.img_width, Some(sp!(32)));
        assert_eq!(specs.img_height, Some(sp!(16)));
        assert_eq!(specs.img_format, Some(sp!(1)));
        assert_eq!(specs.buf_width, Some(sp!(128)));
        assert_eq!(specs.buf_height, Some(sp!(256)));
        assert_eq!(specs.buf_format, Some(sp!(3)));
        let pixel_size = 4; // bytes per pixel for format 1, the default
        assert_eq!(anm.entries[0].texture.unwrap().data.len(), pixel_size * 128 * 128);
        assert_eq!(anm.entries[0].sprites.len(), 1);
    },
);

source_test!(
    ANM_12, png_import_explicit_img_format,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-images"

entry {
    path: "subdir/hi-32x16.png",
    source: "copy",
    img_format: 3,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}
    "#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let specs = anm.entries[0].specs.fill_defaults(format.game);
        assert_eq!(specs.img_width, Some(sp!(7)));
        assert_eq!(specs.img_height, Some(sp!(20)));
        assert_eq!(specs.img_format, Some(sp!(1)));
        assert_eq!(specs.buf_width, Some(sp!(16)));
        assert_eq!(specs.buf_height, Some(sp!(32)));
        assert_eq!(specs.buf_format, Some(sp!(1)));
        let pixel_size = 2; // bytes per pixel for format 3
        assert_eq!(anm.entries[0].texture.unwrap().data.len(), pixel_size * 32 * 16);
        assert_eq!(anm.entries[0].sprites.len(), 1);
    },
);

source_test!(
    ANM_12, png_import_multiple_dirs,
    full_source: r#"
#pragma image_source "./tests/integration/resources/dir-with-nothing-really"
#pragma image_source "./tests/integration/resources/dir-with-images"
#pragma image_source "./tests/integration/resources/dir-with-nothing-really"

entry {
    path: "subdir/hi-32x16.png",
    source: "copy",
    img_format: 3,
    sprites: {sprite0: {id: 0, x: 1.0, y: 1.0, w: 111.0, h: 111.0}},
}
    "#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        let specs = anm.entries[0].specs.fill_defaults(format.game);
        assert_eq!(specs.img_width, Some(sp!(7)));
        assert_eq!(specs.img_height, Some(sp!(20)));
        assert_eq!(specs.img_format, Some(sp!(1)));
        assert_eq!(specs.buf_width, Some(sp!(16)));
        assert_eq!(specs.buf_height, Some(sp!(32)));
        assert_eq!(specs.buf_format, Some(sp!(1)));
        let pixel_size = 2; // bytes per pixel for format 3
        assert_eq!(anm.entries[0].texture.unwrap().data.len(), pixel_size * 32 * 16);
        assert_eq!(anm.entries[0].sprites.len(), 1);
    },
);

// FIXME: Should have a test where both a .anm and a directory have the same image path,
//        but currently the order of image-source application isn't specified beyond
//        "things in file take precedence over CLI"

// FIXME: Test with wrong img_width/img_height

// FIXME: Test with buf_width/buf_height not a power of 2

// FIXME: Test with buf_width/buf_height not large enough for image dimensions

// =============================================================================

#[test]
fn thecl_defs() {
    let format = &ANM_12;
    let thecl_defs = TestFile::new_temp("thecl defs output");
    format.compile_with_args(&TestFile::from_content("input", r#"
#pragma image_source "./tests/integration/resources/th12-multiple-match-source.anm"

entry {
    path: "subdir/file1.png",
    source: "none",
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 40.0, h: 60.0}},
}

script -45 hello {}

script there {}

entry {
    path: "subdir/file2.png",
    source: "none",
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 40.0, h: 60.0}},
}

script howyado {}
    "#), &["--output-thecl-defs".as_ref(), thecl_defs.as_path().as_ref()]);

    let actual = thecl_defs.read_to_string();
    let expected = r#"
global hello = 0;
global there = 1;
global howyado = 2;
    "#;
    assert_eq!(actual.trim(), expected.trim());
}
