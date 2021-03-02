use crate::integration_impl::formats::*;
use crate::integration_impl::{TestFile, expected};

// =============================================================================
// Image sources

compile_fail_test!(
    ANM_10, image_source_does_not_exist,
    items_before: r#"
        #pragma image_source "this/is/a/bad/path"
    "#,
    main_body: "",
    expected: "reading file",
);

// Tests that copy an embedded image
mod embedded_image {
    use super::*;

    // These tests are based on "th12-embedded-image-source.anm",
    //  whose original source can be seen at "th12-embedded-image-source.anm.spec"

    // This input gathers its image from an existing anm file.
    #[test]
    fn full() {
        let format = &ANM_12;
        let anm = format.compile(&TestFile::from_content("input", r#"
#pragma mapfile "map/any.anmm"
#pragma image_source "./tests/integration/resources/th12-embedded-image-source.anm"

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
"#)).read_anm(format);
        assert_eq!(anm.entries[0].specs.offset_x, Some(200));
    }

    // This input gathers both an image and its metadata from an existing anm file.
    //
    // It also overrides sprites and scripts.
    #[test]
    fn partial() {
        let format = &ANM_12;
        let anm = format.compile(&TestFile::from_content("input", r#"
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
"#)).read_anm(format);
        assert_eq!(anm.entries[0].sprites[0].offset, [12.0, 0.0]);
        assert_eq!(anm.entries[0].scripts.len(), 2);
        assert_eq!(anm.entries[0].scripts[0].instrs[0].opcode, 2);
    }
}

// Tests with no image source.
mod no_source {
    use super::*;

    // Test that it is possible to compile ANM scripts that require no image source.
    #[test]
    fn okay() {
        let format = &ANM_12;
        format.compile(&TestFile::from_content("input", r#"
#pragma mapfile "map/any.anmm"

entry {
    path: "subdir/file.png",
    has_data: false,
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
"#)).read_anm(format);
    }

    // This input is like 'okay' but it is missing some metadata.
    compile_fail_test!(
        ANM_12, err_missing_metadata,
        full_source: r#"
#pragma mapfile "map/any.anmm"

entry {
    path: "subdir/file.png",
    has_data: false,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 512.0, h: 480.0}},
}

script -45 script0 {
    delete();
}
        "#,
        expected: "required field",
    );

    // This input is identical to 'okay' except with has_data: true, so it will fail.
    compile_fail_test!(
        ANM_12, err_missing_image,
        full_source: r#"
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
        "#,
        expected: "no bitmap data",
    );
}

// This file tests that metadata is grabbed from the entry with the matching name
// even when out of order.
#[test]
fn multiple_match() {
    // Note for all_files_tested(): image source based on "th12-multiple-match-source.anm.spec"
    let format = &ANM_12;
    let anm = format.compile(&TestFile::from_content("input", r#"
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
    "#)).read_anm(format);
    assert_eq!(anm.entries[0].specs.width, Some(2000));  // pulled from file1
    assert_eq!(anm.entries[0].sprites[0].size, [111.0, 111.0]);
    assert_eq!(anm.entries[0].scripts[0].instrs[0].opcode, 1);
    assert_eq!(anm.entries[1].specs.width, Some(1000));  // pulled from file2
    assert_eq!(anm.entries[1].sprites[0].size, [222.0, 220.0]);
    assert_eq!(anm.entries[1].scripts[0].instrs[0].opcode, 2);
}

// This file tests that metadata can be grabbed from multiple entries with the
// same path; they are matched by order in the file.
#[test]
fn multiple_same() {
    // Note for all_files_tested(): image source based on "th12-multiple-same-source.anm.spec"
    let format = &ANM_12;
    let anm = format.compile(&TestFile::from_content("input", r#"
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
    "#)).read_anm(format);
    assert_eq!(anm.entries[0].specs.width, Some(1000));
    assert_eq!(anm.entries[0].sprites[0].size, [111.0, 111.0]);
    assert_eq!(anm.entries[0].scripts[0].instrs[0].opcode, 1);
    assert_eq!(anm.entries[1].specs.width, Some(2000));
    assert_eq!(anm.entries[1].sprites[0].size, [222.0, 220.0]);
    assert_eq!(anm.entries[1].scripts[0].instrs[0].opcode, 2);
}

// FIXME somehow group these image_source tests so that new formats are automatically tested?
compile_fail_test!(
    STD_08, image_source_in_std,
    items_before: r#"
        #pragma image_source "tests/integration/resources/th12-embedded-image-source.anm"
    "#,
    main_body: "",
    expected: "unexpected image_source",
);
compile_fail_test!(
    MSG_06, image_source_in_msg,
    items_before: r#"
        #pragma image_source "tests/integration/resources/th12-embedded-image-source.anm"
    "#,
    main_body: "",
    expected: "unexpected image_source",
);

// =============================================================================
// Sprite IDs

// This is the first written test of const vars that depend on other const vars.
// (sprite IDs were the first const vars implemented in the compiler, even before
//  const var items!)
#[test]
fn sprite_ids_gone_wild() {
    let format = &ANM_12;
    let anm = format.compile(&TestFile::from_content("input", r#"
#pragma image_source "./tests/integration/resources/th12-multiple-match-source.anm"

entry {
    path: "subdir/file1.png",
    has_data: false,
    sprites: {
        valueA: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: valueC + 2 - valueC},
        valueB: {x: 0.0, y: 0.0, w: 0.0, h: 0.0},
        valueC: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: 26 * 2 + 1},
        valueD: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: valueE - 1},
    },
}

entry {
    path: "subdir/file2.png",
    has_data: false,
    sprites: {
        valueE: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: 401},
        valueF: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: _S(%valueE + 2.4) + 1},
    },
}

script script0 {
    ins_1();
}
    "#)).read_anm(format);
    assert_eq!(anm.entries[0].sprites[0].id, Some(2));
    assert_eq!(anm.entries[0].sprites[1].id, None);  // 3
    assert_eq!(anm.entries[0].sprites[2].id, Some(53));
    assert_eq!(anm.entries[0].sprites[3].id, Some(400));
    assert_eq!(anm.entries[1].sprites[0].id, None);  // 401
    assert_eq!(anm.entries[1].sprites[1].id, Some(404));
}

compile_fail_test!(
    ANM_10, meta_sprite_id_circular_dependency,
    items_before: r#"
entry {
    path: "subdir/file-2.png",
    has_data: false,
    sprites: {
        coolSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: bestSprite * 3},
        bestSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: coolestSprite * 3},
        coolestSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: coolSprite + 1},
    },
}
    "#,
    main_body: "",
    expected: "depends on its own value",
);

compile_fail_test!(
    ANM_10, meta_non_const,
    items_before: r#"
entry {
    path: "subdir/file-2.png",
    has_data: false,
    memory_priority: 3 * I0,
    low_res_scale: false,
    sprites: {
        sprite200: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 200},
    },
}
    "#,
    main_body: "",
    // NOTE: be careful changing this.  If the new error complains about missing fields
    // or missing image data, fix the test input instead.
    expected: "const",
);

// It is okay for two sprites to have the same name (this occurs in decompiled output),
// but they must also have the same ID.
#[test]
fn sprite_ids_dupe() {
    let format = &ANM_12;
    let anm = format.compile(&TestFile::from_content("input", r#"
#pragma image_source "./tests/integration/resources/th12-multiple-match-source.anm"

entry {
    path: "subdir/file1.png",
    has_data: false,
    sprites: {
        valueA: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: 26 * 2 + 1},
    },
}

entry {
    path: "subdir/file2.png",
    has_data: false,
    sprites: {
        xyzzyx: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: 24},
        valueA: {x: 1.0, y: 1.0, w: 1.0, h: 1.0, id: 53},
    },
}

script script0 {
    ins_1();
}
    "#)).read_anm(format);
    assert_eq!(anm.entries[0].sprites[0].id, Some(53));
    assert_eq!(anm.entries[1].sprites[0].id, Some(24));
    assert_eq!(anm.entries[1].sprites[1].id, Some(53));
}

// same but one's implicit
#[test]
fn sprite_ids_dupe_implicit() {
    let format = &ANM_12;
    let anm = format.compile(&TestFile::from_content("input", r#"
#pragma image_source "./tests/integration/resources/th12-multiple-match-source.anm"

entry {
    path: "subdir/file1.png",
    has_data: false,
    sprites: {
        valueA: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: 26 * 2 + 1},
    },
}

entry {
    path: "subdir/file2.png",
    has_data: false,
    sprites: {
        xyzzyx: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: 52},
        valueA: {x: 1.0, y: 1.0, w: 1.0, h: 1.0},   // dupe, but has same id as above
    },
}

script script0 {
    ins_1();
}
    "#)).read_anm(format);
    assert_eq!(anm.entries[0].sprites[0].id, Some(53));
    assert_eq!(anm.entries[1].sprites[0].id, Some(52));
    assert_eq!(anm.entries[1].sprites[1].id, None);  // 53
}

// Now they have mismatched IDs.
compile_fail_test!(
    ANM_12, err_sprite_clash,
    full_source: r#"
#pragma image_source "./tests/integration/resources/th12-multiple-match-source.anm"

entry {
    path: "subdir/file1.png",
    has_data: false,
    sprites: {my_sprite: {x: 1.0, y: 1.0, w: 111.0, h: 111.0, id: 0}},
}

entry {
    path: "subdir/file2.png",
    has_data: false,
    sprites: {my_sprite: {x: 2.0, y: 2.0, w: 222.0, h: 220.0, id: 1}},
}

script script0 {
    ins_1();
}
    "#,
    expected: "redefinition"
);

// Same but one's implicit.
compile_fail_test!(
    ANM_12, err_sprite_clash_implicit,
    full_source: r#"
#pragma image_source "./tests/integration/resources/th12-multiple-match-source.anm"

entry {
    path: "subdir/file1.png",
    has_data: false,
    sprites: {my_sprite: {x: 1.0, y: 1.0, w: 111.0, h: 111.0, id: 1}},
}

entry {
    path: "subdir/file2.png",
    has_data: false,
    sprites: {my_sprite: {x: 2.0, y: 2.0, w: 222.0, h: 220.0}},
}

script script0 {
    ins_1();
}
    "#,
    expected: "redefinition"
);

// Type-checking/const-checking sprite IDs is actually a bit annoying.
compile_fail_test!(
    ANM_10, meta_sprite_id_type_error,
    items_before: r#"
entry {
    path: "subdir/file-2.png",
    has_data: false,
    sprites: {
        coolSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 3.5},
    },
}
    "#,
    main_body: "",
    expected: expected::TYPE_ERROR,
);

compile_fail_test!(
    ANM_10, meta_sprite_id_non_const,
    items_before: r#"
entry {
    path: "subdir/file-2.png",
    has_data: false,
    sprites: {
        sprite200: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 3 * I0},
    },
}
    "#,
    main_body: "",
    expected: "const",
);

// Dupes may follow different code paths for type checking and const checking since
// the expressions are never used beyond checking equality to the originals.
compile_fail_test!(
    ANM_10, meta_sprite_id_dupe_type_error,
    items_before: r#"
entry {
    path: "subdir/file-2.png",
    has_data: false,
    sprites: {
        coolSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 3},
    },
}
entry {
    path: "subdir/file-3.png",
    has_data: false,
    sprites: {
        coolSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 3.5},
    },
}
    "#,
    main_body: "",
    expected: expected::TYPE_ERROR,
);

compile_fail_test!(
    ANM_10, meta_sprite_id_dupe_non_const,
    items_before: r#"
entry {
    path: "subdir/file-2.png",
    has_data: false,
    sprites: {
        coolSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 3},
    },
}
entry {
    path: "subdir/file-3.png",
    has_data: false,
    sprites: {
        coolSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 3 * I0},
    },
}
    "#,
    main_body: "",
    expected: "const",
);

#[test]
fn const_using_sprite_id() {
    let format = ANM_12;
    let source = TestFile::from_content("input", r#"
#pragma mapfile "map/any.anmm"
#pragma image_source "tests/integration/resources/th12-embedded-image-source.anm"

entry {
    path: "lmao.png",
    has_data: false,
    sprites: {
        sprite0: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 10},
    },
}

const int B = sprite0;

script script0 {
    ins_3(B);
}
    "#);
    let anm = format.compile(&source).read_anm(&format);
    assert_eq!(anm.entries[0].scripts[0].instrs[0].args_blob, vec![10, 0, 0, 0])
}

#[test]
fn sprite_id_using_const() {
    let format = ANM_12;
    let source = TestFile::from_content("input", r#"
#pragma mapfile "map/any.anmm"
#pragma image_source "tests/integration/resources/th12-embedded-image-source.anm"

entry {
    path: "lmao.png",
    has_data: false,
    sprites: {
        sprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: B},
    },
}

const int B = 10;

script script0 {
    ins_3(sprite);
}
    "#);
    let anm = format.compile(&source).read_anm(&format);
    assert_eq!(anm.entries[0].scripts[0].instrs[0].args_blob, vec![10, 0, 0, 0])
}

#[test]
fn const_shadows_sprite_id() {
    let format = ANM_12;
    let source = TestFile::from_content("input", r#"
#pragma mapfile "map/any.anmm"
#pragma image_source "tests/integration/resources/th12-embedded-image-source.anm"

entry {
    path: "lmao.png",
    has_data: false,
    sprites: {
        B: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 42},
        C: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: B + 2},
    },
}

const int B = 10;

script script0 {
    ins_3(B);
}
    "#);
    let anm = format.compile(&source).read_anm(&format);
    assert_eq!(anm.entries[0].sprites[0].id, Some(42));
    assert_eq!(anm.entries[0].sprites[1].id, Some(12));
    assert_eq!(anm.entries[0].scripts[0].instrs[0].args_blob, vec![10, 0, 0, 0])
}


// =============================================================================

#[test]
fn thecl_defs() {
    let format = &ANM_12;
    let thecl_defs = TestFile::new_temp("thecl defs output");
    format.compile_with_args(&TestFile::from_content("input", r#"
#pragma image_source "./tests/integration/resources/th12-multiple-match-source.anm"

entry {
    path: "subdir/file1.png",
    has_data: false,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 40.0, h: 60.0}},
}

script -45 hello {}

script there {}

entry {
    path: "subdir/file2.png",
    has_data: false,
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
