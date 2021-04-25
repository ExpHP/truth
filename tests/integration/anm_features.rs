use crate::integration_impl::formats::*;
use crate::integration_impl::{TestFile, expected};

// =============================================================================
// Image sources

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
"#,
        check_compiled:|output, format| {
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
        check_compiled:|output, format| {
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
        check_compiled:|output, format| {
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
        check_compiled:|output, format| {
            assert!(output.read_anm(format).entries[0].texture.is_some());
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
    check_compiled:|output, format| {
        let anm = output.read_anm(format);
        assert_eq!(anm.entries[0].specs.width, Some(2000));  // pulled from file1
        assert_eq!(anm.entries[0].sprites[0].size, [111.0, 111.0]);
        assert_eq!(anm.entries[0].scripts[0].instrs[0].opcode, 1);
        assert_eq!(anm.entries[1].specs.width, Some(1000));  // pulled from file2
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
    check_compiled:|output, format| {
        let anm = output.read_anm(format);
        assert_eq!(anm.entries[0].specs.width, Some(1000));
        assert_eq!(anm.entries[0].sprites[0].size, [111.0, 111.0]);
        assert_eq!(anm.entries[0].scripts[0].instrs[0].opcode, 1);
        assert_eq!(anm.entries[1].specs.width, Some(2000));
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

// =============================================================================
// Sprite IDs

// This is the first written test of const vars that depend on other const vars.
// (sprite IDs were the first const vars implemented in the compiler, even before
//  const var items!)
source_test!(
    ANM_12, sprite_ids_gone_wild,
    full_source: r#"
#pragma image_source "./tests/integration/resources/th12-multiple-match-source.anm"

entry {
    path: "subdir/file1.png",
    source: "none",
    sprites: {
        valueA: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: valueC + 2 - valueC},
        valueB: {x: 0.0, y: 0.0, w: 0.0, h: 0.0},
        valueC: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: 26 * 2 + 1},
        valueD: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: valueE - 1},
    },
}

entry {
    path: "subdir/file2.png",
    source: "none",
    sprites: {
        valueE: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: 401},
        valueF: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: _S(%valueE + 2.4) + 1},
    },
}

script script0 {
    ins_1();
}
    "#,
    check_compiled:|output, format| {
        let anm = output.read_anm(format);
        assert_eq!(anm.entries[0].sprites[0].id, Some(2));
        assert_eq!(anm.entries[0].sprites[1].id, None);  // 3
        assert_eq!(anm.entries[0].sprites[2].id, Some(53));
        assert_eq!(anm.entries[0].sprites[3].id, Some(400));
        assert_eq!(anm.entries[1].sprites[0].id, None);  // 401
        assert_eq!(anm.entries[1].sprites[1].id, Some(404));
    },
);

source_test!(
    ANM_10, meta_sprite_id_circular_dependency,
    items: r#"
entry {
    path: "subdir/file-2.png",
    source: "none",
    sprites: {
        coolSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: bestSprite * 3},
        bestSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: coolestSprite * 3},
        coolestSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: coolSprite + 1},
    },
}
    "#,
    expect_fail: "depends on its own value",
);

source_test!(
    ANM_10, meta_non_const,
    items: r#"
entry {
    path: "subdir/file-2.png",
    source: "none",
    memory_priority: 3 * I0,
    low_res_scale: false,
    sprites: {
        sprite200: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 200},
    },
}
    "#,
    // NOTE: be careful changing this.  If the new error complains about missing fields
    // or missing image data, fix the test input instead.
    expect_fail: "const",
);

// It is okay for two sprites to have the same name (this occurs in decompiled output),
// but they must also have the same ID.
source_test!(
    ANM_12, sprite_ids_dupe,
    full_source: r#"
#pragma image_source "./tests/integration/resources/th12-multiple-match-source.anm"

entry {
    path: "subdir/file1.png",
    source: "none",
    sprites: {
        valueA: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: 26 * 2 + 1},
    },
}

entry {
    path: "subdir/file2.png",
    source: "none",
    sprites: {
        xyzzyx: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: 24},
        valueA: {x: 1.0, y: 1.0, w: 1.0, h: 1.0, id: 53},
    },
}

script script0 {
    ins_1();
}
    "#,
    check_compiled:|output, format| {
        let anm = output.read_anm(format);
        assert_eq!(anm.entries[0].sprites[0].id, Some(53));
        assert_eq!(anm.entries[1].sprites[0].id, Some(24));
        assert_eq!(anm.entries[1].sprites[1].id, Some(53));
    },
);

// same but one's implicit
source_test!(
    ANM_12, sprite_ids_dupe_implicit,
    full_source: r#"
#pragma image_source "./tests/integration/resources/th12-multiple-match-source.anm"

entry {
    path: "subdir/file1.png",
    source: "none",
    sprites: {
        valueA: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: 26 * 2 + 1},
    },
}

entry {
    path: "subdir/file2.png",
    source: "none",
    sprites: {
        xyzzyx: {x: 0.0, y: 0.0, w: 0.0, h: 0.0, id: 52},
        valueA: {x: 1.0, y: 1.0, w: 1.0, h: 1.0},   // dupe, but has same id as above
    },
}

script script0 {
    ins_1();
}
    "#,
    check_compiled:|output, format| {
        let anm = output.read_anm(format);
        assert_eq!(anm.entries[0].sprites[0].id, Some(53));
        assert_eq!(anm.entries[1].sprites[0].id, Some(52));
        assert_eq!(anm.entries[1].sprites[1].id, None);  // 53
    },
);

// Now they have mismatched IDs.
source_test!(
    ANM_12, err_sprite_clash,
    full_source: r#"
#pragma image_source "./tests/integration/resources/th12-multiple-match-source.anm"

entry {
    path: "subdir/file1.png",
    source: "none",
    sprites: {my_sprite: {x: 1.0, y: 1.0, w: 111.0, h: 111.0, id: 0}},
}

entry {
    path: "subdir/file2.png",
    source: "none",
    sprites: {my_sprite: {x: 2.0, y: 2.0, w: 222.0, h: 220.0, id: 1}},
}

script script0 {
    ins_1();
}
    "#,
    expect_fail: "ambiguous"
);

// Same but one's implicit.
source_test!(
    ANM_12, err_sprite_clash_implicit,
    full_source: r#"
#pragma image_source "./tests/integration/resources/th12-multiple-match-source.anm"

entry {
    path: "subdir/file1.png",
    source: "none",
    sprites: {my_sprite: {x: 1.0, y: 1.0, w: 111.0, h: 111.0, id: 1}},
}

entry {
    path: "subdir/file2.png",
    source: "none",
    sprites: {my_sprite: {x: 2.0, y: 2.0, w: 222.0, h: 220.0}},
}

script script0 {
    ins_1();
}
    "#,
    expect_fail: "ambiguous"
);

// Type-checking/const-checking sprite IDs is actually a bit annoying.
source_test!(
    ANM_10, meta_sprite_id_type_error,
    items: r#"
entry {
    path: "subdir/file-2.png",
    source: "none",
    sprites: {
        coolSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 3.5},
    },
}
    "#,
    expect_fail: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, meta_sprite_id_non_const,
    items: r#"
entry {
    path: "subdir/file-2.png",
    source: "none",
    sprites: {
        sprite200: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 3 * I0},
    },
}
    "#,
    expect_fail: "const",
);

// Dupes may follow different code paths for type checking and const checking since
// the expressions are never used beyond checking equality to the originals.
source_test!(
    ANM_10, meta_sprite_id_dupe_type_error,
    items: r#"
entry {
    path: "subdir/file-2.png",
    source: "none",
    sprites: {
        coolSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 3},
    },
}
entry {
    path: "subdir/file-3.png",
    source: "none",
    sprites: {
        coolSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 3.5},
    },
}
    "#,
    expect_fail: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, meta_sprite_id_dupe_non_const,
    items: r#"
entry {
    path: "subdir/file-2.png",
    source: "none",
    sprites: {
        coolSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 3},
    },
}
entry {
    path: "subdir/file-3.png",
    source: "none",
    sprites: {
        coolSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 3 * I0},
    },
}
    "#,
    expect_fail: "const",
);

source_test!(
    ANM_12, const_using_sprite_id,
    full_source: r#"
#pragma mapfile "map/any.anmm"
#pragma image_source "tests/integration/resources/th12-embedded-image-source.anm"

entry {
    path: "lmao.png",
    source: "none",
    sprites: {
        sprite0: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 10},
    },
}

const int B = sprite0;

script script0 {
    ins_3(B);
}
    "#,
    check_compiled:|output, format| {
        let anm = output.read_anm(format);
        assert_eq!(anm.entries[0].scripts[0].instrs[0].args_blob, vec![10, 0, 0, 0]);
    },
);

source_test!(
    ANM_12, sprite_id_using_const,
    full_source: r#"
#pragma mapfile "map/any.anmm"
#pragma image_source "tests/integration/resources/th12-embedded-image-source.anm"

entry {
    path: "lmao.png",
    source: "none",
    sprites: {
        sprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: B},
    },
}

const int B = 10;

script script0 {
    ins_3(sprite);
}
    "#,
    check_compiled:|output, format| {
        let anm = output.read_anm(format);
        assert_eq!(anm.entries[0].scripts[0].instrs[0].args_blob, vec![10, 0, 0, 0]);
    },
);

source_test!(
    ANM_12, const_shadows_sprite_id,
    full_source: r#"
#pragma mapfile "map/any.anmm"
#pragma image_source "tests/integration/resources/th12-embedded-image-source.anm"

entry {
    path: "lmao.png",
    source: "none",
    sprites: {
        B: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 42},
        C: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: B + 2},
    },
}

const int B = 10;

script script0 {
    ins_3(B);
}
    "#,
    check_compiled:|output, format| {
        let anm = output.read_anm(format);
        assert_eq!(anm.entries[0].sprites[0].id, Some(42));
        assert_eq!(anm.entries[0].sprites[1].id, Some(12));
        assert_eq!(anm.entries[0].scripts[0].instrs[0].args_blob, vec![10, 0, 0, 0]);
    },
);

source_test!(
    ANM_12, consts_in_various_other_meta,
    full_source: r#"
#pragma mapfile "map/any.anmm"
#pragma image_source "tests/integration/resources/th12-embedded-image-source.anm"

const string FILEPATH = "lmao.png";

entry {
    path: FILEPATH,
    source: "none",
    sprites: {
        sprite0: {x: POS_X, y: 0.0, w: 512.0, h: 480.0},
        sprite1: {x: POS_X + 3.0, y: 0.0, w: 512.0, h: 480.0},
    },
}

const float POS_X = 20.0;

script script0 {}
    "#,
    check_compiled:|output, format| {
        let anm = output.read_anm(format);
        assert_eq!(anm.entries[0].sprites[0].offset[0], 20.0);
        assert_eq!(anm.entries[0].sprites[1].offset[0], 23.0);
    },
);

source_test!(
    ANM_12, sprite_script_name_clash,
    full_source: r#"
#pragma mapfile "map/any.anmm"
#pragma image_source "tests/integration/resources/th12-embedded-image-source.anm"

entry {
    path: "lmao.png",
    source: "none",
    sprites: {
        wild: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 22 * 2 - 2},
    },
}

script 23 script23 {
    ins_3(-1);
}

script wild {  // should have ID 1
    ins_3(-1);
}
    "#,
    expect_fail: "ambiguous",
);

source_test!(
    ANM_12, sprite_shadows_reg_alias,
    full_source: r#"
#pragma mapfile "map/any.anmm"
#pragma image_source "tests/integration/resources/th12-embedded-image-source.anm"

entry {
    path: "lmao.png",
    source: "none",
    sprites: {
        RAND: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 22 * 2 - 2},
    },
}

const int x = $RAND;

script 23 script23 {
    ins_3(x);
}
    "#,
    check_compiled:|output, format| {
        let anm = output.read_anm(format);
        assert_eq!(anm.entries[0].scripts[0].instrs[0].args_blob, vec![42, 0, 0, 0]);
    },
);

const SCRIPT_IDS_EXAMPLE: &'static str = r#"
#pragma mapfile "map/any.anmm"
#pragma image_source "./tests/integration/resources/th12-multiple-match-source.anm"

entry {
    path: "subdir/file1.png",
    source: "none",
    sprites: {
        sprite0: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 0},
    },
}

script myScript {
    scriptNew(child);
}

script 24 irrelevant {}

entry {
    path: "subdir/file2.png",
    source: "none",
    sprites: {
        sprite1: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 1},
    },
}

script child {}

script 101 another {}
"#;

#[test]
fn script_ids() {
    let format = ANM_12;
    let source = TestFile::from_content("input", SCRIPT_IDS_EXAMPLE);
    let anm = format.compile(&source).read_anm(&format);

    assert_eq!(anm.entries[0].scripts[0].id, 0);
    assert_eq!(anm.entries[0].scripts[1].id, 24);
    assert_eq!(anm.entries[1].scripts[0].id, 25);
    assert_eq!(anm.entries[1].scripts[1].id, 101);
}

#[test]
fn scripts_as_consts() {
    let format = ANM_12;
    let source = TestFile::from_content("input", SCRIPT_IDS_EXAMPLE);
    let anm = format.compile(&source).read_anm(&format);

    // the value of the const should be the *index across all entries* (2), not the ID (25)
    assert_eq!(anm.entries[0].scripts[0].instrs[0].args_blob, vec![2, 0, 0, 0]);
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
