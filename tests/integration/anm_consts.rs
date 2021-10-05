use crate::integration_impl::formats::*;
use crate::integration_impl::{TestFile, expected};

// This is the first written test of const vars that depend on other const vars.
// (sprite IDs were the first const vars implemented in the compiler, even before
//  const var items!)
source_test!(
    ANM_12, sprite_ids_gone_wild,
    full_source: r#"
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
    "#,
    check_compiled: |output, format| {
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
    has_data: false,
    sprites: {
        coolSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: bestSprite * 3},
        bestSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: coolestSprite * 3},
        coolestSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: coolSprite + 1},
    },
}
    "#,
    expect_error: "depends on its own value",
);

source_test!(
    ANM_10, meta_non_const,
    items: r#"
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
    // NOTE: be careful changing this.  If the new error complains about missing fields
    // or missing image data, fix the test input instead.
    expect_error: "const",
);

// It is okay for two sprites to have the same name (this occurs in decompiled output),
// but they must also have the same ID.
source_test!(
    ANM_12, sprite_ids_dupe,
    full_source: r#"
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
    "#,
    check_compiled: |output, format| {
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
    "#,
    check_compiled: |output, format| {
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
    expect_error: "ambiguous"
);

// Same but one's implicit.
source_test!(
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
    expect_error: "ambiguous"
);

// Type-checking/const-checking sprite IDs is actually a bit annoying.
source_test!(
    ANM_10, meta_sprite_id_type_error,
    items: r#"
entry {
    path: "subdir/file-2.png",
    has_data: false,
    sprites: {
        coolSprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 3.5},
    },
}
    "#,
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, meta_sprite_id_non_const,
    items: r#"
entry {
    path: "subdir/file-2.png",
    has_data: false,
    sprites: {
        sprite200: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 3 * I0},
    },
}
    "#,
    expect_error: "const",
);

// Dupes may follow different code paths for type checking and const checking since
// the expressions are never used beyond checking equality to the originals.
source_test!(
    ANM_10, meta_sprite_id_dupe_type_error,
    items: r#"
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
    expect_error: expected::TYPE_ERROR,
);

source_test!(
    ANM_10, meta_sprite_id_dupe_non_const,
    items: r#"
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
    expect_error: "const",
);

source_test!(
    ANM_12, const_using_sprite_id,
    full_source: r#"
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
    "#,
    check_compiled: |output, format| {
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
    has_data: false,
    sprites: {
        sprite: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: B},
    },
}

const int B = 10;

script script0 {
    ins_3(sprite);
}
    "#,
    check_compiled: |output, format| {
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
    "#,
    check_compiled: |output, format| {
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
    has_data: false,
    sprites: {
        sprite0: {x: POS_X, y: 0.0, w: 512.0, h: 480.0},
        sprite1: {x: POS_X + 3.0, y: 0.0, w: 512.0, h: 480.0},
    },
}

const float POS_X = 20.0;

script script0 {}
    "#,
    check_compiled: |output, format| {
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
    has_data: false,
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
    expect_error: "ambiguous",
);

source_test!(
    ANM_12, sprite_shadows_reg_alias,
    full_source: r#"
#pragma mapfile "map/any.anmm"
#pragma image_source "tests/integration/resources/th12-embedded-image-source.anm"

entry {
    path: "lmao.png",
    has_data: false,
    sprites: {
        RAND: {x: 0.0, y: 0.0, w: 512.0, h: 480.0, id: 22 * 2 - 2},
    },
}

const int x = $RAND;

script 23 script23 {
    ins_3(x);
}
    "#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        assert_eq!(anm.entries[0].scripts[0].instrs[0].args_blob, vec![42, 0, 0, 0]);
    },
);

const SCRIPT_IDS_EXAMPLE: &'static str = r#"
#pragma mapfile "map/any.anmm"
#pragma image_source "./tests/integration/resources/th12-multiple-match-source.anm"

entry {
    path: "subdir/file1.png",
    has_data: false,
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
    has_data: false,
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
