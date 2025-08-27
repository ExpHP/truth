#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

// =============================================================================
// Image sources

source_test!(
    STD_08, bad_object_name,
    full_source: r#"
#pragma mapfile "map/any.anmm"

meta {
    unknown: 0,
    stage_name: "dm",
    bgm: [
        {path: "bgm/th08_08.mid", name: "dm"},
        {path: "bgm/th08_09.mid", name: "dm"},
        {path: " ", name: " "},
        {path: " ", name: " "},
    ],
    objects: {
        blurb: {
            layer: 0,
            pos: [-320.0, -128.0, -12.0],
            size: [768.0, 384.0, 0.0],
            quads: [rect {anm_script: 0, pos: [-64.0, 0.0, -12.0], size: [512.0, 256.0]}],
        },
        blorb: {
            layer: 1,
            pos: [-81.602196, -140.91132, -425.6022],
            size: [531.2044, 505.268, 571.2044],
            quads: [rect {anm_script: 2, pos: [64.0, 224.0, -64.0], size: [112.0, 96.0]}],
        },
    },
    instances: [
        blurb {pos: [-192.0, 6600.0, 0.0]},
        blorb {pos: [320.0, 4296.0, 0.0]},
        blarb {pos: [-192.0, 6344.0, 0.0]},   //~ ERROR no object named
        blorb {pos: [320.0, 4296.0, 0.0]},
    ],
}

script main {}
"#,
);

source_test!(
    STD_12, strip_in_bad_game,
    full_source: r#"
#pragma mapfile "map/any.anmm"

meta {
    unknown: 0,
    anm_path: "stage01.anm",
    objects: {
        thing: {
            layer: 0,
            pos: [-320.0, -128.0, -12.0],
            size: [768.0, 384.0, 0.0],
            quads: [
                rect {anm_script: 0, pos: [-64.0, 0.0, -12.0], size: [512.0, 256.0]},
                strip {
                    anm_script: 1,
                    start: [218.0, 192.0, 0.0],
                    end: [268.0, 192.0, -280.0],
                    width: 5.0,
                }
            ],
        },
    },
    instances: [
        thing {pos: [-192.0, 6600.0, 0.0]},
    ],
}

script main {}
"#,
    expect_warning: "TH08 and TH09",
);

source_test!(
    STD_12, renamed_layer_old_unknown,
    full_source: r#"
#pragma mapfile "map/any.anmm"

meta {
    unknown: 0,
    anm_path: "stage01.anm",
    objects: {
        thing: {
            unknown: 3,  // <--- old name, not yet deprecated
            pos: [10.0, 20.0, 30.0],
            size: [10.0, 20.0, 30.0],
            quads: [],
        },
    },
    instances: [],
}

script main {}
"#,
    check_compiled: |_, _| {},
);

source_test!(
    STD_12, renamed_layer_missing,
    full_source: r#"
#pragma mapfile "map/any.anmm"

meta {
    unknown: 0,
    anm_path: "stage01.anm",
    objects: {
        thing: {                     //~ ERROR 'layer'
            pos: [10.0, 20.0, 30.0],
            size: [10.0, 20.0, 30.0],
            quads: [],
        },
    },
    instances: [],
}

script main {}
"#,
);

source_test!(
    STD_12, renamed_layer_conflict,
    full_source: r#"
#pragma mapfile "map/any.anmm"

meta {
    unknown: 0,
    anm_path: "stage01.anm",
    objects: {
        thing: {
            unknown: 3,   //~ ERROR both 'unknown' and 'layer'
            layer: 4,
            pos: [10.0, 20.0, 30.0],
            size: [10.0, 20.0, 30.0],
            quads: [],
        },
    },
    instances: [],
}

script main {}
"#,
);

source_test!(
    STD_08, intrinsic_padding,
    main_body: r#"
blah:
    up(0.0, 0.0, 0.0);
blah2:
    // both of these are "jmp blah @ timeof(blah)"
    ins_4(@blob="00000000 00000000 50000000");  // garbage padding
    ins_4(@blob="00000000 00000000 00000000");
"#,

    // FIXME: would like this to roundtrip as blob instead of warning
    expect_decompile_warning: "nonzero data found in padding",
    require_roundtrip: false,
    check_decompiled: |decompiled| {
        // FIXME:  Check for blob once this decompiles to have blob

        // specificity: double check that this instruction is indeed the jump intrinsic
        //  by making sure the second one decompiled.
        assert!(decompiled.contains("loop {"));
    },
);
