#[allow(unused)]
use crate::integration_impl::{expected, formats::*};
use crate::integration_impl::TestFile;

// =============================================================================

source_test!(
    ANM_16, anti_scratch_bad_in_func,
    items: r#"
    script grandparent {
        F2 = 1.0;
        scriptNew(parent);
    +100:
        nop();
    }

    script parent {
        // Even though this sub has no mention of F2, it is NOT safe to
        // use it for scratch purposes.
        F3 = (F0 + 1.0) * ((F0 + 2.0) * (F0 + 3.0));
        copyVars();
        scriptNew(child);
    +100:
        nop();
    }

    script child {
        copyVars();
        F0 = F2;  // this uses the value of F2 set in grandparent
    }
"#,
    expect_error: "scratch registers are disabled",
);

source_test!(
    ANM_16, anti_scratch_okay_in_other_func,
    items: r#"
    script grandparent {
        // using F2 is okay here, we don't call copyParentVars
        F3 = (F0 + 1.0) * ((F0 + 2.0) * (F0 + 3.0));
        scriptNew(parent);
    +100:
        nop();
    }

    script parent {
        copyVars();
    }
"#,
    check_compiled: |_, _| {},
);

// =============================================================================

source_test!(
    // KNOWN FAILURE:
    //    Truth currently silently miscompiles this. :(
    #[ignore]
    ANM_06, eosd_anm_explicit_jump_at_time,
    main_body: r#"
    label:
        goto label @ 100;
"#,
    expect_error: expected::NOT_SUPPORTED_BY_FORMAT,
);

source_test!(
    // KNOWN FAILURE:
    //    Truth currently silently miscompiles this. :(
    #[ignore]
    ANM_06, eosd_anm_evil_jump_at_prev_time,
    // This test *implicitly* creates a jump whose time argument does not match the
    // time of the instruction at that offset. This cannot be represented in EoSD ANM!
    main_body: r#"
        nop();
        loop {
    +10:
            nop();
        }
"#,
    expect_error: "try inserting a nop before",
);

// =============================================================================

// NOTE: This isn't a source test because it reads the contents of --output-thecl-defs.
#[test]
fn thecl_defs() {
    let format = &ANM_12;
    let thecl_defs = TestFile::new_temp("thecl defs output");
    format.compile(&TestFile::from_content("input", r#"
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
    "#), &["--output-thecl-defs".as_ref(), thecl_defs.as_path().as_ref()], &[]);

    let actual = thecl_defs.read_to_string();
    let expected = r#"
global hello = 0;
global there = 1;
global howyado = 2;
    "#;
    assert_eq!(actual.trim(), expected.trim());
}
