use crate::integration_impl::formats::*;

// =============================================================================
// Image sources

source_test!(
    MSG_06, empty,
    full_source: r#"
meta {
    table: {},
}
"#,
    check_compiled: |_, _| {
        let msg = output.read_msg(format);
        assert_eq!(msg.scripts.len(), 0);
        assert_eq!(msg.script_table.table_len, 0);
    },
);

source_test!(
    MSG_06, default_table_len,
    full_source: r#"
meta {
    table: {
        0: {script: script0},
        10: {script: script10},
        11: {script: script10},
        default: {script: script0},
    },
}

script script0 {}
script script10 {}
"#,
    check_compiled: |_, _| {
        let msg = output.read_msg(format);
        assert_eq!(msg.scripts.len(), 2);  // 0 and 10
        assert_eq!(msg.script_table.table.len(), 3);  // 0, 10, 11
        assert_eq!(msg.script_table.table_len, 12);
    },
);


source_test!(
    MSG_06, integer_meta_key_normalization,
    full_source: r#"
meta {
    table_len: 2,
    table: {
        0: {script: script0},
        1: {script: script0},
        0x0: {script: script0},
    },
}

script script0 {}
"#,
    expect_fail: "duplicate",
);
