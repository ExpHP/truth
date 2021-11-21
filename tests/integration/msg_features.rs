#[allow(unused)]
use crate::integration_impl::{expected, formats::*};
use truth::ast::meta::ToMeta;

source_test!(
    MSG_06, empty,
    full_source: r#"
meta {
    table: {},
}
"#,
    check_compiled: |output, format| {
        let msg = output.read_msg(format);
        assert_eq!(msg.scripts.len(), 0);
        assert_eq!(msg.dense_table.len(), 0);
    },
);

source_test!(
    MSG_06, default_table_len,
    full_source: r#"
meta {
    table: {
        0: {script: "script0"},
        10: {script: "script10"},
        11: {script: "script10"},
        default: {script: "script0"},
    },
}

script script0 {}
script script10 {}
"#,
    check_compiled: |output, format| {
        let msg = output.read_msg(format);
        assert_eq!(msg.scripts.len(), 2);
        assert_eq!(msg.dense_table.len(), 12);
    },
);

source_test!(
    MSG_06, table_default,
    full_source: r#"
meta {
    table_len: 15,
    table: {
        0: {script: "script0"},
        10: {script: "script10"},
        11: {script: "script10"},
        default: {script: "script0"},
    },
}

script script0 {}
script script10 {}
"#,
    check_compiled: |output, format| {
        let msg = output.read_msg(format);
        assert_eq!(msg.dense_table.len(), 15);
        assert_eq!(msg.dense_table[3].script.value.to_meta(), "script0".to_meta());
        assert_eq!(msg.dense_table[10].script.value.to_meta(), "script10".to_meta());
        assert_eq!(msg.dense_table[11].script.value.to_meta(), "script10".to_meta());
        assert_eq!(msg.dense_table[13].script.value.to_meta(), "script0".to_meta());
    },
);

source_test!(
    MSG_06, duplicate_script,
    full_source: r#"
meta {
    table: {
        0: {script: "script0"},
    },
}

script script0 {}
script script0 {}
"#,
    expect_error: "redefinition",
);


source_test!(
    MSG_06, dense_table_doesnt_require_default,
    full_source: r#"
meta {
    table: {
        0: {script: "script0"},
        1: {script: "script1"},
        3: {script: "script3"},
        2: {script: "script2"},
    },
}

script script2 {}
script script3 {}
script script0 {}
script script1 {}
"#,
    check_compiled: |output, format| {
        let msg = output.read_msg(format);
        assert_eq!(msg.scripts.len(), 4);
        assert_eq!(msg.dense_table.len(), 4);
        assert_eq!(msg.dense_table[2].script.value.to_meta(), "script2".to_meta());
        assert_eq!(msg.dense_table[3].script.value.to_meta(), "script3".to_meta());
    },
);

source_test!(
    MSG_06, table_len_too_short,
    full_source: r#"
meta {
    table_len: 1,
    table: {
        0: {script: "script0"},
        1: {script: "script1"},
        2: {script: "script2"},
        3: {script: "script2"},
    },
}

script script2 {}
script script0 {}
script script1 {}
"#,
    expect_warning: "unused table entry",
);

source_test!(
    MSG_06, integer_meta_key_normalization,
    full_source: r#"
meta {
    table_len: 2,
    table: {
        0: {script: "script0"},
        1: {script: "script0"},
        0x0: {script: "script0"},
    },
}

script script0 {}
"#,
    expect_error: "duplicate",
);

source_test!(
    MSG_06, unused_script,
    full_source: r#"
meta {
    table_len: 1,
    table: {
        0: {script: "script0"},
    },
}

script script0 {}
script foo {}
"#,
    expect_warning: "unused script 'foo'",
);

source_test!(
    MSG_06, dedicated_default,
    full_source: r#"
meta {
    table_len: 2,
    table: {
        0: {script: "script0"},
        default: {script: "theDefault"},
    },
}

script script0 {}
script theDefault {}
"#,
    // we're mostly checking that there's no warning
    check_compiled: |_, _| {},
);

source_test!(
    MSG_06, unused_default_script,
    full_source: r#"
meta {
    table_len: 1,
    table: {
        0: {script: "script0"},
        default: {script: "theDefault"},
    },
}

script script0 {}
script theDefault {}
"#,
    // This table is dense, so the default is unused.
    //
    // However, users might want an "error" script as a default, and so it
    // shouldn't matter that the default is never used.
    // Hence we're mostly just checking that there's no warning here.
    check_compiled: |_, _| {},
);
