#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

source_test!(
    ECL_07, show_instr_offsets,
    // FIXME stolen test
    items: r#"
void neither() {}
void anInt(int a) {}
void twoInts(int a, int b) {}
void aFloat(float a) {}
void mixed(int a, int b, float x, int c, float y) {}
"#,
    main_body: r#"
    neither();
    anInt(7);
    twoInts(2, 4);
    aFloat(4.0);
    mixed(2, I0, 2.0, 7, F0);
    "#,
    check_decompiled: |decompiled| {
        assert!(decompiled.contains("();"));
        assert!(decompiled.contains("(7);"));
        assert!(decompiled.contains("(2, 4);"));
        assert!(decompiled.contains("(4.0);"));
        assert!(decompiled.contains(" 2.0, ")); // check for a big argument list
    },
);
