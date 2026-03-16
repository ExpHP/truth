#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

source_test!(
    ECL_07, no_block_with_instr_offsets,
    main_body: r#"
    loop {
    }
    "#,
    decompile_args: &["--show-instr-offsets"],
    check_decompiled: |decompiled| {
        assert!(decompiled.contains("goto"));
    },
);

source_test!(
    ECL_07, no_diffswitch_with_instr_offsets,
    main_body: r#"
    // This should decompile into TWO separate instructions.
    I0 = (2::4:);
    "#,
    mapfile: "!eclmap
!difficulty_flags
0  E-
1  N-
2  H-
3  L-
",
    decompile_args: &["--show-instr-offsets"],
    check_decompiled: |decompiled| {
        // should have assignments and diff LABELS (not a diff SWITCH)
        assert!(decompiled.contains("= 2;"));
        assert!(decompiled.contains("= 4;"));
        assert!(decompiled.contains(r##"{"EN"}: "##));
        assert_snapshot!(decompiled)
    },
);

source_test!(
    ECL_07, no_call_with_instr_offsets,
    items: r#"
void twoInts(int a, int b) {}
"#,
    main_body: r#"
    // This should decompile into THREE separate instructions.
    twoInts(2, 4);
    "#,
    decompile_args: &["--show-instr-offsets"],
    check_decompiled: |decompiled| {
        // should have assignment and a call instruction
        assert!(decompiled.contains("= 2;"));
        assert!(decompiled.contains("ins_41(sub0);"));
        assert_snapshot!(decompiled)
    },
);
