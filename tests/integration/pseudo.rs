#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

source_test!(
    ANM_10, pseudo_blob,
    // This tests that a user provided @mask overrides the one that gets automatically computed.
    main_body: r#"
        anchor(@blob="01000200");
    "#,
    check_decompiled: |decompiled| {
        assert!(decompiled.contains("(1, 2)"));  // turned into words
    },
);

source_test!(
    ANM_10, pseudo_mask_override,
    // This tests that a user provided @mask overrides the one that gets automatically computed.
    main_body: r#"
        color(@mask=0b100, I2, 10, 20);
    "#,
    check_decompiled: |decompiled| {
        assert!(decompiled.contains("[20]"));  // turned into reg
        assert!(decompiled.contains("10002,"));  // turned into immediate
    },
);

source_test!(
    ANM_10, pseudo_in_const_call,
    items: r#"
        const int foo(int x) { return x; }
    "#,
    main_body: r#"
        int x = foo(@mask=0b1, 12);
    "#,
    expect_error: "not an instruction",
);

source_test!(
    ANM_10, pseudo_in_inline_call,
    items: r#"
        inline void foo(int x) { wait(x); }
    "#,
    main_body: r#"
        foo(@mask=0b1, 12);
    "#,
    expect_error: "not an instruction",
);

source_test!(
    ANM_10, pseudo_after_arg,
    main_body: r#"
        wait(12, @mask=0b1);
    "#,
    expect_error: "before",
);

source_test!(
    ANM_10, pseudo_blob_with_arg,
    main_body: r#"
        wait(@blob="0f000000", 15);
    "#,
    expect_error: "redundant",
);

source_test!(
    ANM_10, pseudo_bad_name,
    main_body: r#"
        wait(@blobloblob="0f000000");
    "#,
    expect_error: "pseudo",
);

source_test!(
    ANM_10, pseudo_len_ndiv_4,
    main_body: r#"
        wait(@blob="0f0000");
    "#,
    expect_error: "by 4",
);

source_test!(
    ANM_10, pseudo_dupe,
    main_body: r#"
        wait(@blob="0f000000", @blob="0f000000");
    "#,
    expect_error: "duplicate",
);

source_test!(
    ANM_10, pseudo_non_const,
    main_body: r#"
        I0 = 1;
        wait(@mask=I0, @blob="10270000");
    "#,
    expect_error: "const",
);
