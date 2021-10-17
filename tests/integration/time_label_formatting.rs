use crate::integration_impl::formats::*;

source_test!(
    ECL_08, general_1,
    main_body: r#"
    0: dummy();
    2: dummy();
    5: dummy();
"#,
    sbsb: |decompiled| {
        assert!(!decompiled.contains("\n0:"));  // suppress initial 0 label
        assert!(decompiled.contains("\n+2:"));  // prefer relative labels
        assert_snapshot!(decompiled)
    },
);

source_test!(
    ECL_08, general_2,
    main_body: r#"
    5: dummy();
    3: dummy();
    0: dummy();
"#,
    sbsb: |decompiled| {
        assert!(decompiled.contains("5:"));  // nonzero beginning, don't care if rel or absolute
        assert!(decompiled.contains("\n3:"));  // decreased label
        assert!(decompiled.contains("\n0:"));  // explicit zero label
        assert_snapshot!(decompiled)
    },
);

source_test!(
    ECL_08, after_neg,
    // negative label followed by 0 or positive.
    main_body: r#"
    -1: dummy();
    0: dummy();
    -1: dummy();
    6: dummy();
"#,
    sbsb: |decompiled| {
        assert_eq!(decompiled.matches("\n-1:").count(), 2);
        assert_eq!(decompiled.matches("\n0:").count(), 2);  // the "6:" should become "0: +6"
        assert_eq!(decompiled.matches("\n+6:").count(), 1);
        assert_snapshot!(decompiled)
    },
);

source_test!(
    ECL_08, compression,
    // compression of identical time labels, regardless of sign
    main_body: r#"
    0: dummy(); dummy();
    6: dummy(); dummy();
    -1: dummy(); dummy();
"#,
    sbsb: |decompiled| {
        assert_eq!(decompiled.matches(":").count(), 2);
        assert_snapshot!(decompiled);
    },
);
