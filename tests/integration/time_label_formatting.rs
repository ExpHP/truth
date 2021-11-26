#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

source_test!(
    ECL_06, general_1,
    main_body: r#"
    0: nop();
    2: nop();
    5: nop();
"#,
    check_decompiled: |decompiled| {
        assert!(!decompiled.contains("\n0:"));  // suppress initial 0 label
        assert!(decompiled.contains("\n+2:"));  // prefer relative labels
        assert_snapshot!(decompiled)
    },
);

source_test!(
    ECL_06, general_2,
    main_body: r#"
    5: nop();
    3: nop();
    0: nop();
"#,
    check_decompiled: |decompiled| {
        assert!(decompiled.contains("5:"));  // nonzero beginning, don't care if rel or absolute
        assert!(decompiled.contains("\n3:"));  // decreased label
        assert!(decompiled.contains("\n0:"));  // explicit zero label
        assert_snapshot!(decompiled)
    },
);

source_test!(
    ECL_06, after_neg,
    // negative label followed by 0 or positive.
    main_body: r#"
    -1: nop();
    0: nop();
    -1: nop();
    6: nop();
"#,
    check_decompiled: |decompiled| {
        assert_eq!(decompiled.matches("\n-1:").count(), 2);
        assert_eq!(decompiled.matches("\n0:").count(), 2);  // the "6:" should become "0: +6"
        assert_eq!(decompiled.matches("\n+6:").count(), 1);
        assert_snapshot!(decompiled)
    },
);

source_test!(
    ECL_06, neg_neg,
    // increasing or decreasing negative labels
    main_body: r#"
    -1: nop();
    -2: nop();
    -1: nop();
"#,
    check_decompiled: |_decompiled| {
        // mostly just care that the output is correct, this never shows up in practice
    },
);

source_test!(
    ECL_06, compression,
    // compression of identical time labels, regardless of sign
    main_body: r#"
    0: nop(); nop();
    6: nop(); nop();
    -1: nop(); nop();
"#,
    check_decompiled: |decompiled| {
        assert_eq!(decompiled.matches(":").count(), 2);
        assert_snapshot!(decompiled);
    },
);
