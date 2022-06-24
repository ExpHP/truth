#[allow(unused)]
use crate::integration_impl::{expected, formats::*, Format};

const FORMAT_WITH_GT_JMP: Format = ECL_08;
const FORMAT_WITH_NE_JMP: Format = ANM_12;

source_test!(
    FORMAT_WITH_NE_JMP, ne_jmp_can_roundtrip,
    main_body: r#"
        label:
            if (--I2) goto label;
    "#,
    check_decompiled: |decompiled| { assert!(decompiled.contains("(--$REG[10002])")); },
);

source_test!(
    FORMAT_WITH_GT_JMP, gt_jmp_can_roundtrip,
    main_body: r#"
        label:
            if (--I2 > 0) goto label;
    "#,
    check_decompiled: |decompiled| { assert!(decompiled.contains("(--$REG[10002] > 0)")); },
);

source_test!(
    FORMAT_WITH_GT_JMP, ne_jmp_can_suggest_gt,
    main_body: r#"
        label:
            if (--I2) goto label;  //~ ERROR (--I2 > 0)
    "#,
);

source_test!(
    FORMAT_WITH_NE_JMP, gt_jmp_can_suggest_ne,
    main_body: r#"
        label:
            if (--I2 > 0) goto label;  //~ ERROR (--I2)
    "#,
);

source_test!(
    FORMAT_WITH_NE_JMP, ne_format_can_compile_times,
    main_body: r#"
        times(I2=5) { nop(); }
    "#,
    check_compiled: |_, _| { /* just compile */ },
);

source_test!(
    FORMAT_WITH_GT_JMP, gt_format_can_compile_times,
    main_body: r#"
        times(I2=5) { nop(); }
    "#,
    check_compiled: |_, _| { /* just compile */ },
);
