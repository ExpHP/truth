#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

source_test!(
    ECL_08, ne_jmp_can_suggest_gt,
    main_body: r#"
        label:
            if (--I2) goto label;  //~ ERROR (--I2 > 0)
    "#,
);

source_test!(
    ANM_12, gt_jmp_can_suggest_ne,
    main_body: r#"
        label:
            if (--I2 > 0) goto label;  //~ ERROR (--I2)
    "#,
);
