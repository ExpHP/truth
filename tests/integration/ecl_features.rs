use crate::integration_impl::{expected, formats::*};

source_test!(
    ECL_08, wrong_lang,
    full_source: r#"
timeline 0 {
    eclOnly(0, 3, 3);
}

void sub0 {
    timelineOnly(0, 3, 3);
}
"#,
    expect_fail: expected::UNIMPLEMENTED,
    // expect_fail: "there is a ECL Timeline",
);
