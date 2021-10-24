use crate::integration_impl::formats::*;

source_test!(
    MSG_06, bad_mapfile_item,
    mapfile: r#"!anmmap
!ins_signatures
300 oott
"#,
    main_body: r#""#,
    expect_error: "JIS",
);
