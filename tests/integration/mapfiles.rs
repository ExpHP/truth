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

#[test]
fn missing_test() {
    panic!(
        "test of user mapfile that sets an existing instruction as an \
        incorrect intrinsic but doesn't set a signature (so it has no span/uses \
        the core mapfile)"
    )
}


#[test]
fn missing_test_2() {
    panic!(
        "test of user mapfile that sets a instruction as an \
        intrinsic which has no signature"
    )
}
