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
#[ignore]
fn missing_test() {
    panic!(
        "test of user mapfile that sets an existing instruction as an \
        incorrect intrinsic but doesn't set a signature (so it has no span/uses \
        the core mapfile)"
    )
}


#[test]
#[ignore]
fn missing_test_2() {
    panic!(
        "test of user mapfile that sets a instruction as an \
        intrinsic which has no signature"
    )
}


#[test]
#[ignore]
fn missing_test_3() {
    panic!(
        "test of user mapfile that has wrong num args for intrinsic and also \
        a binary file with that number of arguments"
    )
}
