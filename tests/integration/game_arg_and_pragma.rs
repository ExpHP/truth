#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

source_test!(
    ANM_NOGAME, no_game_defined,
    main_body: r#""#,
    expect_error: "--game"
);

source_test!(
    ANM_NOGAME, pragma_game_conflict,
    items: r#"
#pragma game 6
#pragma game 10  //~ ERROR conflicting
    "#,
);

source_test!(
    ANM_NOGAME, cli_overrides_pragma,
    compile_args: &["-g", "7"],
    items: r#"
#pragma game 12
    "#,
    main_body: r#"
        // exists in th12 but not th07
        ins_300(0);  //~ ERROR signature
    "#,
);
