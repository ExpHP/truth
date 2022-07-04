#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

source_test!(
    ECL_06, basic,
    main_body: r#"
    0: nop();
    +20: nop();
    +30: nop();
    10: nop();
    +20: nop();
    +-15: nop();
"#,
    check_compiled: |output, format| {
        let ecl = output.read_olde_ecl(format);
        assert_eq!(ecl.subs[0][0].time, 0);
        assert_eq!(ecl.subs[0][1].time, 20);
        assert_eq!(ecl.subs[0][2].time, 50);
        assert_eq!(ecl.subs[0][3].time, 10);
        assert_eq!(ecl.subs[0][4].time, 30);
        assert_eq!(ecl.subs[0][5].time, 15);
    },
);

source_test!(
    ECL_06, r#const,
    items: r#"
    const int BLOOP = 60;
"#,
    main_body: r#"
    70: nop();
    +BLOOP: nop();
"#,
    check_compiled: |output, format| {
        let ecl = output.read_olde_ecl(format);
        assert_eq!(ecl.subs[0][0].time, 70);
        assert_eq!(ecl.subs[0][1].time, 130);
    },
);

source_test!(
    ECL_06, non_const,
    main_body: r#"
    70: nop();
    +I0: nop();  //~ ERROR const
"#,
);

source_test!(
    ECL_06, overflow,
    items: r#"
    const int BLOOP = 60;
"#,
    main_body: r#"
    +0x70000000: nop();
    +0x70000000: nop();
    +0x70000000: nop();
"#,
    check_compiled: |output, format| {
        let ecl = output.read_olde_ecl(format);
        assert_eq!(ecl.subs[0][0].time, 0x7000_0000);
        assert_eq!(ecl.subs[0][1].time, 0xe000_0000_u32 as i32);
        assert_eq!(ecl.subs[0][2].time, 0x5000_0000);
    },
);
