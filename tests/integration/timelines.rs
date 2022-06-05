#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

const TIMELINE_DEBUGGING_ECLMAP: &'static str = r#"!eclmap
!timeline_ins_signatures
10 S
"#;

source_test!(
    ECL_08, auto_indices,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
timeline { ins_10(100); }
timeline { ins_10(200); }
timeline { ins_10(300); }
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.timelines[0][0].args_blob, blobify![100]);
        assert_eq!(ecl.timelines[1][0].args_blob, blobify![200]);
        assert_eq!(ecl.timelines[2][0].args_blob, blobify![300]);
    },
);

source_test!(
    ECL_08, explicit_indices,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
timeline 2 { ins_10(300); }
timeline 0 { ins_10(100); }
timeline 1 { ins_10(200); }
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.timelines[0][0].args_blob, blobify![100]);
        assert_eq!(ecl.timelines[1][0].args_blob, blobify![200]);
        assert_eq!(ecl.timelines[2][0].args_blob, blobify![300]);
    },
);

source_test!(
    ECL_08, named,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
timeline timeA { }
timeline timeB { }
"#,
    check_compiled: |_, _| {
        // just check that it succeeds
    },
);

source_test!(
    ECL_08, mixture_of_auto_and_explicit,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
timeline 2 { ins_10(300); }  //~ WARNING explicit
timeline { ins_10(100); }
timeline { ins_10(200); }
"#,
    check_compiled: |output, format| {
        let ecl = output.read_ecl(format);
        assert_eq!(ecl.timelines[0][0].args_blob, blobify![100]);
        assert_eq!(ecl.timelines[1][0].args_blob, blobify![200]);
        assert_eq!(ecl.timelines[2][0].args_blob, blobify![300]);
    },
);

source_test!(
    ECL_08, negative,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
timeline -1 { }  //~ ERROR negative
timeline -2 { }  //~ ERROR negative
"#,
);

source_test!(
    ECL_08, missing,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
timeline 3 { }
timeline 4 { }  //~ ERROR missing
timeline 0 { }
"#,
);

source_test!(
    ECL_08, duplicate,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
timeline 0 { ins_10(100); }
timeline 0 { ins_10(200); }  //~ ERROR redefin
"#,
);

source_test!(
    ECL_08, duplicate_implicit,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
timeline 0 { ins_10(100); }  //~ WARNING explicit
timeline { ins_10(100); }  //~ ERROR redefin
"#,
);

source_test!(
    ECL_06, too_many_6,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
timeline { ins_10(100); }
timeline { ins_10(100); }
"#,
    expect_error: "too many timelines",
);

source_test!(
    ECL_07, too_many_7,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
timeline { ins_10(100); }
timeline { ins_10(100); }
timeline { ins_10(100); }
timeline { ins_10(100); }

timeline { ins_10(100); }
timeline { ins_10(100); }
timeline { ins_10(100); }
timeline { ins_10(100); }

timeline { ins_10(100); }
timeline { ins_10(100); }
timeline { ins_10(100); }
timeline { ins_10(100); }

timeline { ins_10(100); }
timeline { ins_10(100); }
timeline { ins_10(100); }
timeline { ins_10(100); }
"#,
    expect_error: "too many timelines",
);

