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
script foo { ins_10(100); }
script bar { ins_10(200); }
script baz { ins_10(300); }
"#,
    check_compiled: |output, format| {
        let ecl = output.read_olde_ecl(format);
        assert_eq!(ecl.timelines[0][0].args_blob, blobify![100]);
        assert_eq!(ecl.timelines[1][0].args_blob, blobify![200]);
        assert_eq!(ecl.timelines[2][0].args_blob, blobify![300]);
    },
);

source_test!(
    ECL_08, explicit_indices,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
script 2 foo { ins_10(300); }
script 0 bar { ins_10(100); }
script 1 baz { ins_10(200); }
"#,
    check_compiled: |output, format| {
        let ecl = output.read_olde_ecl(format);
        assert_eq!(ecl.timelines[0][0].args_blob, blobify![100]);
        assert_eq!(ecl.timelines[1][0].args_blob, blobify![200]);
        assert_eq!(ecl.timelines[2][0].args_blob, blobify![300]);
    },
);

source_test!(
    ECL_08, named,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
script timeA { }
script timeB { }
"#,
    check_compiled: |_, _| {
        // just check that it succeeds
    },
);

source_test!(
    ECL_08, mixture_of_auto_and_explicit,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
script 2 foo { ins_10(300); }  //~ WARNING explicit
script bar { ins_10(100); }
script baz { ins_10(200); }
"#,
    check_compiled: |output, format| {
        let ecl = output.read_olde_ecl(format);
        assert_eq!(ecl.timelines[0][0].args_blob, blobify![100]);
        assert_eq!(ecl.timelines[1][0].args_blob, blobify![200]);
        assert_eq!(ecl.timelines[2][0].args_blob, blobify![300]);
    },
);

source_test!(
    ECL_08, negative,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
script -1 foo { }  //~ ERROR negative
script -2 bar { }  //~ ERROR negative
"#,
);

source_test!(
    ECL_08, missing,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
script 3 foo { }
script 4 bar { }  //~ ERROR missing
script 0 baz { }
"#,
);

source_test!(
    ECL_08, duplicate,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
script 0 foo { ins_10(100); }
script 0 bar { ins_10(200); }  //~ ERROR redefin
"#,
);

source_test!(
    ECL_08, duplicate_implicit,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
script 0 foo { ins_10(100); }  //~ WARNING explicit
script bar { ins_10(100); }  //~ ERROR redefin
"#,
);

source_test!(
    ECL_06, too_many_6,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
script foo { ins_10(100); }
script bar { ins_10(100); }
"#,
    expect_error: "too many timelines",
);

source_test!(
    ECL_07, too_many_7,
    mapfile: TIMELINE_DEBUGGING_ECLMAP,
    full_source: r#"
script timeline00 { ins_10(100); }
script timeline01 { ins_10(100); }
script timeline02 { ins_10(100); }
script timeline03 { ins_10(100); }

script timeline04 { ins_10(100); }
script timeline05 { ins_10(100); }
script timeline06 { ins_10(100); }
script timeline07 { ins_10(100); }

script timeline08 { ins_10(100); }
script timeline09 { ins_10(100); }
script timeline10 { ins_10(100); }
script timeline11 { ins_10(100); }

script timeline12 { ins_10(100); }
script timeline13 { ins_10(100); }
script timeline14 { ins_10(100); }
script timeline15 { ins_10(100); }
"#,
    expect_error: "too many timelines",
);

