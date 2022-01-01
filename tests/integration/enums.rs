#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

source_test!(
    STD_12, simple_enum_compile,
    mapfile: r#"!stdmap
!ins_names
400 testIns
!ins_signatures
400 SS(enum="TestEnum")
!enum(name="TestEnum")
20 Red
40 Green
    "#,
    main_body: r#"
        testIns(30, Red);
        testIns(30, 20);
    "#,
    check_compiled: |output, format| {
        let std = output.read_std(format);
        assert_eq!(std.script[0].args_blob, blobify![30, 20]);
        assert_eq!(std.script[1].args_blob, blobify![30, 20]);
    },
);

source_test!(
    #[ignore]
    STD_12, simple_enum_decompile,
    mapfile: r#"!stdmap
!ins_names
400 testIns
!ins_signatures
400 SS(enum="TestEnum")
!enum(name="TestEnum")
20 Red
40 Green
    "#,
    main_body: r#"
        testIns(20, 20);
    "#,
    check_decompiled: |decompiled| {
        assert!(decompiled.contains("(20, Red)"));
    },
);

source_test!(
    STD_12, undefined_enum_compile,
    mapfile: r#"!stdmap
!ins_signatures
400 SS(enum="TestEnum")  //~ ERROR undefined
    "#,
    main_body: "",
);

source_test!(
    STD_12, undefined_enum_decompile,
    decompile_mapfile: r#"!stdmap
!ins_signatures
400 SS(enum="TestEnum")  //~ ERROR undefined
    "#,
    main_body: "",
);

source_test!(
    STD_12, enum_no_variants_decompile,
    mapfile: r#"!stdmap
!ins_names
400 testIns
!ins_signatures
400 SS(enum="TestEnum")
!enum(name="TestEnum")
    "#,
    main_body: r#"
        testIns(30, 20);
    "#,
    check_decompiled: |s| {
        // mostly just checking that it doesn't panic on looking up a map.
        // (e.g. if it fails to initialize empty enum maps properly)
        assert!(s.contains(", 20)"));
    },
);

