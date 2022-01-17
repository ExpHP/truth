#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

source_test!(
    STD_12, compile_simple,
    mapfile: r#"!stdmap
!ins_signatures
400 SS(enum="TestEnum")
!enum(name="TestEnum")
20 Red
40 Green
    "#,
    main_body: r#"
        ins_400(30, Red);
        ins_400(30, 20);
    "#,
    check_compiled: |output, format| {
        let std = output.read_std(format);
        assert_eq!(std.script[0].args_blob, blobify![30, 20]);
        assert_eq!(std.script[1].args_blob, blobify![30, 20]);
    },
);

source_test!(
    #[ignore]
    STD_12, decompile_simple,
    mapfile: r#"!stdmap
!ins_signatures
400 SS(enum="TestEnum")
!enum(name="TestEnum")
20 Red
40 Green
    "#,
    main_body: r#"
        ins_400(20, 20);
    "#,
    check_decompiled: |decompiled| {
        assert!(decompiled.contains("(20, Red)"));
    },
);

source_test!(
    STD_12, compile_undefined,
    mapfile: r#"!stdmap
!ins_signatures
400 SS(enum="TestEnum")  //~ ERROR undefined
    "#,
    main_body: "",
);

source_test!(
    STD_12, decompile_undefined,
    decompile_mapfile: r#"!stdmap
!ins_signatures
400 SS(enum="TestEnum")  //~ ERROR undefined
    "#,
    main_body: "",
);

source_test!(
    STD_12, decompile_no_consts,
    mapfile: r#"!stdmap
!ins_signatures
400 SS(enum="TestEnum")
!enum(name="TestEnum")
    "#,
    main_body: r#"
        ins_400(30, 20);
    "#,
    check_decompiled: |decompiled| {
        // mostly just checking that it doesn't panic on looking up a map.
        // (e.g. if it fails to initialize empty enum maps properly)
        assert!(decompiled.contains(", 20)"));
    },
);

source_test!(
    STD_12, rename_const,
    mapfile: r#"!stdmap
!ins_signatures
400 SS(enum="TestEnum")
!enum(name="TestEnum")
20 OldName
20 Aaaaaa  # some more names to reduce likelihood of accidental success
20 Zzzzzz
20 Qwerty
20 NewName
    "#,
    main_body: r#"
        ins_400(30, OldName);
        ins_400(30, NewName);
    "#,
    check_decompiled: |decompiled| {
        // the final name should take precedence
        assert_eq!(decompiled.matches(", NewName)").count(), 2);
    },
);

source_test!(
    STD_12, compile_bad_conflict,
    mapfile: r#"!stdmap
!enum(name="TestEnum")
20 Name
40 Name  //~ ERROR conflicting
    "#,
    main_body: "",
);

source_test!(
    STD_12, decompile_bad_conflict,
    decompile_mapfile: r#"!stdmap
!enum(name="TestEnum")
20 Name
40 Name  //~ ERROR conflicting
    "#,
    main_body: "",
);

source_test!(
    STD_12, split_between_mapfiles,
    mapfile: r#"!stdmap
!ins_signatures
400 SS(enum="TestEnum")
!enum(name="TestEnum")
40 Green
    "#,
    mapfile: r#"!stdmap
!enum(name="TestEnum")
20 Red
    "#,
    main_body: r#"
        ins_400(30, Red);
        ins_400(30, Green);
    "#,
    check_decompiled: |decompiled| {
        assert!(decompiled.contains(", Red);"));
        assert!(decompiled.contains(", Green);"));
    },
);

source_test!(
    STD_12, used_as_integer,
    mapfile: r#"!stdmap
!ins_signatures
400 S
!enum(name="FooEnum")
20 Name
    "#,
    main_body: r#"
        ins_400(Name);
        ins_400(2 + Name * 2);
    "#,
    check_compiled: |output, format| {
        let std = output.read_std(format);
        assert_eq!(std.script[0].args_blob, blobify![20]);
        assert_eq!(std.script[1].args_blob, blobify![42]);
    },
);

source_test!(
    STD_12, legal_conflict,
    mapfile: r#"!stdmap
!ins_signatures
400 S(enum="FooEnum")S(enum="BarEnum")
!enum(name="FooEnum")
20 Name
!enum(name="BarEnum")
40 Name
    "#,
    main_body: r#"
        ins_400(Name, Name);
    "#,
    check_compiled: |output, format| {
        let std = output.read_std(format);
        assert_eq!(std.script[0].args_blob, blobify![20, 40]);
    },
    check_decompiled: |decompiled| {
        assert!(decompiled.contains("(Name, Name)"));
    },
);

source_test!(
    STD_12, legal_conflict_used_ambiguously,
    mapfile: r#"!stdmap
!ins_signatures
400 S
!enum(name="FooEnum")
20 Name
!enum(name="BarEnum")
40 Name
    "#,
    main_body: r#"
        ins_400(Name);  //~ ERROR FooEnum::Name
    "#,
);

source_test!(
    ANM_12, legal_builtin_conflict,
    mapfile: r#"!anmmap
!ins_signatures
300 N
400 S(enum="FooEnum")
!enum(name="FooEnum")
20 Name
    "#,
    items: r#"
        script Name {
            ins_400(Name);
        }
    "#,
    main_body: r#"
        ins_300(Name);
    "#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        // Name as enum const
        assert_eq!(anm.entries[0].scripts[0].instrs[0].args_blob, blobify![20]);
        // Name as script ID
        assert_eq!(anm.entries[0].scripts[1].instrs[0].args_blob, blobify![0]);
    },
    check_decompiled: |decompiled| {
        assert_eq!(decompiled.matches("(Name)").count(), 2);
    },
);

source_test!(
    ANM_12, legal_builtin_conflict_used_ambiguously,
    mapfile: r#"!anmmap
!ins_signatures
400 S
!enum(name="FooEnum")
20 Name
    "#,
    items: r#"
        script Name {}
    "#,
    main_body: r#"
        ins_400(Name);  //~ ERROR: ambiguous
    "#,
);

source_test!(
    ANM_12, other_enum_warning,
    mapfile: r#"!anmmap
!ins_names
300 TakesScript
400 TakesFoo
500 TakesBar
!ins_signatures
300 N
400 S(enum="FooEnum")
500 S(enum="BarEnum")

!enum(name="FooEnum")
20 FooOnly
40 ScriptAndFoo
!enum(name="BarEnum")
30 BarOnly
    "#,
    items: r#"
        script ScriptOnly {}
        script ScriptAndFoo {}
    "#,
    main_body: r#"
        TakesFoo(BarOnly); //~ WARNING different enum
        TakesFoo(ScriptOnly); //~ WARNING script

        // prefer to mention the user enum over the builtin
        TakesBar(ScriptAndFoo); //~ WARNING different enum

        // These are valid
        TakesScript(ScriptAndFoo);
        TakesFoo(ScriptAndFoo);

        TakesScript(FooOnly); //~ WARNING enum
    "#,
    // this test is mostly about the warnings,
    // but also do a round-trip decompile test with this mapfile
    check_decompiled: |_| {},
);
