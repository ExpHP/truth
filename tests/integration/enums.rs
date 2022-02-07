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
        ins_400(30, TestEnum.Red);
        ins_400(30, .Red);
        ins_400(30, 20);
    "#,
    check_compiled: |output, format| {
        let std = output.read_std(format);
        assert_eq!(std.script[0].args_blob, blobify![30, 20]);
        assert_eq!(std.script[1].args_blob, blobify![30, 20]);
        assert_eq!(std.script[2].args_blob, blobify![30, 20]);
    },
);

source_test!(
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
        assert!(decompiled.contains("(20, .Red)"));
    },
);

source_test!(
    ANM_10, enum_arg_not_ident,
    mapfile: r#"!anmmap
!ins_signatures
999 S(enum="ax@3")  //~ ERROR ident
"#,
    main_body: "",
);

source_test!(
    ANM_10, enum_def_not_ident,
    mapfile: r#"!anmmap
!enum(name="ax@3")  //~ ERROR ident
"#,
    main_body: "",
);

mod undefined_enum {
    use super::*;

    // we should error if an enum is never defined
    const USAGE_MAPFILE_WITH_ERROR: &'static str = r#"!stdmap
!ins_signatures
400 S(enum="TestEnum")  //~ ERROR no such enum
    "#;

    source_test!(
        STD_12, compile_undefined,
        mapfile: USAGE_MAPFILE_WITH_ERROR,
        main_body: "",
    );

    source_test!(
        STD_12, decompile_undefined,
        decompile_mapfile: USAGE_MAPFILE_WITH_ERROR,
        main_body: "",
    );

    source_test!(
        STD_12, compile_undefined_in_ast,
        // An enum parameter is not currently valid syntax, but if it were, then we
        // need to check that the enum name is valid, just like we do for mapfile sigs.
        items: r#"
            const int ConstFn(enum NotAnEnum x) {  //~ ERROR token
                return x + 10;
            }
        "#,
    );

    // if there's a similar name we should suggest it
    source_test!(
        STD_12, suggestion,
        mapfile: r#"!stdmap
!ins_signatures
400 S(enum="TesEnum")  //~ ERROR TestEnum

!enum(name="BarEnum")
!enum(name="TestEnum")
!enum(name="Roxanne")
    "#,
        main_body: "",
    );

    // It's okay if the enum is declared in a separate mapfile, regardless of inclusion order
    const USAGE_MAPFILE_OKAY: &'static str = r#"!stdmap
!ins_signatures
400 S(enum="TestEnum")
    "#;

    const DECLARATION_MAPFILE: &'static str = r#"!stdmap
!enum(name="TestEnum")
    "#;

    source_test!(
        STD_12, separated_order_1,
        mapfile: USAGE_MAPFILE_OKAY,
        mapfile: DECLARATION_MAPFILE,
        main_body: "",
        check_compiled: |_, _| {},
    );

    source_test!(
        STD_12, separated_order_2,
        mapfile: DECLARATION_MAPFILE,
        mapfile: USAGE_MAPFILE_OKAY,
        main_body: "",
        check_compiled: |_, _| {},
    );
}

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
        ins_400(30, .OldName);
        ins_400(30, .NewName);
    "#,
    check_decompiled: |decompiled| {
        // the final name should take precedence
        assert_eq!(decompiled.matches(", .NewName)").count(), 2);
    },
);

source_test!(
    STD_12, compile_bad_conflict,
    mapfile: r#"!stdmap
!enum(name="TestEnum")
20 Name  //~ ERROR ambiguous
40 Name
    "#,
    main_body: "",
);

source_test!(
    STD_12, decompile_bad_conflict,
    decompile_mapfile: r#"!stdmap
!enum(name="TestEnum")
20 Name  //~ ERROR ambiguous
40 Name
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
        ins_400(30, .Red);
        ins_400(30, .Green);
    "#,
    check_decompiled: |decompiled| {
        assert!(decompiled.contains(", .Red);"));
        assert!(decompiled.contains(", .Green);"));
    },
);

source_test!(
    ANM_12, used_as_integer,
    mapfile: r#"!anmmap
!ins_signatures
400 S
!enum(name="FooEnum")
20 Name
    "#,
    main_body: r#"
        ins_400(FooEnum.Name);
        ins_400(2 + FooEnum.Name * 2);
        ins_999(@mask=FooEnum.Name, @blob="01000000");
    "#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        assert_eq!(anm.entries[0].scripts[0].instrs[0].args_blob, blobify![20]);
        assert_eq!(anm.entries[0].scripts[0].instrs[1].args_blob, blobify![42]);
        assert_eq!(anm.entries[0].scripts[0].instrs[2].param_mask, 20);
    },
);

source_test!(
    STD_12, used_in_const,
    mapfile: r#"!stdmap
!ins_signatures
400 S
!enum(name="FooEnum")
20 Name
    "#,
    main_body: r#"
        const int x = 2 + FooEnum.Name * 2;
        ins_400(x);
    "#,
    check_compiled: |output, format| {
        let std = output.read_std(format);
        assert_eq!(std.script[0].args_blob, blobify![42]);
    },
);

source_test!(
    STD_12, invalid_infer_in_const,
    mapfile: r#"!stdmap
!ins_signatures
400 S
!enum(name="FooEnum")
20 Name
    "#,
    main_body: r#"
        const int x = 2 + .Name * 2;  //~ ERROR unqualified
    "#,
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
        ins_400(.Name, .Name);
    "#,
    check_compiled: |output, format| {
        let std = output.read_std(format);
        assert_eq!(std.script[0].args_blob, blobify![20, 40]);
    },
    check_decompiled: |decompiled| {
        assert!(decompiled.contains("(.Name, .Name)"));
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
        ins_400(.Name);  //~ ERROR unqualified
        ins_999(@mask=.Name, @blob="01000000");  //~ ERROR unqualified
    "#,
);

source_test!(
    ANM_12, legal_builtin_conflict,
    mapfile: r#"!anmmap
!ins_names
300 TakesScript
400 TakesFoo
!ins_signatures
300 N
400 S(enum="FooEnum")
!enum(name="FooEnum")
20 Name
21 Name2
    "#,
    items: r#"
        script Name {}
    "#,
    main_body: r#"
        TakesScript(Name);
        TakesFoo(Name);  //~ WARNING script
        TakesFoo(.Name);

        // a regular const sharing the same name is okay
        const int Name2 = 10;
        TakesFoo(Name2);  // no warning
        TakesFoo(.Name2);
    "#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        assert_eq!(anm.entries[0].scripts[1].instrs[0].args_blob, blobify![0]);
        assert_eq!(anm.entries[0].scripts[1].instrs[1].args_blob, blobify![0]);
        assert_eq!(anm.entries[0].scripts[1].instrs[2].args_blob, blobify![20]);
    },
    check_decompiled: |decompiled| {
        assert_eq!(decompiled.matches("(0)").count(), 1);  // from TakesFoo(Name)
        assert_eq!(decompiled.matches("(.Name)").count(), 1);
    },
);

source_test!(
    ANM_12, other_enum,
    mapfile: r#"!anmmap
!ins_signatures
400 S(enum="FooEnum")

!enum(name="FooEnum")
20 FooOnly
!enum(name="BarEnum")
30 BarOnly
    "#,
    main_body: r#"
        ins_400(.BarOnly); //~ ERROR no such enum const
    "#,
);

source_test!(
    ANM_12, deduction_in_const_fn,
    mapfile: r#"!anmmap
!ins_signatures
400 S
!enum(name="FooEnum")
20 Red
    "#,
    // An enum parameter is not currently valid syntax, but if it were, then this
    // is a concern that came up when implementing value substitution for enums.
    //
    // (Basically, the part of the const simplification pass that figures out the
    //  appropriate enum for '.Red' would need some sort of equivalent in the
    //  (separate) const evaluator)
    items: r#"
        const int ConstFn(enum FooEnum x) {  //~ ERROR token
            return x + 10;
        }
    "#,
    main_body: r#"
        const y = ConstFn(.Red);
        ins_400(y);
    "#,
);
