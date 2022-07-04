#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

source_test!(
    STD_08, new_lines,
    main_body: r#"
        interrupt[1]:
        posKeyframe(0.0, 0.0, 0.0);
        interrupt[2]:
        interrupt[3]:
        posKeyframe(0.0, 0.0, 0.0);
    "#,
    check_decompiled: |decompiled| {
        // test for blank line before interrupt[2] but NOT before interrupt[3]
        assert!(decompiled.contains("\n\ninterrupt[2]:\ninterrupt[3]:\n"), "{:?}", decompiled);
    },
);

source_test!(
    #[ignore = "unignore this once 'imm' is implemented"]
    ANM_12, decompile_register,
    main_body: r#"
        ins_64(45);
        ins_64($REG[10000]);
    "#,
    check_decompiled: |decompiled| {
        // the second one should have fallen back to raw syntax
        assert!(decompiled.contains("($REG[10000])"));
        // specificity (prove that we have the right opcode)
        assert!(decompiled.contains("interrupt[45]"));
    },
);

source_test!(
    ANM_12, sugar_const,
    items: r#"
        const int MY_INTERRUPT = 5;
    "#,
    main_body: r#"
    interrupt[MY_INTERRUPT]:
    "#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);
        assert_eq!(anm.entries[0].scripts[0].instrs[0].args_blob, blobify![5]);
    },
);

source_test!(
    ANM_12, sugar_register,
    main_body: r#"
    interrupt[45]:
    interrupt[I0]:  //~ ERROR const
    "#,
);

source_test!(
    ANM_12, decompile_enum,
    mapfile: r#"!anmmap
!ins_signatures
64 S(enum="AnmInterrupt")

!enum(name="AnmInterrupt")
13 MyInterrupt
"#,
    main_body: r#"
    interrupt[13]:
"#,
    check_decompiled: |decompiled| {
        assert!(decompiled.contains("interrupt[MyInterrupt]:"))
    },
);
