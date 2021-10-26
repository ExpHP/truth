use crate::integration_impl::formats::*;

source_test!(
    ANM_10, seqmap_missing_section_header,
    mapfile: r#"!anmmap
300 ot
"#,
    main_body: r#""#,
    expect_error: "missing section header",
);

source_test!(
    ANM_10, seqmap_missing_magic,
    mapfile: r#"
300 ot
"#,
    main_body: r#""#,
    expect_error: "missing magic",
);

source_test!(
    ANM_10, abi_multiple_o,
    mapfile: r#"!anmmap
!ins_signatures
300 oot
"#,
    main_body: r#""#,
    expect_error: "multiple 'o'",
);

source_test!(
    // NOTE: in the future this should be allowed but for now it is rejected because
    //       it doesn't implement the right semantics. Note the desired semantics may
    //       differ between different sections and require additional tests.
    //       (it should behave similar to whatever you get from having multiple
    //        separate mapfiles define conflicting keys for that section)
    ANM_10, seqmap_duplicate_key,
    mapfile: r#"!anmmap
!ins_names
10 blue
10 bloo
"#,
    main_body: r#""#,
    expect_error: "duplicate key error",
);

source_test!(
    ANM_10, intrinsic_name_garbage,
    mapfile: r#"!anmmap
!ins_intrinsics
4 lmfao
"#,
    main_body: r#""#,
    expect_error: "invalid intrinsic name",
);

source_test!(
    ANM_10, intrinsic_name_xkcd_859,
    mapfile: r#"!anmmap
!ins_intrinsics
4 CondJmp(>,int
"#,
    main_body: r#""#,
    expect_error: "invalid intrinsic name",
);

source_test!(
    ANM_10, intrinsic_name_extra_arg,
    mapfile: r#"!anmmap
!ins_intrinsics
4 Jmp(int)
"#,
    main_body: r#""#,
    expect_error: "invalid intrinsic name",
);

source_test!(
    ANM_10, intrinsic_name_missing_arg,
    mapfile: r#"!anmmap
!ins_intrinsics
4 CondJmp(>=)
"#,
    main_body: r#""#,
    expect_error: "invalid intrinsic name",
);

source_test!(
    ANM_10, intrinsic_name_typo,
    mapfile: r#"!anmmap
!ins_intrinsics
4 CondimentJmp(>=,int)
"#,
    main_body: r#""#,
    expect_error: "invalid intrinsic name",
);

source_test!(
    ANM_10, intrinsic_jmp_needs_offset,
    mapfile: r#"!anmmap
!ins_intrinsics
4 Jmp(+)
!ins_signatures
4 St
"#,
    main_body: r#""#,
    expect_error: "without an 'o'",
);

source_test!(
    ANM_10, intrinsic_jmp_mislabeled_time,
    mapfile: r#"!anmmap
!ins_intrinsics
4 Jmp()
!ins_signatures
4 So
"#,
    main_body: r#""#,
    expect_error: "unexpected dword",
);

source_test!(
    ANM_10, intrinsic_jmp_non_consecutive_offset_time,
    mapfile: r#"!anmmap
!ins_signatures
300 tSo
!ins_intrinsics
300 CountJmp()
"#,
    main_body: r#""#,
    expect_error: "must be consecutive", // current limitation
);

source_test!(
    ANM_10, intrinsic_op_output_arg_wrong_type,
    mapfile: r#"!anmmap
!ins_intrinsics
99 AssignOp(=,int)
!ins_signatures
99 fS
"#,
    main_body: r#""#,
    expect_error: "unexpected encoding",
);

source_test!(
    ANM_10, intrinsic_op_input_arg_wrong_type,
    mapfile: r#"!anmmap
!ins_intrinsics
99 AssignOp(=,int)
!ins_signatures
99 Sf
"#,
    main_body: r#""#,
    expect_error: "unexpected encoding",
);

source_test!(
    ANM_10, intrinsic_has_extra_arg,
    mapfile: r#"!anmmap
!ins_intrinsics
99 AssignOp(=,int)
!ins_signatures
99 SSS
"#,
    main_body: r#""#,
    expect_error: "unexpected",
);

source_test!(
    ANM_10, intrinsic_has_insufficient_args,
    mapfile: r#"!anmmap
!ins_intrinsics
99 AssignOp(=,int)
!ins_signatures
99 S
"#,
    main_body: r#""#,
    expect_error: "not enough arguments",
);

source_test!(
    ANM_10, intrinsic_with_mismatched_signature_in_core_map,
    mapfile: r#"!anmmap
!ins_intrinsics
3 Jmp()    # id of sprite which is S
"#,
    main_body: r#""#,
    expect_error: "missing jump offset",
);

source_test!(
    ANM_10, intrinsic_without_signature,
    mapfile: r#"!anmmap
!ins_intrinsics
999 Jmp()
"#,
    items: r#"
// the multiple scripts are a regression test for commit c051299ba21de11e
// (we should only get one copy of the error)
script aaa { }
script bbb { }
"#,
    main_body: r#""#,
    expect_error: "has no signature",
);

source_test!(
    ANM_10, intrinsic_with_novel_abi,
    mapfile: r#"!anmmap
!ins_signatures
99  Sto   # no game has a CountJmp signature like this!!
!ins_intrinsics
99  CountJmp()
"#,
    main_body: r#"
    $I0 = 10;
blah:
    +50:
    ins_99($I0, timeof(blah), offsetof(blah));
"#,
    sbsb: |decompiled| {
        // should decompile to a `do { } while (--$I0)` loop!
        assert!(decompiled.contains("while (--"));
    },
    // NOTE: This test depends somewhat riskily on the fact that, currently, the last
    //       opcode assigned to an intrinsic takes priority during compilation.
    //       (so the recompile step also uses opcode 99 instead of 5 and hence the
    //       final binary matches)
    //
    //       This behavior of truth is incidental/not (yet) specified and the test
    //       could be made more robust with the addition of a --no-default-intrinsics
    //       flag to guarantee that the opcode 5 pairing is completely forgotten.
);

source_test!(
    ANM_10, intrinsic_float_op_like_eosd_ecl,
    mapfile: r#"!anmmap
!ins_signatures
99  Sff   # EoSD ECL writes output regs as integers
!ins_intrinsics
99  BinOp(+,float)
"#,
    main_body: r#"
    ins_99($REG[10], %REG[20], 3.5f);
"#,
    sbsb: |decompiled| {
        // The raw ins_ used $REG but the decompiled op should use %REG syntax
        assert!(decompiled.contains("%REG[10] = %REG[20] + 3.5"));
    },
    // NOTE: This test depends somewhat riskily on the fact that, currently, the last
    //       opcode assigned to an intrinsic takes priority during compilation.
);

source_test!(
    ANM_10, multiple_m_arguments,
    compile_args: [
        "-m", "tests/integration/resources/multiple-mapfiles-1.anmm",
        "-m", "tests/integration/resources/multiple-mapfiles-2.anmm",
    ],
    main_body: r#"
    aaa(2, 4);
    bbb(5, 7);
"#,
    check_compiled: |_, _| {}, // just expecting no warnings/errors
);
