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
    ANM_10, seqmap_duplicate_key,
    mapfile: r#"!anmmap
!ins_signatures
99 S
!ins_names
99 blue
99 bloo
"#,
    main_body: r#"
    blue(5);
    bloo(7);
    "#,
    sbsb: |decompiled| {
        // prefer the most recent name
        assert!(decompiled.contains("bloo"));
        assert!(!decompiled.contains("blue"));
    },
);

source_test!(
    ANM_10, seqmap_duplicate_section,
    mapfile: r#"!anmmap
!ins_names
99 blue
!ins_signatures
99 S
!ins_names
99 bloo
"#,
    main_body: r#"
    blue(5);
    bloo(7);
    "#,
    check_compiled: |_, _| {
        // just need it to succeed...
    },
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
    ECL_06, diff_flags_bad_index,
    mapfile: r#"!eclmap
!difficulty_flags
8 b-
"#,
    main_body: "",
    expect_error: "out of range",
);

source_test!(
    ECL_06, diff_flags_syntax_errors,
    mapfile: r#"!eclmap
!difficulty_flags
1 @-
2 X@
3 a
4 θ   # a two byte character
5 There_should_be_errors_on_all_lines_from_1_to_this_number
"#,
    main_body: "",
    expect_error: "invalid difficulty",
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
