#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

source_test!(
    ANM_10, mapfile_does_not_exist,
    items: r#"
        #pragma mapfile "this/is/a/bad/path"
    "#,
    expect_error: "while resolving",
);

source_test!(
    ANM_10, seqmap_missing_section_header,
    mapfile: r#"!anmmap
300 ot  //~ ERROR missing section header
"#,
    main_body: r#""#,
);

source_test!(
    ANM_10, seqmap_missing_magic,
    mapfile: r#"//~ ERROR missing magic
300 ot
"#,
    main_body: r#""#,
);

source_test!(
    ANM_10, abi_multiple_o,
    mapfile: r#"!anmmap
!ins_signatures
300 oot   //~ ERROR multiple 'o'
"#,
    main_body: r#""#,
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
    check_decompiled: |decompiled| {
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
    ANM_10, keywords_or_forbidden_idents,
    mapfile: r#"!anmmap
!ins_names
99 break  //~ ERROR identifier
100 ins_200  //~ ERROR identifier
"#,
    main_body: "",
);

source_test!(
    ANM_10, intrinsic_name_garbage,
    mapfile: r#"!anmmap
!ins_intrinsics

# no parens
4 lmfao            //~ ERROR invalid intrinsic name

# xkcd 859
5 CondJmp(>,int    //~ ERROR invalid intrinsic name

# extra arg
6 Jmp(int)         //~ ERROR invalid intrinsic name

# missing arg
7 CondJmp(>=)      //~ ERROR invalid intrinsic name

# intrinsic name typo
8 CondimentJmp(>=,int)  //~ ERROR invalid intrinsic name
"#,
    main_body: r#""#,
);

source_test!(
    ANM_10, intrinsic_jmp_needs_offset,
    mapfile: r#"!anmmap
!ins_intrinsics
4 Jmp(+)
!ins_signatures
4 St     //~ ERROR without an 'o'
"#,
    main_body: r#""#,
);

source_test!(
    ANM_10, intrinsic_jmp_mislabeled_time,
    mapfile: r#"!anmmap
!ins_intrinsics
4 Jmp()
!ins_signatures
4 So     //~ ERROR unexpected dword
"#,
    main_body: r#""#,
);

source_test!(
    ANM_10, intrinsic_jmp_non_consecutive_offset_time,
    mapfile: r#"!anmmap
!ins_signatures
300 tSo   //~ ERROR must be consecutive
!ins_intrinsics
300 CountJmp()
"#,
    main_body: r#""#,
);

source_test!(
    ANM_10, intrinsic_op_output_arg_wrong_type,
    mapfile: r#"!anmmap
!ins_intrinsics
99 AssignOp(=,int)
!ins_signatures
99 fS     //~ ERROR unexpected encoding
"#,
    main_body: r#""#,
);

source_test!(
    ANM_10, intrinsic_op_input_arg_wrong_type,
    mapfile: r#"!anmmap
!ins_intrinsics
99 AssignOp(=,int)
!ins_signatures
99 Sf     //~ ERROR unexpected encoding
"#,
    main_body: r#""#,
);

source_test!(
    ANM_10, intrinsic_has_extra_arg,
    mapfile: r#"!anmmap
!ins_intrinsics
99 AssignOp(=,int)
!ins_signatures
99 SSS     //~ ERROR unexpected
"#,
    main_body: r#""#,
);

source_test!(
    ANM_10, intrinsic_has_insufficient_args,
    mapfile: r#"!anmmap
!ins_intrinsics
99 AssignOp(=,int)
!ins_signatures
99 S     //~ ERROR not enough arguments
"#,
    main_body: r#""#,
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
999 Jmp()  //~ ERROR has no signature
"#,
    items: r#"
// this particular error used to be generated once per script (commit c051299ba21de11e),
// so put a couple here as a regression test.
// (they don't need to actually use the instruction)
script aaa { }
script bbb { }
"#,
    main_body: r#""#,
);

source_test!(
    ANM_10, intrinsic_for_op_that_no_game_has,
    mapfile: r#"!anmmap
!ins_intrinsics
999 BinOp(>>>,int)
!ins_signatures
999 SSS
"#,
    main_body: r#"
    int x = 10;
    int y = 15;
    int z = x >>> (y + 3);
"#,
    check_compiled: |output, format| {
        let ecl = output.read_anm(format);
        assert!(ecl.entries[0].scripts[0].instrs.iter().any(|instr| instr.opcode == 999));
    },
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
    check_decompiled: |decompiled| {
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
    check_decompiled: |decompiled| {
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
8 b-  //~ ERROR out of range
"#,
    main_body: "",
);

source_test!(
    ECL_06, diff_flags_syntax_errors,
    mapfile: r#"!eclmap
!difficulty_flags
1 @-                         //~ ERROR invalid difficulty
2 X@                         //~ ERROR invalid difficulty
3 a                          //~ ERROR invalid difficulty
4 θ  # a two byte character  //~ ERROR invalid difficulty
"#,
    main_body: "",
);

source_test!(
    ANM_10, multiple_m_arguments,
    compile_args: &[
        "-m", "tests/integration/resources/multiple-mapfiles-1.anmm",
        "-m", "tests/integration/resources/multiple-mapfiles-2.anmm",
    ],
    main_body: r#"
    aaa(2, 4);
    bbb(5, 7);
"#,
    check_compiled: |_, _| {}, // just expecting no warnings/errors
);
