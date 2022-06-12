#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

// NOTE: there is another expr_compile test file that does a lot more.
//
// This file is for things that are easier to test using the source_test macro.

source_test!(
    ANM_10, unary_neg_bitnot_intrinsic_preferred_over_fallback,
    mapfile: r#"!anmmap
!ins_intrinsics
1000 UnOp(op="-"; type="int")
2000 UnOp(op="~"; type="int")
1500 BinOp(op="-"; type="int")

!ins_signatures
1000 SS
2000 SS
1500 SSS
    "#,
    main_body: r#"
    int a = -$I0;
    int b = ~$I0;
"#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);

        // should be intrinsics and not fallback
        assert_eq!(anm.entries[0].scripts[0].instrs[0].opcode, 1000);
        assert_eq!(anm.entries[0].scripts[0].instrs[0].args_blob[4..], blobify![10000]);
        assert_eq!(anm.entries[0].scripts[0].instrs[1].opcode, 2000);
        assert_eq!(anm.entries[0].scripts[0].instrs[1].args_blob[4..], blobify![10000]);
    },
    // NOTE: This test depends somewhat riskily on the fact that, currently, the last
    //       opcode assigned to an intrinsic takes priority during compilation.
);


source_test!(
    ANM_10, unary_neg_bitnot_fallbacks,
    mapfile: r#"!anmmap
!ins_intrinsics
1500 BinOp(op="-"; type="int")

!ins_signatures
1500 SSS
    "#,
    main_body: r#"
    int a = -$I0;
    int b = ~$I0;
"#,
    check_compiled: |output, format| {
        let anm = output.read_anm(format);

        assert_eq!(anm.entries[0].scripts[0].instrs[0].opcode, 1500);
        assert_eq!(anm.entries[0].scripts[0].instrs[0].args_blob[4..], blobify![0, 10000]);
        assert_eq!(anm.entries[0].scripts[0].instrs[1].opcode, 1500);
        assert_eq!(anm.entries[0].scripts[0].instrs[1].args_blob[4..], blobify![-1, 10000]);
    },
    // NOTE: This test depends somewhat riskily on the fact that, currently, the last
    //       opcode assigned to an intrinsic takes priority during compilation.
);

// // FIXME: implement --no-default-intrinsics
// source_test!(
//     ANM_10, unary_neg_fallbacks_unavailable,
//     compile_options: ["--no-default-intrinsics"],
//     mapfile: r#"!anmmap
//     "#,
//     main_body: r#"
//     int a = -$I0;  //~ ERROR unsupported
//     float x = -%F0;  //~ ERROR unsupported
// "#,
// );
