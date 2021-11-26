#[allow(unused)]
use crate::integration_impl::{expected, formats::*};

source_test!(
    STD_08, loop_simple,
    main_body: r#"
        up(0.0, 1.0, -1.0);
        fov(0.5235988);
        posKeyframe(0.0, 0.0, 0.0);
        spriteC(5);
        spriteA(4);
    label:
        pos(0.0, 4984.0, 20.0);
        posTime(1024, 0);
        pos(0.0, 5240.0, 20.0);
    +1024:
        goto label;
    -1:
        posKeyframe(0.0, 0.0, 0.0);
    "#,
    sbsb: |decompiled| {
        assert!(decompiled.contains("loop {"));
    },
);

source_test!(
    STD_08, loop_nonzero_time,
    // like above, but the label has a nonzero label
    main_body: r#"
        up(0.0, 1.0, -1.0);
    +10:
        up(0.0, 1.0, -1.0);
    label:
        pos(0.0, 4984.0, 20.0);
        posTime(1024, 0);
        pos(0.0, 5240.0, 20.0);
    +1024:
        goto label;
    -1:
        posKeyframe(0.0, 0.0, 0.0);
    "#,
    sbsb: |decompiled| {
        assert!(decompiled.contains("loop {"));
    },
);

source_test!(
    STD_08, loop_previous_instr_time,
    // in this one, the jump has the time of the previous instruction.
    // this should still be able to decompile a loop.
    main_body: r#"
        up(0.0, 1.0, -1.0);
    +10:
        up(0.0, 1.0, -1.0);
    +20:
    label:
        pos(0.0, 4984.0, 20.0);
    +1024:
        goto label @ 10;
    -1:
        posKeyframe(0.0, 0.0, 0.0);
    "#,
    sbsb: |decompiled| {
        assert!(decompiled.contains("loop {"));
        assert!(decompiled.contains("+20:"));
        assert!(decompiled.find("loop {").unwrap() < decompiled.find("+20:").unwrap());
    },
);

source_test!(
    STD_08, loop_other_time,
    // this time the jump time is so weird we can't possibly decompile a loop
    main_body: r#"
        up(0.0, 1.0, -1.0);
    +10:
        up(0.0, 1.0, -1.0);
    +20:
    label:
        pos(0.0, 4984.0, 20.0);
    +1024:
        goto label @ 200;
    -1:
        posKeyframe(0.0, 0.0, 0.0);
    "#,
    sbsb: |decompiled| {
        assert!(!decompiled.contains("loop {"));
    },
);

source_test!(
    STD_08, two_loops_1_label,
    main_body: r#"
    label:
        up(0.0, 1.0, -1.0);
        goto label;
        up(0.0, 1.0, -1.0);
        goto label;
    "#,
    sbsb: |decompiled| {
        // should decompile to a nested loop
        assert!(decompiled.contains("loop {"));
        assert!(decompiled[decompiled.find("loop {").unwrap()..].contains("loop {"));
    },
);

source_test!(
    STD_08, empty_loop,
    main_body: r#"
    +10:
        posKeyframe(0.0, 0.0, 0.0);
    label:
        goto label;
        posKeyframe(0.0, 0.0, 0.0);
    "#,
    sbsb: |decompiled| {
        assert!(decompiled.contains("loop {"));
    },
);

source_test!(
    STD_08, empty_loop_time,
    main_body: r#"
    +10:
        posKeyframe(0.0, 0.0, 0.0);
    +5:
    label:
        goto label @ 10;
        posKeyframe(0.0, 0.0, 0.0);
    "#,
    sbsb: |decompiled| {
        // This should decompile to something like 'loop { +5: }'
        assert!(decompiled.contains("loop {"));
    },
);

source_test!(
    ANM_10, time_loop_at_beginning_of_script,
    main_body: r#"
    label:
    +1:
        pos(0.0, 0.0, 0.0);
        goto label;
    "#,
    sbsb: |decompiled| {
        // This is a regression test for a bug where raising would place this label
        // at the wrong time due to having no "previous instruction"
        assert!(decompiled.contains("loop {"));
    },
);

// A test specifically engineered for the forward-iterating consolidation algorithm
// for loop decompilation, which needs to be careful with its use of indices.
source_test!(
    ECL_06, loop_index_invalidation_check,
    main_body: r#"
    A:
        // numerous statements so that indices change by a fair amount
        ins_0();
        ins_0();
        ins_0();
        ins_0();
        goto A;
    B:
        // the forward-iterating algorithm for loop decompilation could be broken
        // by this next loop if it were to not correctly account for index invalidation.
        ins_0();
        goto B;
    "#,
    sbsb: |decompiled| {
        assert_eq!(decompiled.matches("loop {").count(), 2);
    },
);

// In the absence of other jumps, forward unconditional gotos shouldn't become anything.
source_test!(
    STD_08, forward_jump,
    main_body: r#"
        up(0.0, 1.0, -1.0);
    +10: // 10
        goto label_100;
        up(0.0, 1.0, -1.0);
    +1024: // 1034
    label_100:
        pos(0.0, 5240.0, 20.0);
    "#,
    sbsb: |decompiled| {
        assert!(!decompiled.contains("loop {"));
    },
);

source_test!(
    ECL_06, loop_ruined_by_difficulty,
    main_body: r#"
    +10:
        I1 = 0;
    label:
        I1 = I1 + 1;
        {"E"}: goto label;
    "#,
    sbsb: |decompiled| {
        assert!(!decompiled.contains("loop {"));
    },
);

source_test!(
    ANM_12, break_decompilation,
    main_body: r#"
        start:
            if (I3 == 2) goto end;
        if (--I0) goto start;
        end:
    "#,
    sbsb: |decompiled| assert!(decompiled.contains("break;")),
);

source_test!(
    ANM_12, break_decompilation_ruined_by_time,
    main_body: r#"
        start:
            if (I3 == 2) goto end;
        if (--I0) goto start;
        +1:    // this should prevent decompilation of 'break'
        end:
    "#,
    sbsb: |_decompiled| {
        // don't care so long as it compiles back
    },
);

// =============================================================================

source_test!(
    ANM_12, r#if,
    main_body: r#"
        $I0 = RAND % 3;
        if (I0 != 0) goto end;
        sprite(2);
    end:
        sprite(3);
    "#,
    sbsb: |decompiled| {
        assert!(decompiled.contains(r#"
    if ($REG[10000] == 0) {
        ins_3(sprite2);
    }
    ins_3(sprite3);
    "#.trim()));
    },
);

source_test!(
    ANM_12, if_empty,
    main_body: r#"
        $I0 = RAND % 3;
        if (I0 != 0) goto end;
        // empty if is annoying edge case
    end:
        sprite(3);
    "#,
    sbsb: |decompiled| {
        assert!(decompiled.contains(r#"
    if ($REG[10000] == 0) {
    }
    ins_3(sprite3);
    "#.trim()));
    },
);

source_test!(
    ANM_12, if_else,
    main_body: r#"
        $I0 = RAND % 3;
        if (I0 != 0) goto not0;
        sprite(2);
        goto end;
    not0:
        sprite(3);
    end:
        sprite(4);
    "#,
    sbsb: |decompiled| {
        assert!(decompiled.contains(r#"
    if ($REG[10000] == 0) {
        ins_3(sprite2);
    } else {
        ins_3(sprite3);
    }
    ins_3(sprite4);
    "#.trim()));
    },
);

source_test!(
    ANM_12, if_elseif,
    main_body: r#"
        $I0 = RAND % 3;
        if (I0 != 0) goto not0;
        sprite(2);
        goto end;
    not0:
        if (I0 != 1) goto end;
        sprite(3);
    end:
        sprite(4);
    "#,
    sbsb: |decompiled| {
        assert!(decompiled.contains(r#"
    if ($REG[10000] == 0) {
        ins_3(sprite2);
    } else if ($REG[10000] == 1) {
        ins_3(sprite3);
    }
    ins_3(sprite4);
    "#.trim()));
    },
);

source_test!(
    ANM_12, if_elseif_else,
    main_body: r#"
        $I0 = RAND % 3;
        if (I0 != 0) goto not0;
        sprite(2);
        goto end;
    not0:
        if (I0 != 1) goto not1;
        sprite(3);
        goto end;
    not1:
        sprite(1);
    end:
    "#,
    sbsb: |decompiled| {
        assert!(decompiled.contains(r#"
    if ($REG[10000] == 0) {
        ins_3(sprite2);
    } else if ($REG[10000] == 1) {
        ins_3(sprite3);
    } else {
        ins_3(sprite1);
    }"#.trim()));
    },
);

source_test!(
    ANM_12, if_else_refcount_gt_1,
    // this one can't be fully decompiled to an if-else chain because one of the labels that would have
    // to be deleted is referenced somewhere else
    main_body: r#"
        $I0 = RAND % 3;
        if (I0 != 0) goto not0;
        goto not1;
        goto end;
    not0:
        if (I0 != 1) goto not1;
        sprite(3);
        goto end;
    not1:
        sprite(1);
    end:
    "#,
    sbsb: |_decompiled| {
        // don't care so long as it compiles back
    },
);

source_test!(
    ANM_12, if_elseif_decrement,
    main_body: r#"
        I0 = RAND % 3;
        I0 = I0 + 1;
        if (--I0) goto not0;
        goto not1;
        goto end;
    not0:
        if (--I0) goto not1;
        sprite(3);
        goto end;
    not1:
        sprite(1);
    end:
    "#,
    sbsb: |_decompiled| {
        // don't care so long as it compiles back
    },
);

source_test!(
    ANM_12, if_elseif_time_1,
    // This mismatched jump time should prevent if-else chain decompilation
    // (on an if jump)
    main_body: r#"
        $I0 = RAND % 3;
        if (I0 != 0) goto not0;
        sprite(2);
        goto end;
    not0:
        if (I0 != 1) goto not1 @ 10;
        sprite(3);
        goto end;
    not1:
        sprite(1);
    end:
    "#,
    sbsb: |_decompiled| {
        // don't care so long as it compiles back
    },
);

source_test!(
    ANM_12, if_elseif_time_2,
    // This mismatched jump time should prevent if-else chain decompilation
    // (on an unconditional jump-to-end)
    main_body: r#"
        $I0 = RAND % 3;
        if (I0 != 0) goto not0;
        sprite(2);
        goto end;
    not0:
        if (I0 != 1) goto not1;
        sprite(3);
        goto end @ 10;
    not1:
        sprite(1);
    end:
    "#,
    sbsb: |_decompiled| {
        // don't care so long as it compiles back
    },
);

source_test!(
    ANM_12, if_elseif_time_impossible_1,
    // This has a time label change in a place where it is impossible to put
    // one in the decompiled 'if-else if' structure.
    main_body: r#"
        $I0 = RAND % 3;
        if (I0 != 0) goto not0;
        sprite(2);
        goto end;
    +10:
    not0:
        if (I0 != 1) goto not1;
        sprite(3);
        goto end;
    not1:
        sprite(1);
    end:
    "#,
    sbsb: |_decompiled| {
        // don't care so long as it compiles back
    },
);

source_test!(
    ANM_12, if_elseif_time_sorta_possible,
    // this one can technically be compiled into
    //
    //     if (I0 == 0) {
    //         sprite(2)
    //     } else {
    //     +10:
    //         if (I0 == 1) { ... }
    //         else { ... }
    //     }
    //
    // but anyways, it's tricky.
    main_body: r#"
        $I0 = RAND % 3;
        if (I0 != 0) goto not0;
        sprite(2);
        goto end;
    not0:
    +10:
        if (I0 != 1) goto not1;
        sprite(3);
        goto end;
    not1:
        sprite(1);
    end:
    "#,
    sbsb: |_decompiled| {
        // don't care so long as it compiles back
    },
);

source_test!(
    ANM_12, if_elseif_time_impossible_2,
    // another impossible spot for the time label change;
    // this one's basically inside the "else" keyword
    main_body: r#"
        $I0 = RAND % 3;
        if (I0 != 0) goto not0;
        sprite(2);
        goto end;
    not0:
        if (I0 != 1) goto not1;
        sprite(3);
        goto end;
    +10:
    not1:
        sprite(1);
    end:
    "#,
    sbsb: |_decompiled| {
        // don't care so long as it compiles back
    },
);

source_test!(
    ANM_12, if_elseif_time_unimpossible,
    // despite the pattern of the last three, this one's actually possible.
    // (the time label change is inside the else block)
    main_body: r#"
        $I0 = RAND % 3;
        if (I0 != 0) goto not0;
        sprite(2);
        goto end;
    not0:
        if (I0 != 1) goto not1;
        sprite(3);
        goto end;
    not1:
    +10:
        sprite(1);
    end:
    "#,
    sbsb: |_decompiled| {
        // don't care so long as it compiles back
    },
);

source_test!(
    ECL_06, if_elseif_difficulty_impossible_1,
    main_body: r#"
        set_int_rand_bound(I0, 3);
        if (I0 != 0) goto not0;
        I1 = 3;
        goto end;
    not0:
        {"E"}: if (I0 != 1) goto not1;
        I1 = 2;
        goto end;
    not1:
        I1 = 1;
    end:
    "#,
    sbsb: |_decompiled| {
        // don't care so long as it compiles back
    },
);

source_test!(
    ECL_06, if_elseif_difficulty_impossible_2,
    main_body: r#"
        set_int_rand_bound(I0, 3);
        if (I0 != 0) goto not0;
        I1 = 2;
        {"E"}: goto end;
    not0:
        if (I0 != 1) goto not1;
        I1 = 3;
        goto end;
    not1:
        I1 = 1;
    end:
    "#,
    sbsb: |_decompiled| {
        // don't care so long as it compiles back
    },
);

source_test!(
    ECL_06, if_elseif_difficulty_unimpossible,
    main_body: r#"
        set_int_rand_bound(I0, 3);
        if (I0 != 0) goto not0;
        I1 = 2;
        goto end;
    not0:
        if (I0 != 1) goto not1;
        I1 = 3;
        goto end;
    not1:
    +10:
        {"E"}: I1 = 1;
    end:
    "#,
    sbsb: |_decompiled| {
        // don't care so long as it compiles back
    },
);


source_test!(
    ANM_12, if_elseif_wrong_order,
    // the cases here are not in source order (there's a backwards jump),
    // so they should be at least partially prevented from decompiling.
    main_body: r#"
        $I0 = RAND % 4;
        if (I0 != 0) goto not0;
        sprite(2);
        goto end;
    not1:
        if (I0 != 2) goto not2;
        sprite(0);
        goto end;
    not0:
        if (I0 != 1) goto not1;
        sprite(3);
        goto end;
    not2:
        sprite(1);
    end:
    "#,
    sbsb: |_decompiled| {
        // don't care so long as it compiles back
    },
);

source_test!(
    ANM_12, no_else_referenced_again,
    main_body: r#"
        $I0 = RAND % 4;
        if (I0 != 0) goto not0;
        sprite(1);
        if (I0 != 0) goto not0;
        sprite(2);
    not0:           // test is to make sure this guy doesn't get deleted
        sprite(3);
    "#,
    sbsb: |_decompiled| {
        // don't care so long as it compiles back
    },
);

source_test!(
    ANM_12, if_elseif_end_before,
    // end before the rest.  This should prevent decompilation.
    main_body: r#"
    end:
        $I0 = RAND % 3;
        if (I0 != 0) goto not0;
        sprite(2);
        goto end;
    not0:
        if (I0 != 1) goto not1;
        sprite(3);
        goto end;
    not1:
        sprite(1);
    "#,
    sbsb: |_decompiled| {
        // don't really care what this does, it probably decompiles into a bunch
        // of horrific looking nested loops.  Doesn't matter as long as it's correct.
    },
);

source_test!(
    ANM_12, goto_different_ends,
    main_body: r#"
        $I0 = RAND % 3;
        if (I0 != 0) goto not0;
        sprite(2);
        goto enda;
    not0:
        if (I0 != 1) goto not1;
        sprite(3);
        goto endb;
    not1:
        sprite(1);
    enda:
        pos(0.0, 0.0, 0.0);
    endb:
    "#,
    sbsb: |_decompiled| {
        // don't care so long as it compiles back
    },
);

source_test!(
    ANM_12, cond_jump_to_end,
    // this has a conditional jump to the end.  shenanigans!
    main_body: r#"
        $I0 = RAND % 3;
        if (I0 != 0) goto not0;
        sprite(2);
        goto end;
    not0:
        if (I0 != 1) goto not1;
        sprite(3);
        if (I0 != 1) goto end;
    not1:
        sprite(1);
    end:
    "#,
    sbsb: |_decompiled| {
        // don't care so long as it compiles back
    },
);

source_test!(
    ANM_12, dont_decompile_if_with_interrupt,
    main_body: r#"
        if ($I0 == 0) {
            pos(0.0, 4984.0, 20.0);
    interrupt[5]:
            pos(0.0, 4984.0, 20.0);
        }
    "#,
    sbsb: |decompiled| {
        // don't decompile a block
        assert!(decompiled.contains("!= 0) goto"));
        assert!(!decompiled.contains("== 0) {"));
    },
);

source_test!(
    ANM_12, dont_decompile_if_else_with_interrupt,
    main_body: r#"
        if ($I0 == 0) {
            pos(0.0, 4924.0, 20.0);
        } else {
            pos(0.0, 4954.0, 20.0);
    interrupt[5]:
            pos(0.0, 4984.0, 20.0);
        }
    "#,
    sbsb: |decompiled| {
        // don't decompile a block
        assert!(decompiled.contains("!= 0) goto"));
        assert!(!decompiled.contains("== 0) {"));
    },
);

// =============================================================================

source_test!(
    // this shows up in vanilla EoSD ECL files
    ECL_06, nested_loops_after_if,
    main_body: r#"
        if ($I1 == 0) {
            ins_0();
        } else {
            ins_0();
        }
        loop {
            loop {
                loop {
                }
            }
        }
    "#,
    sbsb: |decompiled| {
        assert!(decompiled.contains(r#"
    if ($REG[-10002] == 0) {
        ins_0();
    } else {
        ins_0();
    }
    loop {
        loop {
            loop {
            }
        }
    }
    "#.trim()));
    },
);

source_test!(
    // this shows up in vanilla EoSD files
    ECL_06, loop_at_end_of_else_if,
    main_body: r#"
        if ($I1 == 0) {
        } else {
            do {
                ins_0();
            } while ($I1 == 2);
        }
    "#,
    sbsb: |decompiled| {
        assert!(decompiled.contains(r#"
    if ($REG[-10002] == 0) {
    } else {
        do {
            ins_0();
        } while ($REG[-10002] == 2);
    }
    "#.trim()));
    },
);

// =============================================================================

source_test!(
    ECL_06, label_created_by_offsetof_timeof,
    main_body: r#"
    +20:
        loop {
            nop();
        }
    "#,
    decompile_args: ["--no-intrinsics"],
    sbsb: |decompiled| {
        // --nointrinsics should result in these
        assert!(decompiled.contains(r"offsetof"));
        assert!(decompiled.contains(r"timeof"));
        // and those should result in a label
        assert!(regex!(r#"label_\w+:"#).find(decompiled).is_some());
    },
);

source_test!(
    ECL_06, label_that_cant_use_timeof,
    main_body: r#"
    +20:
    label0:
        nop();
        goto label0 @ 30;
    "#,
    decompile_args: ["--no-intrinsics"],
    sbsb: |decompiled| {
        // --nointrinsics should result in this
        assert!(decompiled.contains(r"offsetof"));
        // but this can't use timeof in this case
        assert!(decompiled.contains(r"(30,"));
    },
);

source_test!(
    // Known failure for two reasons:
    //  * expect_decompile_warning + sbsb not implemented
    //  * even though a fallback to print hex for invalid offset arguments in `ins_`
    //    syntax is implemented, decompilation fails long before this point because all offsets
    //    are validated to guarantee that intrinsics can decompile.
    //   (so this is blocked on the ability to have intrinsics fall back to `ins_` syntax.)
    #[ignore]
    ECL_06, label_that_cant_use_offsetof,
    main_body: r#"
    +20:
        nop();
        jump(20, -0x40);
    "#,
    decompile_args: ["--no-intrinsics"],
    sbsb: |decompiled| {
        assert!(decompiled.contains(r"-0x40"));
        assert!(decompiled.contains(r"(30,"));
    },
    expect_decompile_warning: "invalid offset",
);

source_test!(
    ECL_06, weird_difficulty_mixed_loop,
    main_body: r#"
    +20:
    label:
    +10:
        nop();
    E:
        // the nops are to prevent difficulty labels from showing up
        // too close to something and making it not decompile
        nop();
        jump(timeof(label), offsetof(label));
        nop();
    HL:
        nop();
        jump(timeof(label), offsetof(label));
    "#,
    sbsb: |_| { /* just needs to roundtrip */ },
);

source_test!(
    // there are currently numerous places in the instruction raising code that have
    // to ask the label emitter to emit labels, so check that it indeed does so
    ECL_06, decompile_labels_before_smorgasboard,
    main_body: r#"
        // labels before long intrinsic
        +10:
        label1:
        cmp_int(I3, 3);
        jump_lss(timeof(foo), offsetof(foo));
        foo:
        goto label1;

        // labels before diff switch
        +10:
        label2:
        {"EN"}: I0 = 3;
        {"HL"}: I0 = 7;
        goto label2;

        // labels before instruction that falls back to raw
        +10:
        label3:
        set_int(3, 3);
        goto label3;

        // labels before blob
        +10:
        label4:
        ins_9999(@blob="00112233");
        goto label4;
    "#,
    sbsb: |decompiled| {
        // check that all labels and time labels decompiled
        assert_eq!(decompiled.matches("+10:").count(), 4);
        assert_eq!(decompiled.matches("loop {").count(), 4);

        // for specificity: make sure that each of these things actually decompiled
        assert!(decompiled.contains("if ($REG[-10004]")); // for the long intrinsic
        assert!(decompiled.contains(": 7 :")); // for the diff switch
        assert!(decompiled.contains("(3, 3)")); // for the fallback
        assert!(decompiled.contains("@blob=\"00112233\"")); // for the blob
    },
    expect_decompile_warning: expected::DECOMP_UNKNOWN_SIG,
);
