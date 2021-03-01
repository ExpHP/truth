use crate::integration_impl::formats::*;

#[test]
fn loop_simple() {
    STD_08.sbsb_test(r#"
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
    "#, |decompiled| {
        assert!(decompiled.contains("loop {"));
    });
}

#[test]
fn loop_nonzero_time() {
    // like above, but the label has a nonzero label
    STD_08.sbsb_test(r#"
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
    "#, |decompiled| {
        assert!(decompiled.contains("loop {"));
    });
}

#[test]
fn loop_previous_instr_time() {
    // in this one, the jump has the time of the previous instruction.
    // this should still be able to decompile a loop.
    STD_08.sbsb_test(r#"
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
    "#, |decompiled| {
        assert!(decompiled.contains("loop {"));
        assert!(decompiled.contains("+20:"));
        assert!(decompiled.find("loop {").unwrap() < decompiled.find("+20:").unwrap());
    });
}

#[test]
fn loop_other_time() {
    // this time the jump time is so weird we can't possibly decompile a loop
    STD_08.sbsb_test(r#"
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
    "#, |decompiled| {
        assert!(!decompiled.contains("loop {"));
    });
}

#[test]
fn two_loops_1_label() {
    STD_08.sbsb_test(r#"
    label:
        up(0.0, 1.0, -1.0);
        goto label;
        up(0.0, 1.0, -1.0);
        goto label;
    "#, |decompiled| {
        // should decompile to a nested loop
        assert!(decompiled.contains("loop {"));
        assert!(decompiled[decompiled.find("loop {").unwrap()..].contains("loop {"));
    });
}

#[test]
fn empty_loop() {
    STD_08.sbsb_test(r#"
    +10:
        posKeyframe(0.0, 0.0, 0.0);
    label:
        goto label;
        posKeyframe(0.0, 0.0, 0.0);
    "#, |decompiled| {
        assert!(decompiled.contains("loop {"));
    });
}

#[test]
fn empty_loop_time() {
    STD_08.sbsb_test(r#"
    +10:
        posKeyframe(0.0, 0.0, 0.0);
    +5:
    label:
        goto label @ 10;
        posKeyframe(0.0, 0.0, 0.0);
    "#, |decompiled| {
        // This should decompile to something like 'loop { +5: }'
        assert!(decompiled.contains("loop {"));
    });
}

#[test]
fn forward_jump() {
    STD_08.sbsb_test(r#"
        up(0.0, 1.0, -1.0);
    +10: // 10
        goto label_100;
        up(0.0, 1.0, -1.0);
    +1024: // 1034
    label_100:
        pos(0.0, 5240.0, 20.0);
    "#, |decompiled| {
        assert!(!decompiled.contains("loop {"));
    });
}

// =============================================================================

#[test]
fn if_elseif_else() {
    ANM_10.sbsb_test(r#"
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
    "#, |decompiled| {
        assert!(decompiled.contains(r#"
    if ($REG[10000] == 0) {
        ins_3(sprite2);
    } else if ($REG[10000] == 1) {
        ins_3(sprite3);
    } else {
        ins_3(sprite1);
    }"#.trim()));
    });
}

#[test]
fn if_else_refcount_gt_1() {
    // this one can't be fully decompiled to an if-else chain because one of the labels that would have
    // to be deleted is referenced somewhere else
    ANM_10.sbsb_test(r#"
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
    "#, |_decompiled| {
        // don't care so long as it compiles back
    })
}

#[test]
fn if_elseif_decrement() {
    ANM_10.sbsb_test(r#"
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
    "#, |_decompiled| {
        // don't care so long as it compiles back
    })
}

#[test]
fn if_elseif_time_1() {
    // This mismatched jump time should prevent if-else chain decompilation
    // (on an if jump)
    ANM_10.sbsb_test(r#"
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
    "#, |_decompiled| {
        // don't care so long as it compiles back
    })
}

#[test]
fn if_elseif_time_2() {
    // This mismatched jump time should prevent if-else chain decompilation
    // (on an unconditional jump-to-end)
    ANM_10.sbsb_test(r#"
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
    "#, |_decompiled| {
        // don't care so long as it compiles back
    })
}

#[test]
fn if_elseif_time_impossible_1() {
    // This has a time label change in a place where it is impossible to put
    // one in the decompiled 'if-else if' structure.
    ANM_10.sbsb_test(r#"
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
    "#, |_decompiled| {
        // don't care so long as it compiles back
    })
}

#[test]
fn if_elseif_time_sorta_possible() {
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
    ANM_10.sbsb_test(r#"
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
    "#, |_decompiled| {
        // don't care so long as it compiles back
    })
}

#[test]
fn if_elseif_time_impossible_2() {
    // another impossible spot for the time label change;
    // this one's basically inside the "else" keyword
    ANM_10.sbsb_test(r#"
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
    "#, |_decompiled| {
        // don't care so long as it compiles back
    })
}

#[test]
fn if_elseif_time_unimpossible() {
    // despite the pattern of the last three, this one's actually possible.
    // (the time label change is inside the else block)
    ANM_10.sbsb_test(r#"
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
    "#, |_decompiled| {
        // don't care so long as it compiles back
    })
}

#[test]
fn if_elseif_wrong_order() {
    // the cases here are not in source order (there's a backwards jump),
    // so they should be at least partially prevented from decompiling.
    ANM_10.sbsb_test(r#"
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
    "#, |_decompiled| {
        // don't care so long as it compiles back
    });
}

#[test]
fn if_elseif_end_before() {
    // end before the rest.  This should prevent decompilation.
    ANM_10.sbsb_test(r#"
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
    "#, |_decompiled| {
        // don't really care what this does, it probably decompiles into a bunch
        // of horrific looking nested loops.  Doesn't matter as long as it's correct.
    });
}

#[test]
fn goto_different_ends() {
    ANM_10.sbsb_test(r#"
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
    "#, |_decompiled| {
        // don't care so long as it compiles back
    });
}

#[test]
fn cond_jump_to_end() {
    // this has a conditional jump to the end.  shenanigans!
    ANM_10.sbsb_test(r#"
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
    "#, |_decompiled| {
        // don't care so long as it compiles back
    });
}
