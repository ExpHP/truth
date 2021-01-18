//! Tests that perform AST lowering with expression conversion to register-allocated locals (like in ANM
//! and early ECL).

#[macro_use]
extern crate truth;
use truth::{ast, llir, vm::AstVm, CompileError};
use truth::{Files, Eclmap, TypeSystem, ScalarValue, ScalarType as Ty, RegId};

use rand::Rng;

struct Var {
    reg: RegId,
    ty: Option<Ty>,
    name: Option<&'static str>,
    scratch: bool,
    in_mapfile: bool,
}

// Note: In these tests, instructions with opcodes < 100 are reserved for specially recognized instructions
//       and instructions named in the mapfile.  Use opcodes >= 100 for arbitrary instructions in the text.
fn make_eclmap(vars: &[Var]) -> Eclmap {
    let mut lines = vec![];
    lines.push(format!("!anmmap"));
    lines.push(format!("!gvar_types"));
    for var in vars.iter().filter(|x| x.in_mapfile) {
        if let Some(ty) = var.ty {
            lines.push(format!("{} {}", var.reg, ty.sigil()));
        }
    }
    lines.push(format!("!gvar_names"));
    for var in vars.iter().filter(|x| x.in_mapfile) {
        if let Some(name) = var.name {
            lines.push(format!("{} {}", var.reg, name));
        }
    }
    lines.push(format!("!ins_names"));
    lines.push(format!("70 nop"));
    lines.push(format!("71 func_SSff"));
    lines.push(format!("!ins_signatures"));
    lines.push(format!("70"));
    lines.push(format!("71 SSff"));
    Eclmap::parse(&lines.join("\n")).unwrap()
}

const ANTI_SCRATCH_OPCODE: u16 = 99;

fn make_instr_format(vars: &[Var]) -> impl llir::InstrFormat {
    let mut format = llir::TestFormat::default();
    format.intrinsic_opcode_pairs.push((llir::IntrinsicInstrKind::Jmp, 1));
    format.intrinsic_opcode_pairs.push((llir::IntrinsicInstrKind::CountJmp, 2));
    format.intrinsic_opcode_pairs.push((llir::IntrinsicInstrKind::Unop(ast::UnopKind::Sin, Ty::Float), 3));
    format.intrinsic_opcode_pairs.push((llir::IntrinsicInstrKind::Unop(ast::UnopKind::Cos, Ty::Float), 4));
    llir::register_assign_ops(&mut format.intrinsic_opcode_pairs, 10);
    llir::register_binary_ops(&mut format.intrinsic_opcode_pairs, 30);
    llir::register_cond_jumps(&mut format.intrinsic_opcode_pairs, 40);

    format.general_use_int_regs = vars.iter().filter(|x| x.ty == Some(Ty::Int) && x.scratch).map(|x| x.reg).collect();
    format.general_use_float_regs = vars.iter().filter(|x| x.ty == Some(Ty::Float) && x.scratch).map(|x| x.reg).collect();
    format.anti_scratch_opcode = Some(ANTI_SCRATCH_OPCODE);
    format
}

fn make_randomized_vm(vars: &[Var]) -> AstVm {
    let mut rng = rand::thread_rng();

    let mut vm = AstVm::new().with_max_iterations(10000);
    for var in vars {
        match var.ty {
            Some(Ty::Int) => vm.set_reg(var.reg, ScalarValue::Int(rng.gen_range(-7, 7+1))),
            Some(Ty::Float) => vm.set_reg(var.reg, ScalarValue::Float({
                let sign = rng.gen_range(0, 2) - 1;
                sign as f32 * rng.gen_range(0.3, 1.7)
            })),
            None => vm.set_reg(var.reg, ScalarValue::Int(0)),
        }
    }
    vm
}

const REG_A: RegId = RegId(1000);
const REG_B: RegId = RegId(1001);
const REG_C: RegId = RegId(1002);
const REG_D: RegId = RegId(1003);
const REG_X: RegId = RegId(1004);
const REG_Y: RegId = RegId(1005);
const REG_Z: RegId = RegId(1006);
const REG_W: RegId = RegId(1007);
const REG_COUNT: RegId = RegId(1020);

const SIMPLE_FOUR_VAR_SPEC: &'static [Var] = &[
    Var { reg: REG_A, ty: Some(Ty::Int), name: Some("A"), scratch: true, in_mapfile: true },
    Var { reg: REG_B, ty: Some(Ty::Int), name: Some("B"), scratch: true, in_mapfile: true },
    Var { reg: REG_C, ty: Some(Ty::Int), name: Some("C"), scratch: true, in_mapfile: true },
    Var { reg: REG_D, ty: Some(Ty::Int), name: Some("D"), scratch: true, in_mapfile: true },
    Var { reg: REG_X, ty: Some(Ty::Float), name: Some("X"), scratch: true, in_mapfile: true },
    Var { reg: REG_Y, ty: Some(Ty::Float), name: Some("Y"), scratch: true, in_mapfile: true },
    Var { reg: REG_Z, ty: Some(Ty::Float), name: Some("Z"), scratch: true, in_mapfile: true },
    Var { reg: REG_W, ty: Some(Ty::Float), name: Some("W"), scratch: true, in_mapfile: true },
    Var { reg: REG_COUNT, ty: Some(Ty::Int), name: Some("COUNT"), scratch: false, in_mapfile: true },
];

const NOMAP_FOUR_VAR_SPEC: &'static [Var] = &[
    Var { reg: REG_A, ty: Some(Ty::Int), name: None, scratch: true, in_mapfile: false },
    Var { reg: REG_B, ty: Some(Ty::Int), name: None, scratch: true, in_mapfile: false },
    Var { reg: REG_C, ty: Some(Ty::Int), name: None, scratch: true, in_mapfile: false },
    Var { reg: REG_D, ty: Some(Ty::Int), name: None, scratch: true, in_mapfile: false },
    Var { reg: REG_X, ty: Some(Ty::Float), name: None, scratch: true, in_mapfile: false },
    Var { reg: REG_Y, ty: Some(Ty::Float), name: None, scratch: true, in_mapfile: false },
    Var { reg: REG_Z, ty: Some(Ty::Float), name: None, scratch: true, in_mapfile: false },
    Var { reg: REG_W, ty: Some(Ty::Float), name: None, scratch: true, in_mapfile: false },
    Var { reg: REG_COUNT, ty: Some(Ty::Int), name: None, scratch: false, in_mapfile: false },
];

// A slightly more constrained spec with only three scratch vars.
const SIMPLE_THREE_VAR_SPEC: &'static [Var] = &[
    Var { reg: REG_A, ty: Some(Ty::Int), name: Some("A"), scratch: true, in_mapfile: true },
    Var { reg: REG_B, ty: Some(Ty::Int), name: Some("B"), scratch: true, in_mapfile: true },
    Var { reg: REG_C, ty: Some(Ty::Int), name: Some("C"), scratch: true, in_mapfile: true },
    Var { reg: REG_X, ty: Some(Ty::Float), name: Some("W"), scratch: true, in_mapfile: true },
    Var { reg: REG_Y, ty: Some(Ty::Float), name: Some("X"), scratch: true, in_mapfile: true },
    Var { reg: REG_Z, ty: Some(Ty::Float), name: Some("Y"), scratch: true, in_mapfile: true },
    Var { reg: REG_COUNT, ty: Some(Ty::Int), name: Some("COUNT"), scratch: false, in_mapfile: true },
];


/// Construct two `AstVm`s with the same randomly initialized state, then:
///
/// * Run one on the input source text.
/// * Run the other one on what you end up with after lowering the source to Instrs
///   (with expression compilation) and then raising it back into Stmts.
///
/// The second input will have had its complicated expressions compiled into more primitive
/// statements that make use of scratch variables.  This scratch variable usage may cause
/// the final value of some registers to differ between the two; but this should be the
/// only difference.
///
/// This function will automatically check that the `time`, `real_time`, and `call_log`
/// match.  Then it returns the VMs so that the caller can check the equality of any registers
/// that it knows should not have been used for scratch.
#[track_caller]
fn run_randomized_test(vars: &[Var], text: &str) -> (AstVm, AstVm) {
    let mut files = Files::new();
    _run_randomized_test(&mut files, vars, text)
        .unwrap_or_else(|e| panic!("{}", e.to_string(&files).unwrap()))
}

#[track_caller]
fn _run_randomized_test(files: &mut Files, vars: &[Var], text: &str) -> Result<(AstVm, AstVm), CompileError> {
    let mut ty_ctx = TypeSystem::new();

    let eclmap = make_eclmap(vars);
    let instr_format = make_instr_format(vars);
    let base_vm = make_randomized_vm(vars);
    ty_ctx.extend_from_eclmap("<mapfile>".as_ref(), &eclmap);

    let parsed_block = {
        use ast::VisitMut;

        let mut block = files.parse::<ast::Block>("<input>", text.as_ref())?.value;
        ty_ctx.resolve_names(&mut block)?;

        let mut visitor = truth::passes::desugar_blocks::Visitor::new(&mut ty_ctx);
        visitor.visit_block(&mut block);
        visitor.finish()?;

        block
    };

    let old_code = parsed_block.0;
    let instrs = llir::lower_sub_ast_to_instrs(&instr_format, &old_code, &mut ty_ctx)?;
    let new_code = llir::raise_instrs_to_sub_ast(&instr_format, &instrs, &ty_ctx.regs_and_instrs)?;

    let mut old_vm = base_vm.clone();
    let mut new_vm = base_vm.clone();
    eprintln!("{}", truth::fmt::stringify(&ast::Block(new_code.clone())));
    old_vm.run(&old_code);
    new_vm.run(&new_code);

    assert_eq!(old_vm.time, new_vm.time, "time");
    assert_eq!(old_vm.real_time, new_vm.real_time, "real_time");
    assert_eq!(old_vm.call_log, new_vm.call_log);
    Ok((old_vm, new_vm))
}

/// Checks that attempting to compile this produces a "no more registers of this type" error.
#[track_caller]
fn expect_not_enough_vars(vars: &[Var], text: &str) {
    let mut files = Files::new();
    let mut ty_ctx = TypeSystem::new();

    let eclmap = make_eclmap(vars);
    let instr_format = make_instr_format(vars);
    ty_ctx.extend_from_eclmap("<mapfile>".as_ref(), &eclmap);

    let parsed_block = {
        use ast::VisitMut;

        let mut block = files.parse::<ast::Block>("<input>", text.as_ref()).unwrap().value;
        ty_ctx.resolve_names(&mut block).unwrap();

        let mut visitor = truth::passes::desugar_blocks::Visitor::new(&mut ty_ctx);
        visitor.visit_block(&mut block);
        visitor.finish().unwrap();

        block
    };

    let err = llir::lower_sub_ast_to_instrs(&instr_format, &parsed_block.0, &mut ty_ctx).unwrap_err();
    let err_s = err.to_string(&files).unwrap();
    assert!(err_s.contains("no more registers of this type"), "{}", err_s);
}

#[track_caller]
fn check_all_regs_of_ty(vars: &[Var], old: &AstVm, new: &AstVm, ty: Ty) {
    for var in vars {
        if var.ty == Some(ty) {
            assert_eq!(old.get_reg(var.reg), new.get_reg(var.reg), "reg {}", var.reg);
        }
    }
}

#[test]
fn vars() {
    // Three source files that should produce identical results
    let tests = vec![
        ("simple_test", SIMPLE_FOUR_VAR_SPEC, r#"{
            int x = 4 + 3 * B, y;
            y = x * x;
            A = x;
        }"#),
        // (check with a raw register access)
        ("simple_test_with_raw", SIMPLE_FOUR_VAR_SPEC, r#"{
            int x = 4 + 3 * [1001], y;
            y = x * x;
            A = x;
        }"#),
        // (check with a read of a non-scratch register)
        ("simple_test_with_nonscratch", SIMPLE_FOUR_VAR_SPEC, r#"{
            int x = 4 + 3 * [1001], y;
            y = x * COUNT;
            A = x;
        }"#),
        // (expression compilation should not require a mapfile to work)
        ("simple_test_nomap", NOMAP_FOUR_VAR_SPEC, r#"{
            int x = 4 + 3 * [1001], y;
            y = x * x;
            [1000] = x;
        }"#),
    ];

    for (test_name, vars, source) in tests {
        for _ in 0..10 {
            let (old_vm, new_vm) = run_randomized_test(vars, source);

            // These can't be scratch vars because they were used
            assert_eq!(old_vm.get_reg(REG_A), new_vm.get_reg(REG_A), "{}", test_name);
            assert_eq!(old_vm.get_reg(REG_B), new_vm.get_reg(REG_B), "{}", test_name);
            // This one is not general purpose so it's ineligible for scratch use
            assert_eq!(old_vm.get_reg(REG_COUNT), new_vm.get_reg(REG_COUNT), "{}", test_name);
            // Float registers were not needed for scratch purposes
            check_all_regs_of_ty(vars, &old_vm, &new_vm, Ty::Float);
        }
    }
}

#[test]
fn float_uses_detected() {
    // Regression test to make sure that float-typed reads are counted as uses.
    for _ in 0..10 {
        // This is designed to fail if any register other than Y is assigned for the local.
        // (Y is in the middle of the scratch vars list, so this can't happen just on accident)
        let (old_vm, new_vm) = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, r#"{
            float x = X + Z;
            W = x;
        }"#);
        assert_eq!(old_vm.get_reg(REG_X), new_vm.get_reg(REG_X));
        assert_eq!(old_vm.get_reg(REG_Z), new_vm.get_reg(REG_Z));
        assert_eq!(old_vm.get_reg(REG_W), new_vm.get_reg(REG_W));

        // Likewise for float-typed reads of integer registers.
        let (old_vm, new_vm) = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, r#"{
            int x = _S(%A + %C);
            D = x;
        }"#);
        assert_eq!(old_vm.get_reg(REG_A), new_vm.get_reg(REG_A));
        assert_eq!(old_vm.get_reg(REG_C), new_vm.get_reg(REG_C));
        assert_eq!(old_vm.get_reg(REG_D), new_vm.get_reg(REG_D));
    }

}

#[test]
fn cast() {
    // A variable should still be recognized as ineligible for scratch use even if only read as the other type.
    for _ in 0..10 {
        let vars = SIMPLE_FOUR_VAR_SPEC;
        let (old_vm, new_vm) = run_randomized_test(vars, r#"{
            int x = 4 + 3 * $X, y;
            y = x * x;
            A = x;
            float a = (3.0 + W) * (5.0 + W);  // this should use Y and Z for scratch, not X.
        }"#);

        let x = old_vm.get_reg(REG_X).unwrap().read_as_float() as i32 * 3 + 4;
        assert_eq!(old_vm.get_reg(REG_A), Some(ScalarValue::Int(x)), "{}", old_vm);

        assert_eq!(old_vm.get_reg(REG_A), new_vm.get_reg(REG_A), "{}\n{}", old_vm, new_vm);
        assert_eq!(old_vm.get_reg(REG_X), new_vm.get_reg(REG_X), "{}\n{}", old_vm, new_vm);
        assert_eq!(old_vm.get_reg(REG_W), new_vm.get_reg(REG_W), "{}\n{}", old_vm, new_vm);
    }
}

#[test]
fn local_scope() {
    // check that local variables should stop taking up a register at the end of their lexical scope
    // FIXME: Simplify this test's source after implementing `while (--lol)` or `if (true) { ... }`
    for _ in 0..10 {
        let source = r#"{
            int lol = 1;
            do {
                int a = 1, b = 2;
                int c = 3;
                ins_999(a, b, c);
            } while (lol == 0);
            lol = 1;
            do {
                int d = 4, e = 5;
                int f = 6;
                ins_999(d, e, f);
            } while (lol == 0);
        }"#;

        // first, demonstrate that the test does fail when there aren't enough scratch registers
        // (lol, a, b, and c require four regs)
        expect_not_enough_vars(SIMPLE_THREE_VAR_SPEC, source);
        // now, show that four regs is enough, demonstrating that the registers for a, b, and c
        // are freed when they fall out of scope
        run_randomized_test(SIMPLE_FOUR_VAR_SPEC, source);
    }
}

// Tests which should require NO scratch variables.  These test to make sure that operations
// implementable as a single instruction are properly recognized as such.
mod no_scratch {
    use super::*;

    #[track_caller]
    fn check_no_scratch(vars: &[Var], source: &str) {
        let (old_vm, new_vm) = run_randomized_test(vars, source);

        // if no scratch vars were used, then the two VMs should be in identical states
        check_all_regs_of_ty(vars, &old_vm, &new_vm, Ty::Int);
        check_all_regs_of_ty(vars, &old_vm, &new_vm, Ty::Float);
    }

    #[test]
    fn direct_assign() {
        for _ in 0..5 {
            let vars = SIMPLE_FOUR_VAR_SPEC;
            let (old_vm, new_vm) = run_randomized_test(vars, r#"{
                A = A;
                A = B;
                W = W;
                A = $X;
            }"#);
            check_all_regs_of_ty(vars, &old_vm, &new_vm, Ty::Int);
            check_all_regs_of_ty(vars, &old_vm, &new_vm, Ty::Float);
        }
    }

    #[test]
    fn binop_3() {
        for _ in 0..5 {
            check_no_scratch(SIMPLE_FOUR_VAR_SPEC, r#"{
                A = B + C;
                A = A * A;
                A = $X + $Y;
            }"#);
        }
    }

    #[test]
    fn assign_op() {
        for _ in 0..5 {
            check_no_scratch(SIMPLE_FOUR_VAR_SPEC, r#"{
                A *= A;
                A += B;
                A *= $Y;
            }"#);
        }
    }

    #[test]
    fn cond_jmp_compare() {
        for _ in 0..5 {
            check_no_scratch(SIMPLE_FOUR_VAR_SPEC, r#"{
                if (A == B) goto hi;
                if (A == $X) goto hi;
                if (A == 2) goto hi;
                ins_400();
            hi:
                if (A != A) goto hi;
            }"#);
        }
    }

    #[test]
    fn cond_jmp_logic_binop() {
        for _ in 0..5 {
            check_no_scratch(SIMPLE_FOUR_VAR_SPEC, r#"{
                if (A && B && C) goto hi;
            hi:
                if (A || B || C) goto lo;
            lo:
            }"#);
        }
    }

    #[test]
    fn cond_jmp_predecrement() {
        for _ in 0..5 {
            check_no_scratch(SIMPLE_FOUR_VAR_SPEC, r#"{
                if (--A) goto hi;
            hi:
                unless (--A) goto lo;
            lo:
            }"#);
        }
    }

    #[test]
    fn cond_jmp_negated_compare() {
        for _ in 0..5 {
            check_no_scratch(SIMPLE_FOUR_VAR_SPEC, r#"{
                if (!(!(!(!(A < B))))) goto hi;
                if (!(!(!(A < B)))) goto hi;
            hi:
            }"#);
        }
    }

    #[test]
    fn cond_jmp_negated_logic_binop() {
        for _ in 0..5 {
            check_no_scratch(SIMPLE_FOUR_VAR_SPEC, r#"{
                if (!(!(!(!((A > 2) && !(A > 0)))))) goto hi;
                if (!(!(!((A > 2) && !(A > 0))))) goto hi;
            hi:
            }"#);
        }
    }

    #[test]
    fn cond_jmp_atom() {
        for _ in 0..5 {
            // `if (<expr>)` can automatically be reinterpreted as `if (<expr> != 0)`
            check_no_scratch(SIMPLE_FOUR_VAR_SPEC, r#"{
                if (A) goto hi;
                ins_400();
            hi:
                if (0) goto hi;
            }"#);
        }
    }

    #[test]
    fn unop() {
        for _ in 0..5 {
            check_no_scratch(SIMPLE_FOUR_VAR_SPEC, r#"{
                A = -A;
                B = -A;
                B = -3;
            }"#);
        }
    }

    #[test]
    fn ins_call() {
        for _ in 0..5 {
            check_no_scratch(SIMPLE_FOUR_VAR_SPEC, r#"{
                func_SSff(A, 2, 6.0, %B);
            }"#);
        }
    }

    #[test]
    fn out_reg_reuse() {
        for _ in 0..5 {
            // these entire expressions can be computed by repeatedly modifying A or X
            // (and this can be done without even rearranging execution order in any manner)
            check_no_scratch(SIMPLE_FOUR_VAR_SPEC, r#"{
                A = B + B * -(B * (C + -A + C + C) + B);
                X = Y + cos(Y * (Y * sin(Z + -X + Z + Z) + Y));
            }"#);
        }
    }
}

struct CheckBoolVms {
    new_if_vm: AstVm,
    new_unless_vm: AstVm,
}

/// Checks that `if (<cond>)` and `unless (<cond>)` choose the correct branches.
///
/// (`expected` is what the condition is expected to conceptually evaluate to, as a boolean)
#[track_caller]
fn check_bool(init: &str, cond: &str, expected: bool) -> CheckBoolVms {
    let (_, new_if_vm) = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, &format!(r#"{{
        {}
        if ({}) goto hi;
        ins_700();
      hi:
    }}"#, init, cond));
    let (_, new_unless_vm) = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, &format!(r#"{{
        {}
        unless ({}) goto hi;
        ins_700();
      hi:
    }}"#, init, cond));

    // For 'if', the call should be skipped if the condition is true.
    assert_eq!(new_if_vm.call_log.len(), 1 - (expected as usize));
    assert_eq!(new_unless_vm.call_log.len(), expected as usize);
    CheckBoolVms { new_if_vm, new_unless_vm }
}

#[test]
fn cond_jump_non_binop() {
    check_bool("", "0", false);
    check_bool("", "1", true);
    check_bool("", "-0", false);
    check_bool("A=2;", "-A", true);
    check_bool("", "_S(0.0)", false);
    check_bool("", "_S(1.0)", true);
}

#[test]
fn cond_jump_non_comparison_binop() {
    check_bool("A=2;", "A * A", true);
}

#[test]
fn cond_jump_logical_negations() {
    check_bool("A=1; B=4;", "A < B", true);
    check_bool("A=4; B=4;", "A < B", false);
    check_bool("A=1; B=4;", "!(A < B)", false);
    check_bool("A=4; B=4;", "!(A < B)", true);
    check_bool("", "!(0)", true);
    check_bool("", "!(_S(1.0))", false);
    check_bool("A=2;", "!(A * A)", false);
}

#[test]
fn cond_jump_logical_binop() {
    check_bool("A=3;", "(A < 3) || (A < 5)", true);
    check_bool("A=3;", "(A < 3) && (A < 5)", false);
    check_bool("A=3;", "(A < 3) || !(A < 5)", false);
    // With negations too! (inside and around)
    check_bool("A=3;", "!(A < 3) && (A < 5)", true);
    check_bool("A=3;", "!(!(A < 3) && (A < 5))", false);
}

#[test]
fn cond_jump_logical_binop_exhaustive() {
    let or: fn(bool, bool) -> bool = |a, b| a || b;
    let and: fn(bool, bool) -> bool = |a, b| a && b;

    for (logic_op, logic_func) in vec![(token![||], or), (token![&&], and)] {
        for (a_str, a_bool) in vec![("A < B", true), ("A > B", false)] {
            for (b_str, b_bool) in vec![("A < B", true), ("A > B", false)] {
                let cond_str = format!("({}) {} ({})", a_str, logic_op, b_str);
                check_bool("A=1; B=2;", &cond_str, logic_func(a_bool, b_bool));
            }
        }
    }
}

#[test]
fn if_unless_predecrement() {
    let vms = check_bool("A=3;", "--A", true);
    assert_eq!(vms.new_if_vm.get_reg(REG_A).unwrap(), ScalarValue::Int(2));
    assert_eq!(vms.new_unless_vm.get_reg(REG_A).unwrap(), ScalarValue::Int(2));

    let vms = check_bool("A=1;", "--A", false);
    assert_eq!(vms.new_if_vm.get_reg(REG_A).unwrap(), ScalarValue::Int(0));
    assert_eq!(vms.new_unless_vm.get_reg(REG_A).unwrap(), ScalarValue::Int(0));

    let vms = check_bool("A=0;", "--A", true);
    assert_eq!(vms.new_if_vm.get_reg(REG_A).unwrap(), ScalarValue::Int(-1));
    assert_eq!(vms.new_unless_vm.get_reg(REG_A).unwrap(), ScalarValue::Int(-1));
}

#[test]
fn cast_assignment() {
    for _ in 0..10 {
        // this hits a tiny special little code path that most casts don't hit, where it is
        // immediately assigned to a variable.
        let vars = SIMPLE_FOUR_VAR_SPEC;
        let (old_vm, new_vm) = run_randomized_test(vars, r#"{
            X = _f(A + 4);
        }"#);

        check_all_regs_of_ty(vars, &old_vm, &new_vm, Ty::Float);
    }
}

#[test]
fn careful_cast_temporaries() {
    // A cast may create a temporary of its argument's type, but it should never create a temporary
    // of its output type. (because whatever's using it can simply read the temporary as that type)
    for _ in 0..10 {
        let vars = SIMPLE_FOUR_VAR_SPEC;
        // None of these should create an integer temporary
        let (old_vm, new_vm) = run_randomized_test(vars, r#"{
            ins_606(_S(%X + 4.0));
            A = A + _S(%X + 4.0);
        }"#);

        check_all_regs_of_ty(vars, &old_vm, &new_vm, Ty::Int);
    }
}

#[test]
fn binop_optimization_correctness() {
    let subexprs = vec![
        "A",  // the variable we're assigning
        "B",  // another atomic expression
        "(B * (1 + A))",  // a non-atomic expression with A, even hiding it a bit inwards to defeat dumb implementations
        "(B * (1 + B))",  // a non-atomic expression without A
    ];

    for &expr_1 in &subexprs {
        for &expr_2 in &subexprs {
            let vars = SIMPLE_FOUR_VAR_SPEC;
            let (old_vm, new_vm) = run_randomized_test(vars, &format!(r#"{{
                A = {} + {};
                B = B;  // guarantee that B is considered used so we can assert on it
            }}"#, expr_1, expr_2));

            assert_eq!(old_vm.get_reg(REG_A), new_vm.get_reg(REG_A));
            assert_eq!(old_vm.get_reg(REG_B), new_vm.get_reg(REG_B));

            // Float vars were not needed for scratch purposes
            check_all_regs_of_ty(vars, &old_vm, &new_vm, Ty::Float);
        }
    }
}

#[test]
fn unop_optimization_correctness() {
    let subexprs = vec![
        "X",  // the variable we're assigning
        "Y",  // another atomic expression
        "(Y * (1.0 + X))",  // a non-atomic expression with A, even hiding it a bit inwards to defeat dumb implementations
        "(Y * (1.0 + Y))",  // a non-atomic expression without A
    ];

    for oper in vec!["-", "sin"] {
        for &expr_1 in &subexprs {
            let vars = SIMPLE_FOUR_VAR_SPEC;
            let (old_vm, new_vm) = run_randomized_test(vars, &format!(r#"{{
                X = {}({});
                Y = Y;  // guarantee that Y is considered used so we can assert on it
            }}"#, oper, expr_1));

            assert_eq!(old_vm.get_reg(REG_X), new_vm.get_reg(REG_X));
            assert_eq!(old_vm.get_reg(REG_Y), new_vm.get_reg(REG_Y));

            check_all_regs_of_ty(vars, &old_vm, &new_vm, Ty::Int);
        }
    }
}

mod anti_scratch_regs {
    use super::*;

    #[test]
    fn safe() {
        run_randomized_test(SIMPLE_FOUR_VAR_SPEC, &format!(r#"{{
            A = B + B * -A;  // requires no scratch
            ins_{}();
        }}"#, ANTI_SCRATCH_OPCODE));
    }

    #[test]
    #[should_panic(expected = "scratch registers are disabled")]
    fn bad_before() {
        run_randomized_test(SIMPLE_FOUR_VAR_SPEC, &format!(r#"{{
            A = A + B * -A;  // requires scratch!
            ins_{}();
        }}"#, ANTI_SCRATCH_OPCODE));
    }

    #[test]
    #[should_panic(expected = "scratch registers are disabled")]
    fn bad_after() {
        // (this is to make sure the check doesn't depend on instruction order...)
        run_randomized_test(SIMPLE_FOUR_VAR_SPEC, &format!(r#"{{
            ins_{}();
            A = A + B * -A;  // requires scratch!
        }}"#, ANTI_SCRATCH_OPCODE));
    }
}

#[test]
fn weird_crash() {
    for _ in 0..10 {
        run_randomized_test(SIMPLE_FOUR_VAR_SPEC, r#"{
            times(2) {
                times(A) {
                    times(3) {
                        ins_300(1 + 5);
                    }
                }
            }
        }"#);
    }
}
