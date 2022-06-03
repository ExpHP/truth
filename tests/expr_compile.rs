//! Tests that perform AST lowering with expression conversion to register-allocated locals (like in ANM
//! and early ECL).

#[macro_use]
extern crate truth;
use truth::{ast, llir, vm::AstVm};
use truth::{Truth, ScalarValue, ScalarType as Ty, RegId};

use rand::Rng;

#[derive(Clone)]
struct Var {
    reg: RegId,
    ty: Option<Ty>,
    name: Option<&'static str>,
    scratch: bool,
    in_mapfile: bool,
    special: Option<truth::vm::SpecialVarKind>,
}

const JUMP_OPCODE: u16 = 1;
const COUNT_JUMP_OPCODE: u16 = 2;
const SINE_OPCODE: u16 = 3;
const COSINE_OPCODE: u16 = 4;
const LT_FLOAT_OPCODE: u16 = 5;
const ASSIGN_OPS_OPCODE: u16 = 10;
const BINARY_OPS_OPCODE: u16 = 30;
const COND_JUMPS_OPCODE: u16 = 40;
const ANTI_SCRATCH_OPCODE: u16 = 99;
const NOP_OPCODE: u16 = 70;
const OTHER_OPCODE: u16 = 100;

// Note: In these tests, instructions with opcodes < 100 are reserved for specially recognized instructions
//       and instructions named in the mapfile.  Use opcodes >= 100 for arbitrary instructions in the text.
fn load_mapfile(truth: &mut Truth, vars: &[Var]) {
    let mut lines = vec![];
    lines.push(format!("!anmmap"));
    lines.push(format!("!gvar_types"));
    for var in vars.iter().filter(|x| x.in_mapfile) {
        if let Some(ty_sigil) = var.ty.and_then(ast::VarSigil::from_ty) {
            lines.push(format!("{} {}", var.reg, ty_sigil));
        }
    }
    lines.push(format!("!gvar_names"));
    for var in vars.iter().filter(|x| x.in_mapfile) {
        if let Some(name) = var.name {
            lines.push(format!("{} {}", var.reg, name));
        }
    }
    let mut ins_names_lines = vec![
        format!("{} nop", NOP_OPCODE),
        format!("{} foo", OTHER_OPCODE),
        format!("{} bar", OTHER_OPCODE + 1),
    ];
    let mut ins_signatures_lines = vec![
        format!("{} ot", JUMP_OPCODE),
        format!("{} Sot", COUNT_JUMP_OPCODE),
        format!("{} ff", SINE_OPCODE),
        format!("{} ff", COSINE_OPCODE),
        format!("{} Sff", LT_FLOAT_OPCODE),
        format!("{}", ANTI_SCRATCH_OPCODE),
        format!("{}", NOP_OPCODE),
        format!("{}", OTHER_OPCODE),
        format!("{}", OTHER_OPCODE + 1),
    ];

    let mut oper_opcodes = ASSIGN_OPS_OPCODE..;
    for _ in 0..6 {
        let s_opcode = oper_opcodes.next().unwrap();
        let f_opcode = oper_opcodes.next().unwrap();
        ins_signatures_lines.push(format!("{} SS", s_opcode));
        ins_signatures_lines.push(format!("{} ff", f_opcode));
    }

    let mut oper_opcodes = BINARY_OPS_OPCODE..;
    for _ in 0..5 {
        let s_opcode = oper_opcodes.next().unwrap();
        let f_opcode = oper_opcodes.next().unwrap();
        ins_signatures_lines.push(format!("{} SSS", s_opcode));
        ins_signatures_lines.push(format!("{} fff", f_opcode));
    }

    let mut oper_opcodes = COND_JUMPS_OPCODE..;
    for _ in 0..6 {
        let s_opcode = oper_opcodes.next().unwrap();
        let f_opcode = oper_opcodes.next().unwrap();
        ins_signatures_lines.push(format!("{} SSot", s_opcode));
        ins_signatures_lines.push(format!("{} ffot", f_opcode));
    }

    let mut unused_opcodes = OTHER_OPCODE + 2..;
    for base in vec!["foo", "bar"] {
        for siggy_len in 1..=4 {
            for siggy_chars in permutations_with_replacement(&["S", "f"], siggy_len) {
                let siggy = siggy_chars.join("");
                let opcode = unused_opcodes.next().unwrap();
                ins_signatures_lines.push(format!("{} {}", opcode, siggy));
                ins_names_lines.push(format!("{} {}_{}", opcode, base, siggy));
            }
        }
    }

    lines.push(format!("!ins_names"));
    lines.extend(ins_names_lines);
    lines.push(format!("!ins_signatures"));
    lines.extend(ins_signatures_lines);
    truth.apply_mapfile_str(&lines.join("\n"), truth::Game::Th10)
        .unwrap_or_else(|_| panic!("{}", truth.get_captured_diagnostics().unwrap()));
}

fn permutations_with_replacement<T: Clone>(items: &[T], count: usize) -> Vec<Vec<T>> {
    if count == 0 {
        return vec![vec![]];
    }
    let mut with_more = vec![];
    let with_fewer = permutations_with_replacement(items, count - 1);
    for fewer in with_fewer {
        for item in items {
            let mut more = fewer.clone();
            more.push(item.clone());
            with_more.push(more);
        }
    }
    with_more
}

fn make_language(vars: &[Var]) -> impl llir::LanguageHooks {
    use llir::IntrinsicInstrKind as I;

    let mut format = llir::TestLanguage::default();
    format.language = truth::LanguageKey::Anm;
    format.intrinsic_opcode_pairs.push((I::Jmp, JUMP_OPCODE));
    format.intrinsic_opcode_pairs.push((I::CountJmp, COUNT_JUMP_OPCODE));
    format.intrinsic_opcode_pairs.push((I::UnOp(ast::UnOpKind::Sin, Ty::Float), SINE_OPCODE));
    format.intrinsic_opcode_pairs.push((I::UnOp(ast::UnOpKind::Cos, Ty::Float), COSINE_OPCODE));
    I::register_assign_ops(&mut format.intrinsic_opcode_pairs, ASSIGN_OPS_OPCODE);
    I::register_binary_ops(&mut format.intrinsic_opcode_pairs, BINARY_OPS_OPCODE);
    I::register_cond_jumps(&mut format.intrinsic_opcode_pairs, COND_JUMPS_OPCODE);
    format.intrinsic_opcode_pairs.push((I::BinOp(ast::BinOpKind::Lt, Ty::Float), LT_FLOAT_OPCODE));

    format.general_use_int_regs = vars.iter().filter(|x| x.ty == Some(Ty::Int) && x.scratch).map(|x| x.reg).collect();
    format.general_use_float_regs = vars.iter().filter(|x| x.ty == Some(Ty::Float) && x.scratch).map(|x| x.reg).collect();
    format.anti_scratch_opcode = Some(ANTI_SCRATCH_OPCODE);
    format
}

fn make_randomized_vm(vars: &[Var]) -> AstVm {
    let mut vm = AstVm::new().with_max_iterations(10000);
    for var in vars {
        if let Some(special) = &var.special {
            vm.set_reg(var.reg, special.clone());
        } else {
            set_random_value(&mut vm, var.reg, var.ty);
        }
    }

    let difficulty = rand::thread_rng().gen_range(0, 4);
    vm.with_difficulty(difficulty)
}

fn set_random_value(vm: &mut AstVm, reg: RegId, ty: Option<Ty>) {
    let mut rng = rand::thread_rng();
    match ty {
        Some(Ty::Int) => vm.set_reg(reg, ScalarValue::Int(rng.gen_range(-7, 7+1))),
        Some(Ty::Float) => vm.set_reg(reg, ScalarValue::Float({
            let sign = rng.gen_range(0, 2) - 1;
            sign as f32 * rng.gen_range(0.3, 1.7)
        })),
        Some(Ty::String) => panic!("nonsense string register!"),
        None => vm.set_reg(reg, ScalarValue::Int(0)),
    }
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
const REG_TY_VOLATILE: RegId = RegId(2001);
const REG_COUNTER: RegId = RegId(2002);

const SIMPLE_FOUR_VAR_SPEC: &'static [Var] = &[
    Var { reg: REG_A, ty: Some(Ty::Int), name: Some("A"), scratch: true, in_mapfile: true, special: None },
    Var { reg: REG_B, ty: Some(Ty::Int), name: Some("B"), scratch: true, in_mapfile: true, special: None },
    Var { reg: REG_C, ty: Some(Ty::Int), name: Some("C"), scratch: true, in_mapfile: true, special: None },
    Var { reg: REG_D, ty: Some(Ty::Int), name: Some("D"), scratch: true, in_mapfile: true, special: None },
    Var { reg: REG_X, ty: Some(Ty::Float), name: Some("X"), scratch: true, in_mapfile: true, special: None },
    Var { reg: REG_Y, ty: Some(Ty::Float), name: Some("Y"), scratch: true, in_mapfile: true, special: None },
    Var { reg: REG_Z, ty: Some(Ty::Float), name: Some("Z"), scratch: true, in_mapfile: true, special: None },
    Var { reg: REG_W, ty: Some(Ty::Float), name: Some("W"), scratch: true, in_mapfile: true, special: None },
    Var { reg: REG_COUNT, ty: Some(Ty::Int), name: Some("COUNT"), scratch: false, in_mapfile: true, special: None },
];

const NOMAP_FOUR_VAR_SPEC: &'static [Var] = &[
    Var { reg: REG_A, ty: Some(Ty::Int), name: None, scratch: true, in_mapfile: false, special: None },
    Var { reg: REG_B, ty: Some(Ty::Int), name: None, scratch: true, in_mapfile: false, special: None },
    Var { reg: REG_C, ty: Some(Ty::Int), name: None, scratch: true, in_mapfile: false, special: None },
    Var { reg: REG_D, ty: Some(Ty::Int), name: None, scratch: true, in_mapfile: false, special: None },
    Var { reg: REG_X, ty: Some(Ty::Float), name: None, scratch: true, in_mapfile: false, special: None },
    Var { reg: REG_Y, ty: Some(Ty::Float), name: None, scratch: true, in_mapfile: false, special: None },
    Var { reg: REG_Z, ty: Some(Ty::Float), name: None, scratch: true, in_mapfile: false, special: None },
    Var { reg: REG_W, ty: Some(Ty::Float), name: None, scratch: true, in_mapfile: false, special: None },
    Var { reg: REG_COUNT, ty: Some(Ty::Int), name: None, scratch: false, in_mapfile: false, special: None },
];

// A slightly more constrained spec with only three scratch vars.
const SIMPLE_THREE_VAR_SPEC: &'static [Var] = &[
    Var { reg: REG_A, ty: Some(Ty::Int), name: Some("A"), scratch: true, in_mapfile: true, special: None },
    Var { reg: REG_B, ty: Some(Ty::Int), name: Some("B"), scratch: true, in_mapfile: true, special: None },
    Var { reg: REG_C, ty: Some(Ty::Int), name: Some("C"), scratch: true, in_mapfile: true, special: None },
    Var { reg: REG_X, ty: Some(Ty::Float), name: Some("W"), scratch: true, in_mapfile: true, special: None },
    Var { reg: REG_Y, ty: Some(Ty::Float), name: Some("X"), scratch: true, in_mapfile: true, special: None },
    Var { reg: REG_Z, ty: Some(Ty::Float), name: Some("Y"), scratch: true, in_mapfile: true, special: None },
    Var { reg: REG_COUNT, ty: Some(Ty::Int), name: Some("COUNT"), scratch: false, in_mapfile: true, special: None },
];

const SPECIAL_VARS: &'static [Var] = &[
    Var {
        reg: REG_TY_VOLATILE, ty: None, name: Some("TY_VOLATILE"), scratch: false, in_mapfile: true,
        special: Some(truth::vm::SpecialVarKind::TypeVolatile { int: 10, float: 20.0 }),
    },
    Var {
        reg: REG_COUNTER, ty: Some(Ty::Int), name: Some("COUNTER"), scratch: false, in_mapfile: true,
        special: Some(truth::vm::SpecialVarKind::Counter { next: 0 }),
    },
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
fn run_randomized_test(vars: &[Var], text: &str) -> Result<TestResult, String> {
    truth::setup_for_test_harness();

    let mut scope = truth::Builder::new().capture_diagnostics(true).build();
    let mut truth = scope.truth();
    _run_randomized_test(&mut truth, vars, text)
        .map_err(|e| {
            e.ignore();
            truth.get_captured_diagnostics().unwrap()
        })
}

#[track_caller]
fn _run_randomized_test(truth: &mut Truth, plain_vars: &[Var], text: &str) -> Result<TestResult, truth::ErrorReported> {
    // all tests have the special vars since they're relatively harmless when not used
    let ref vars = plain_vars.iter().chain(SPECIAL_VARS).cloned().collect::<Vec<_>>();

    load_mapfile(truth, vars);

    let hooks = make_language(vars);
    let base_vm = make_randomized_vm(vars);

    let parsed_block = {
        let mut block = truth.parse::<ast::Block>("<input>", text.as_ref())?.value;

        let ctx = truth.ctx();
        truth::passes::resolution::assign_languages(&mut block, truth::LanguageKey::Anm, ctx)?;
        truth::passes::resolution::resolve_names(&block, ctx)?;
        truth::passes::type_check::run(&block, ctx)?;
        truth::passes::resolution::aliases_to_raw(&mut block, ctx)?;
        truth::passes::resolution::compute_diff_label_masks(&mut block, ctx)?;
        truth::passes::desugar_blocks::run(&mut block, ctx)?;
        block
    };
    assert_eq!(truth.get_captured_diagnostics().unwrap(), "");

    // compile the expressions... (this is the step we are testing)
    let emitter = truth.emitter();
    let ctx = truth.ctx();
    let old_stmts = parsed_block.0;
    let mut errors = truth::error::ErrorFlag::new();
    let mut lowerer = llir::Lowerer::new(&hooks);
    let (def_id, do_debug_info) = (None, false);
    let (instrs, _) = lowerer.lower_sub(&old_stmts, def_id, ctx, do_debug_info).unwrap_or_else(|e| {
        errors.set(e);
        (vec![], None)  // dummy instructions so we can call lowerer.finish before returning
    });
    lowerer.finish(ctx).unwrap_or_else(|e| errors.set(e));

    errors.into_result(())?;

    // decompile back to primitive operations (this gives an "actual" output)
    let new_block = {
        let options = Default::default();
        let const_proof = truth::passes::evaluate_const_vars::run(ctx)?;
        let mut raiser = llir::Raiser::new(&hooks, ctx.emitter, ctx, &options, const_proof)?;
        let mut stmts = raiser.raise_instrs_to_sub_ast(&emitter, &instrs, &ctx)?;
        truth::passes::resolution::aliases_to_raw(&mut stmts[..], ctx)?;
        ast::Block(stmts)
    };

    // check that the compilation preserved semantics by running both
    // the original AST and the decompiled AST in the AstVm
    let mut old_vm = base_vm.clone();
    let mut new_vm = base_vm.clone();
    eprintln!("{}", truth::fmt::stringify(&new_block));
    old_vm.run(&old_stmts, &ctx);
    new_vm.run(&new_block.0, &ctx);

    assert_eq!(old_vm.time, new_vm.time, "time");
    assert_eq!(old_vm.real_time, new_vm.real_time, "real_time");
    assert_eq!(old_vm.instr_log, new_vm.instr_log);
    Ok(TestResult {
        vars: vars.to_vec(),
        old: old_vm,
        new: new_vm,
    })
}

struct TestResult {
    vars: Vec<Var>,
    old: AstVm,
    new: AstVm,
}

impl TestResult {
    /// Expect a register to be equal between the old and new vms.
    #[track_caller]
    fn check_reg(&self, reg: RegId) {
        self.check_reg_with_msg(reg, format_args!("{}\n{}", self.old, self.new));
    }

    #[track_caller]
    fn check_regs(&self, regs: &[RegId]) {
        for &reg in regs {
            self.check_reg_with_msg(reg, format_args!("{}\n{}\nreg {}", self.old, self.new, reg));
        }
    }

    /// Verify that a register was not used as scratch by comparing the values in the old and new vms.
    #[track_caller]
    fn check_reg_not_scratch(&self, reg: RegId) {
        // same check as check_reg really, but we're probably not interested in such verbose information
        self.check_reg_with_msg(reg, format_args!("reg {}", reg));
    }

    /// Expect a register to be equal between the old and new vms.
    #[track_caller]
    fn check_reg_with_msg(&self, reg: RegId, msg: impl core::fmt::Display) {
        assert_eq!(self.old.get_reg(reg), self.new.get_reg(reg), "{}", msg);
    }

    /// Verify that no registers of a given type were used as scratch.
    #[track_caller]
    fn check_no_scratch_of_ty(&self, ty: Ty) {
        for var in &self.vars {
            if var.ty == Some(ty) && var.special.is_none() {
                self.check_reg_not_scratch(var.reg);
            }
        }
    }

    /// Verify that no registers were used as scratch.
    #[track_caller]
    fn check_no_scratch(&self) {
        self.check_no_scratch_of_ty(Ty::Int);
        self.check_no_scratch_of_ty(Ty::Float);
    }
}

/// Checks that attempting to compile this produces a "no more registers of this type" error.
#[track_caller]
fn expect_not_enough_vars(vars: &[Var], text: &str) {
    truth::setup_for_test_harness();

    let mut scope = truth::Builder::new().capture_diagnostics(true).build();
    let mut truth = scope.truth();
    load_mapfile(&mut truth, vars);

    let hooks = make_language(vars);

    let parsed_block = {
        let mut block = truth.parse::<ast::Block>("<input>", text.as_ref()).unwrap().value;

        let ctx = truth.ctx();
        truth::passes::resolution::assign_languages(&mut block, truth::LanguageKey::Anm, ctx).unwrap();
        truth::passes::resolution::resolve_names(&block, ctx).unwrap();
        truth::passes::resolution::aliases_to_raw(&mut block, ctx).unwrap();
        truth::passes::desugar_blocks::run(&mut block, ctx).unwrap();
        block
    };

    // IIFE to catch either of these two function calls failing
    (|| {
        let mut lowerer = llir::Lowerer::new(&hooks);
        let mut errors = truth::error::ErrorFlag::new();

        let (def_id, do_debug_info) = (None, false);
        lowerer.lower_sub(&parsed_block.0, def_id, truth.ctx(), do_debug_info).unwrap_or_else(|e| {
            errors.set(e);
            (vec![], None)  // dummy instrs so we can call .finish()
        });
        lowerer.finish(truth.ctx()).unwrap_or_else(|e| errors.set(e));
        errors.into_result(())
    })().unwrap_err().ignore();
    let err_s = truth.get_captured_diagnostics().unwrap();
    assert!(err_s.contains("no more registers of this type"), "{}", err_s);
}

#[test]
fn vars() {
    // Several source files that should produce identical results
    let tests = vec![
        ("simple_test", SIMPLE_FOUR_VAR_SPEC, r#"{
            int x = 4 + 3 * B, y;
            y = x * x;
            A = x;
        }"#),
        // (check with a raw register access)
        ("simple_test_with_raw", SIMPLE_FOUR_VAR_SPEC, r#"{
            int x = 4 + 3 * $REG[1001], y;
            y = x * x;
            A = x;
        }"#),
        // (check with a read of a non-scratch register)
        ("simple_test_with_nonscratch", SIMPLE_FOUR_VAR_SPEC, r#"{
            int x = 4 + 3 * $REG[1001], y;
            y = x * COUNT;
            A = x;
        }"#),
        // (expression compilation should not require a mapfile to work)
        ("simple_test_nomap", NOMAP_FOUR_VAR_SPEC, r#"{
            int x = 4 + 3 * $REG[1001], y;
            y = x * x;
            $REG[1000] = x;
        }"#),
    ];

    for (test_name, vars, source) in tests {
        for _ in 0..10 {
            let vms = run_randomized_test(vars, source).unwrap();

            // These can't be scratch vars because they were used
            vms.check_reg_with_msg(REG_A, test_name);
            vms.check_reg_with_msg(REG_B, test_name);
            // This one is not general purpose so it's ineligible for scratch use
            vms.check_reg_with_msg(REG_COUNT, test_name);
            // Float registers were not needed for scratch purposes
            vms.check_no_scratch_of_ty(Ty::Float);
        }
    }
}

#[test]
fn float_uses_detected() {
    // Regression test to make sure that float-typed reads are counted as uses.
    for _ in 0..10 {
        // This is designed to fail if any register other than Y is assigned for the local.
        // (Y is in the middle of the scratch vars list, so this can't happen just on accident)
        let vms = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, r#"{
            float x = X + Z;
            W = x;
        }"#).unwrap();
        vms.check_regs(&[REG_X, REG_Z, REG_W]);

        // Likewise for float-typed reads of integer registers.
        let vms = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, r#"{
            int x = $(%A + %C);
            D = x;
        }"#).unwrap();
        vms.check_regs(&[REG_A, REG_C, REG_D]);
    }
}

#[test]
fn cast() {
    // A variable should still be recognized as ineligible for scratch use even if only read as the other type.
    for _ in 0..10 {
        let vars = SIMPLE_FOUR_VAR_SPEC;
        let vms = run_randomized_test(vars, r#"{
            int x = 4 + 3 * $X, y;
            y = x * x;
            A = x;
            float a = (3.0 + W) * (5.0 + W);  // this should use Y and Z for scratch, not X.
        }"#).unwrap();

        let x = vms.old.get_reg(REG_X).unwrap().read_as_float().unwrap() as i32 * 3 + 4;
        assert_eq!(vms.old.get_reg(REG_A), Some(ScalarValue::Int(x)), "{}", vms.old);

        vms.check_regs(&[REG_A, REG_X, REG_W]);
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
                foo_SSS(a, b, c);
            } while (lol == 0);
            lol = 1;
            do {
                int d = 4, e = 5;
                int f = 6;
                foo_SSS(d, e, f);
            } while (lol == 0);
        }"#;

        // first, demonstrate that the test does fail when there aren't enough scratch registers
        // (lol, a, b, and c require four regs)
        expect_not_enough_vars(SIMPLE_THREE_VAR_SPEC, source);
        // now, show that four regs is enough, demonstrating that the registers for a, b, and c
        // are freed when they fall out of scope
        run_randomized_test(SIMPLE_FOUR_VAR_SPEC, source).unwrap();
    }
}

// Tests which should require NO scratch variables.  These test to make sure that operations
// implementable as a single instruction are properly recognized as such.
mod no_scratch {
    use super::*;

    #[track_caller]
    fn check_no_scratch(vars: &[Var], source: &str) {
        run_randomized_test(vars, source).unwrap().check_no_scratch();
    }

    #[test]
    fn direct_assign() {
        for _ in 0..5 {
            check_no_scratch(SIMPLE_FOUR_VAR_SPEC, r#"{
                A = A;
                A = B;
                W = W;
                A = $X;
            }"#);
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
                A += (B:C::B);
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
                foo();
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
                foo();
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
                bar_SSff(A, 2, 6.0:7.0:8.0:9.0, %B);
            }"#);
        }
    }

    #[test]
    fn out_reg_reuse() {
        for _ in 0..5 {
            // these entire expressions can be computed by repeatedly modifying A or X
            // (and this can be done without even rearranging execution order in any manner)
            check_no_scratch(SIMPLE_FOUR_VAR_SPEC, r#"{
                A = B + B * -(B * (C + -(A+1:A+2:B+3:B+4) + (C:B:C:B) + C) + B);
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
    let vms_if = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, &format!(r#"{{
        {}
        if ({}) goto hi;
        foo();
      hi:
    }}"#, init, cond)).unwrap();
    let vms_unless = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, &format!(r#"{{
        {}
        unless ({}) goto hi;
        foo();
      hi:
    }}"#, init, cond)).unwrap();

    // For 'if', the call should be skipped if the condition is true.
    assert_eq!(vms_if.new.instr_log.len(), 1 - (expected as usize));
    assert_eq!(vms_unless.new.instr_log.len(), expected as usize);
    CheckBoolVms { new_if_vm: vms_if.new, new_unless_vm: vms_unless.new }
}

#[test]
fn cond_jump_non_binop() {
    check_bool("", "0", false);
    check_bool("", "1", true);
    check_bool("", "-0", false);
    check_bool("A=2;", "-A", true);
    check_bool("", "int(0.0)", false);
    check_bool("", "int(1.0)", true);
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
    check_bool("", "!(int(1.0))", false);
    check_bool("A=2;", "!(A * A)", false);
}

#[test]
fn cond_jump_float() {
    check_bool("X=1.0;", "X < 2.0", true);
    check_bool("X=1.0;", "X > 2.0", false);
    check_bool("X=1.0;", "X <= 1.0", true);
    check_bool("X=1.0;", "X >= 1.0", true);
    check_bool("", "1.0 <= 2.0", true);
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
        let vms = run_randomized_test(vars, r#"{
            X = float(A + 4);
        }"#).unwrap();

        vms.check_no_scratch_of_ty(Ty::Float);
    }
}

#[test]
fn careful_cast_temporaries() {
    // A cast may create a temporary of its argument's type, but it should never create a temporary
    // of its output type. (because whatever's using it can simply read the temporary as that type)
    for _ in 0..10 {
        let vars = SIMPLE_FOUR_VAR_SPEC;
        // None of these should create an integer temporary
        let vms = run_randomized_test(vars, r#"{
            bar_S(int(%X + 4.0));
            A = A + int(%X + 4.0);
        }"#).unwrap();

        vms.check_no_scratch_of_ty(Ty::Int);
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
            let vms = run_randomized_test(vars, &format!(r#"{{
                A = {} + {};
                B = B;  // guarantee that B is considered used so we can assert on it
            }}"#, expr_1, expr_2)).unwrap();

            vms.check_reg(REG_A);
            vms.check_reg(REG_B);

            // Float vars were not needed for scratch purposes
            vms.check_no_scratch_of_ty(Ty::Float);
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
            let vms = run_randomized_test(vars, &format!(r#"{{
                X = {}({});
                Y = Y;  // guarantee that Y is considered used so we can assert on it
            }}"#, oper, expr_1)).unwrap();

            vms.check_reg(REG_X);
            vms.check_reg(REG_Y);

            vms.check_no_scratch_of_ty(Ty::Int);
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
        }}"#, ANTI_SCRATCH_OPCODE)).unwrap();
    }

    #[test]
    #[should_panic(expected = "scratch registers are disabled")]
    fn bad_before() {
        run_randomized_test(SIMPLE_FOUR_VAR_SPEC, &format!(r#"{{
            A = A + B * -A;  // requires scratch!
            ins_{}();
        }}"#, ANTI_SCRATCH_OPCODE)).unwrap();
    }

    #[test]
    #[should_panic(expected = "scratch registers are disabled")]
    fn bad_after() {
        // (this is to make sure the check doesn't depend on instruction order...)
        run_randomized_test(SIMPLE_FOUR_VAR_SPEC, &format!(r#"{{
            ins_{}();
            A = A + B * -A;  // requires scratch!
        }}"#, ANTI_SCRATCH_OPCODE)).unwrap();
    }
}

#[test]
fn times() {
    for _ in 0..10 {
        run_randomized_test(SIMPLE_FOUR_VAR_SPEC, r#"{
            A = 5;  // ensure positive
            times(2) {
                times(3*A + 2) {
                    foo_S(1 + 5);
                }
            }
        }"#).unwrap();
    }
}

#[test]
fn loop_break() {
    let vms = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, r#"{
        A = 5;
        B = 0;
        times(A = 6) {
            loop {
                B += 1;
                C = B % 7;
                if (C == 0) break;
            }

            while (A != 1000) { break; }
            times(1000) { break; }

            if (A == 3) break;
        }
    }"#).unwrap();
    assert_eq!(vms.new.get_reg(REG_A), Some(ScalarValue::Int(3)));
    assert_eq!(vms.new.get_reg(REG_B), Some(ScalarValue::Int(28)));
}

#[test]
fn loop_diff_switch() {
    for _ in 0..10 {
        let vms = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, r#"{
            A = 5;
            B = 0;
            times(A+2:A+3:B+2:B+1) {
                C += 1;
                nop();
                +5:  // if the loop body got replicated we'll have some time label memes...
            }
        }"#).unwrap();
        vms.check_regs(&[REG_A, REG_B, REG_C]);
    }
}

#[test]
fn cast_diff_switch() {
    for _ in 0..10 {
        let vms = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, r#"{
            A = int(X::Y:);
            A = int(X::Y:) + 2;
            B = int(X*Y::Y*Y:);
        }"#).unwrap();
        vms.check_regs(&[REG_A, REG_B]);
        vms.check_regs(&[REG_X, REG_Y]);
    }
}

#[test]
fn assign_op_diff_switch() {
    for _ in 0..10 {
        let vms = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, r#"{
            A += A+B:C::;
        }"#).unwrap();
        vms.check_regs(&[REG_A, REG_B, REG_C]);
    }
}

#[test]
fn mismatched_diff_switch_cases() {
    for _ in 0..10 {
        let vms = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, r#"{
            A = (B::C:) * (A:C::);
            X = (Y+Z::Z:) * (Y+X:Z::);
        }"#).unwrap();
        vms.check_regs(&[REG_A, REG_B, REG_C]);
        vms.check_regs(&[REG_X, REG_Y, REG_Z]);
    }
}

#[test]
fn nested_diff_switch_cases() {
    for _ in 0..10 {
        let vms = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, r#"{
            A = (A+((A:2:3:4):2:3:4):(A+1:2:3:4):C:);
        }"#).unwrap();
        vms.check_regs(&[REG_A, REG_Z]);
    }
}

#[test]
fn difficulty_label_and_diff_switch() {
    for _ in 0..10 {
        let vms = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, r#"{
            {"12"}: A = 300::400:;
            {"12"}: B = 300:400::;
        }"#).unwrap();
        vms.check_regs(&[REG_A, REG_B]);
    }
}

#[test]
fn read_type_volatile() {
    // these should generate a temporary float to ensure that TY_VOLATILE is
    // read as a float and not as an integer.  This is to ensure correct behavior
    // of e.g. `float($RAND)` in PCB ECL. (which is different from `%RAND`!)
    for _ in 0..10 {
        let vms = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, r#"{
            A = int(%TY_VOLATILE);
            B = $(%TY_VOLATILE);
        }"#).unwrap();

        // if one of these evaluates to 10, it read as an int instead  D:
        assert_eq!(vms.new.get_reg(REG_A), Some(ScalarValue::Int(20)));
        assert_eq!(vms.new.get_reg(REG_B), Some(ScalarValue::Int(20)));
        vms.check_no_scratch_of_ty(Ty::Int);
    }
}

#[test]
fn binop_reuse_where_arg_type_isnt_out_type() {
    for _ in 0..10 {
        // float comparisons are an example of a binop whose result type != the input type
        let vms = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, r#"{
            A = %X + 0.25 < 0.5;
        }"#).unwrap();

        vms.check_no_scratch_of_ty(Ty::Int);
    }
}

#[test]
fn assign_op_cast() {
    for _ in 0..10 {
        let vms = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, r#"{
            A += int(%X + 0.25);
        }"#).unwrap();

        vms.check_no_scratch_of_ty(Ty::Int);
    }
}

#[test]
fn trivial_cast() {
    for _ in 0..10 {
        let vms = run_randomized_test(SIMPLE_FOUR_VAR_SPEC, r#"{
            B = $(A + 2);
            C = int(A + 2);
        }"#).unwrap();

        vms.check_no_scratch_of_ty(Ty::Float);
    }
}
