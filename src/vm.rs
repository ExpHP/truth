use std::collections::HashMap;
use std::fmt;
use crate::ast;
use crate::pos::Sp;
use crate::context::CompilerContext;
use crate::resolve::{DefId, RegId, Resolutions, NodeId, IdMap};
use crate::passes::semantics::time_and_difficulty::{self, TimeAndDifficulty};
use crate::value::ScalarValue;

/// A VM that runs on the AST, which can be used to help verify the validity of AST transforms
/// in unit tests.
///
/// Because it runs on a nested datastructure, it has no concept of a persistent instruction
/// pointer and cannot be paused or resumed.  It will always run the code until it falls off
/// past the last statement or hits a return.
///
/// **Important:** The VM has no interaction with the type system.  This means that it cannot resolve
/// aliases of registers; you should [convert them to raw registers](`crate::passes::resolution::aliases_to_regs`)
/// as a preprocessing step before using the VM.
#[derive(Debug, Clone)]
pub struct AstVm {
    /// Current script time in the VM.
    ///
    /// This increases as the VM waits for instructions, and gets set to specific values
    /// during jumps.
    pub time: i32,
    /// Total amount of time the VM has been running.
    ///
    /// Unlike `time`, this monotonically increases.
    pub real_time: i32,
    /// Log of all opaque instructions that have executed.
    /// (anything using special syntax like operators, assignments and control flow are NOT logged)
    pub instr_log: Vec<LoggedCall>,
    iterations: u32,
    max_iterations: Option<u32>,
    var_values: HashMap<VarId, ScalarValue>,
}

/// Hashable type representing a register or a named variable.
#[derive(Copy, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VarId {
    Reg(RegId),
    Other(DefId),
}

#[derive(Debug, Clone, PartialEq)]
pub struct LoggedCall {
    pub real_time: i32,
    pub opcode: u16,
    pub args: Vec<ScalarValue>,
}

impl fmt::Display for AstVm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "-----------------------------------------")?;
        writeln!(f, " Time {:>7}    RealTime {:>7}", self.time, self.real_time)?;
        writeln!(f, "-----------------------------------------")?;
        if !self.instr_log.is_empty() {
            writeln!(f, "   CALL LOG")?;
            for call in &self.instr_log {
                let arg_strs = call.args.iter().map(|x| x.to_string()).collect::<Vec<_>>();
                writeln!(f, "  {:>5}: ins_{}({})", call.real_time, call.opcode, arg_strs.join(", "))?;
            }
        }

        let mut others = vec![];
        let mut regs = vec![];
        for (&var_id, value) in &self.var_values {
            match var_id {
                VarId::Reg(reg) => regs.push((reg, value.clone())),
                VarId::Other(def_id) => others.push((def_id, value.clone())),
            }
        }
        others.sort_by_key(|&(id, _)| id);
        regs.sort_by_key(|&(id, _)| id);

        if !regs.is_empty() {
            writeln!(f, "  REGISTERS")?;
            for (reg, value) in regs {
                writeln!(f, "  {:>5}  {}", reg, value)?;
            }
        }
        if !others.is_empty() {
            writeln!(f, "  OTHER VARS")?;
            for (local_id, value) in others {
                writeln!(f, "  {:>5}  {}", local_id, value)?;
            }
        }
        Ok(())
    }
}

#[must_use]
enum RunResult {
    /// Nothing is out of the ordinary.
    Nominal,
    /// A `return` was encountered.
    Return(Option<ScalarValue>),
    /// A nested run call is jumping to an outer label.
    ///
    /// (for technical reasons, you can't jump to an inner label)
    IsJumping(ast::StmtGoto),
}

impl AstVm {
    pub fn new() -> Self {
        AstVm {
            time: 0,
            real_time: 0,
            instr_log: vec![],
            var_values: Default::default(),
            iterations: 0,
            max_iterations: None,
        }
    }

    pub fn with_max_iterations(mut self, n: u32) -> Self {
        self.max_iterations = Some(n);
        self
    }

    /// Run the statements until it hits the end or a `return`.  Returns the `return`ed value.
    ///
    /// **Important reminder:** Please be certain that name resolution has been performed, and that
    /// additionally all register aliases have been [converted to raw registers](`crate::passes::resolution::aliases_to_regs`).
    pub fn run(&mut self, stmts: &[Sp<ast::Stmt>], ctx: &CompilerContext<'_>) -> Option<ScalarValue> {
        let stmt_data = time_and_difficulty::run(stmts, &ctx.emitter).expect("unexpected analysis failure");
        match self._run(stmts, &ctx.resolutions, &stmt_data) {
            RunResult::Nominal => None,
            RunResult::Return(value) => value,
            RunResult::IsJumping(goto) => panic!(
                "AST VM tried to jump to {} but this label did not exist within the same or outer scopes! \
                (note: for technical reasons, labels in inner scopes cannot be jumped to by this VM)",
                goto.destination,
            ),
        }
    }

    fn _run(&mut self, stmts: &[Sp<ast::Stmt>], resolutions: &Resolutions, stmt_data: &IdMap<NodeId, TimeAndDifficulty>) -> RunResult {
        let mut stmt_index = 0;

        'stmt: while stmt_index < stmts.len() {
            if let Some(max_iterations) = self.max_iterations {
                if self.iterations >= max_iterations {
                    panic!("iteration limit exceeded!");
                }
            }
            self.iterations += 1;

            macro_rules! handle_goto {
                ($goto:expr) => { match $goto {
                    goto => match self.try_goto(stmts, goto, stmt_data) {
                        Some(index) => {
                            stmt_index = index;
                            continue 'stmt;
                        },
                        None => return RunResult::IsJumping(goto.clone()),
                    },
                }};
            }

            macro_rules! handle_block {
                ($block:expr) => {
                    match self._run($block, resolutions, stmt_data) {
                        RunResult::Nominal => {},
                        RunResult::Return(value) => return RunResult::Return(value),
                        RunResult::IsJumping(goto) => handle_goto!(&goto),
                    }
                };
            }

            let stmt_node_id = stmts[stmt_index].node_id.unwrap();
            let stmt_time = stmt_data[&stmt_node_id].time;
            if self.time < stmt_time {
                let time_diff = stmt_time - self.time;
                self.time += time_diff;
                self.real_time += time_diff;
            }

            let start_time = |block: &ast::Block| stmt_data[&block.start_node_id()].time;
            let end_time = |block: &ast::Block| stmt_data[&block.end_node_id()].time;

            // N.B. this can't easily be factored out into a method because it would require
            //      some way of storing or communicating a "instruction pointer", which
            //      doesn't exist due to the nested nature of the AST.
            match &stmts[stmt_index].body {
                ast::StmtBody::Item(_) => {},

                ast::StmtBody::Goto(goto) => handle_goto!(goto),

                ast::StmtBody::CondGoto { keyword, cond, goto } => {
                    if self.eval_cond(cond, resolutions) == (keyword == &token![if]) {
                        handle_goto!(goto);
                    }
                },

                ast::StmtBody::Return { value, .. } => {
                    return RunResult::Return(value.as_ref().map(|x| self.eval(x, resolutions)));
                },

                ast::StmtBody::CondChain(chain) => {
                    let ast::StmtCondChain { cond_blocks, else_block } = chain;

                    let mut branch_taken = false;
                    for ast::CondBlock { keyword, cond, block } in cond_blocks {
                        if self.eval_cond(cond, resolutions) == (keyword == &token![if]) {
                            branch_taken = true;
                            self.time = start_time(&block);
                            handle_block!(&block.0);
                            break;
                        }
                    }

                    if !branch_taken {
                        if let Some(else_block) = else_block {
                            self.time = start_time(else_block);
                            handle_block!(&else_block.0);
                        }
                    }
                    self.time = end_time(chain.last_block());
                },

                ast::StmtBody::Loop { block, .. } => {
                    loop {
                        handle_block!(&block.0);
                        self.time = start_time(block);
                    }
                },

                ast::StmtBody::While { do_keyword, cond, block, .. } => {
                    if do_keyword.is_some() || self.eval_cond(cond, resolutions) {
                        loop {
                            handle_block!(&block.0);
                            if self.eval_cond(cond, resolutions) {
                                self.time = start_time(block);
                                continue;
                            }
                            break;
                        }
                    } else {
                        // nasty: in the zero-iterations case only, we jump over the loop
                        //    and therefore need to fix the time!
                        self.time = end_time(block);
                    }
                },

                ast::StmtBody::Times { clobber: None, count, block, .. } => {
                    self.time = end_time(block);
                    match self.eval_int(count, resolutions) {
                        0 => {},
                        count => {
                            for _ in 0..count {
                                self.time = start_time(block);
                                handle_block!(&block.0);
                            }
                        },
                    }
                },

                // when a clobber is specified we have to treat it pretty differently
                // as the loop counter now has an observable presence
                ast::StmtBody::Times { clobber: Some(clobber), count, block, .. } => {
                    let count = self.eval_int(count, resolutions);
                    self.set_var_by_ast(clobber, ScalarValue::Int(count), resolutions);

                    self.time = end_time(block);
                    if count != 0 {
                        loop {
                            self.time = start_time(block);
                            handle_block!(&block.0);

                            match self.read_var_by_ast(clobber, resolutions) {
                                ScalarValue::Float(x) => panic!("float count {}", x),
                                ScalarValue::String(x) => panic!("string count {}", x),
                                ScalarValue::Int(x) => {
                                    let predecremented = x - 1;
                                    self.set_var_by_ast(clobber, ScalarValue::Int(predecremented), resolutions);
                                    if predecremented == 0 { break; }
                                },
                            }
                        } // loop
                    }
                },

                ast::StmtBody::Expr(expr) => {
                    match &expr.value {
                        ast::Expr::Call { name, pseudos, args } => {
                            if pseudos.len() > 0 {
                                unimplemented!("VM pseudo-args");  // TODO: we'd have to let LoggedCall potentially hold a blob
                            }

                            let arg_values = args.iter().map(|arg| self.eval(arg, resolutions)).collect::<Vec<_>>();
                            match name.value {
                                ast::CallableName::Ins { opcode, .. } => self.log_instruction(opcode, &arg_values),
                                ast::CallableName::Normal { .. } => unimplemented!("non-instr function in VM"),
                            }
                        },
                        _ => unimplemented!("VM statement expression: {:?}", expr)
                    }
                },

                ast::StmtBody::Assignment { var, op, value } => {
                    match op.value {
                        ast::AssignOpKind::Assign => {
                            let value = self.eval(value, resolutions);
                            self.set_var_by_ast(var, value, resolutions);
                        },
                        _ => {
                            let binop = op.corresponding_binop().expect("only Assign has no binop");
                            let value = sp!(op.span => binop).const_eval(
                                self.read_var_by_ast(var, resolutions),
                                self.eval(value, resolutions),
                            );
                            self.set_var_by_ast(var, value, resolutions);
                        },
                    }
                },

                ast::StmtBody::Declaration { vars, .. } => {
                    for pair in vars.iter() {
                        let (var, expr) = &pair.value;
                        if let Some(expr) = expr {
                            let value = self.eval(expr, resolutions);
                            self.set_var_by_ast(var, value, resolutions);
                        }
                    }
                },

                ast::StmtBody::CallSub { .. } => unimplemented!("CallSub for AST VM"),

                ast::StmtBody::Label(_) => {},

                ast::StmtBody::InterruptLabel(_) => {},

                ast::StmtBody::RawDifficultyLabel(_) => {},

                ast::StmtBody::AbsTimeLabel { .. } => { /* FIXME: switch VM to use these labels */ },
                ast::StmtBody::RelTimeLabel { .. } => { /* FIXME: switch VM to use these labels */ },

                ast::StmtBody::ScopeEnd(_) => {},

                ast::StmtBody::NoInstruction => {},
            }

            stmt_index += 1;
        }
        RunResult::Nominal
    }

    pub fn eval(&mut self, expr: &ast::Expr, resolutions: &Resolutions) -> ScalarValue {
        match expr {
            ast::Expr::Ternary { cond, left, right, .. } => {
                match self.eval_int(cond, resolutions) {
                    0 => self.eval(right, resolutions),
                    _ => self.eval(left, resolutions),
                }
            },

            ast::Expr::Binop(a, op, b) => op.const_eval(self.eval(a, resolutions), self.eval(b, resolutions)),

            ast::Expr::Call { .. } => unimplemented!("func calls in VM exprs"),

            ast::Expr::Unop(op, x) => op.const_eval(self.eval(x, resolutions)),

            ast::Expr::LitInt { value, .. } => ScalarValue::Int(*value),

            ast::Expr::LitFloat { value, .. } => ScalarValue::Float(*value),

            ast::Expr::LitString(ast::LitString { string, .. }) => ScalarValue::String(string.clone()),

            ast::Expr::Var(var) => self.read_var_by_ast(var, resolutions),
        }
    }

    pub fn log_instruction(&mut self, opcode: u16, args: &[ScalarValue]) {
        self.instr_log.push(LoggedCall {
            opcode,
            args: args.to_vec(),
            real_time: self.real_time,
        })
    }

    #[track_caller]
    pub fn eval_cond(&mut self, cond: &ast::Cond, resolutions: &Resolutions) -> bool {
        match cond {
            ast::Cond::PreDecrement(var) => match self.read_var_by_ast(var, resolutions) {
                ScalarValue::Float(x) => panic!("type error: {:?}", x),
                ScalarValue::String(x) => panic!("type error: {:?}", x),
                ScalarValue::Int(value) => {
                    self.set_var_by_ast(var, ScalarValue::Int(value - 1), resolutions);
                    value - 1 != 0
                },
            },
            ast::Cond::Expr(expr) => match self.eval(expr, resolutions) {
                ScalarValue::Float(x) => panic!("type error: {:?}", x),
                ScalarValue::String(x) => panic!("type error: {:?}", x),
                ScalarValue::Int(value) => value != 0,
            },
        }
    }

    #[track_caller]
    pub fn eval_int(&mut self, expr: &ast::Expr, resolutions: &Resolutions) -> i32 {
        match self.eval(expr, resolutions) {
            ScalarValue::Int(x) => x,
            ScalarValue::Float(x) => panic!("type error: {:?}", x),
            ScalarValue::String(x) => panic!("type error: {:?}", x),
        }
    }

    fn var_id_from_name(&self, var: &ast::VarName, resolutions: &Resolutions) -> VarId {
        match *var {
            ast::VarName::Normal { ref ident, language_if_reg: _ } => VarId::Other(resolutions.expect_def(ident)),
            ast::VarName::Reg { reg, language: _ } => VarId::Reg(reg),
        }
    }

    pub fn set_var(&mut self, var_id: VarId, value: ScalarValue) { self.var_values.insert(var_id, value); }
    pub fn get_var(&self, var_id: VarId) -> Option<ScalarValue> { self.var_values.get(&var_id).cloned() }

    /// Convenience wrapper of [`Self::set_var`] for test code.
    pub fn set_reg(&mut self, reg: RegId, value: ScalarValue) { self.set_var(VarId::Reg(reg), value); }
    /// Convenience wrapper of [`Self::get_var`] for test code.
    pub fn get_reg(&self, reg: RegId) -> Option<ScalarValue> { self.get_var(VarId::Reg(reg)) }

    fn set_var_by_ast(&mut self, var: &ast::Var, value: ScalarValue, resolutions: &Resolutions) {
        let key = self.var_id_from_name(&var.name, resolutions);
        self.var_values.insert(key, value);
    }

    fn read_var_by_ast(&self, var: &ast::Var, resolutions: &Resolutions) -> ScalarValue {
        let var_id = self.var_id_from_name(&var.name, resolutions);
        self.get_var(var_id).unwrap_or_else(|| panic!("read of uninitialized var: {:?}", var.name))
            .apply_sigil(var.ty_sigil).unwrap_or_else(|| panic!("cannot cast {:?} to {:?}", var.name, var.ty_sigil))
    }

    pub fn try_goto(&mut self, stmts: &[Sp<ast::Stmt>], goto: &ast::StmtGoto, stmt_data: &IdMap<NodeId, TimeAndDifficulty>) -> Option<usize> {
        for (index, stmt) in stmts.iter().enumerate() {
            match &stmt.body {
                ast::StmtBody::Label(label) => {
                    if label == &goto.destination {
                        self.time = goto.time.map(|x| x.value).unwrap_or(stmt_data[&stmt.node_id.unwrap()].time);
                        return Some(index);
                    }
                },
                _ => {},
            }
        }
        return None;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::{ScalarValue::{Int, Float}, ScalarType as Ty};
    use crate::game::InstrLanguage::Dummy;

    struct TestSpec<S> {
        globals: Vec<(&'static str, RegId, Ty)>,
        source: S,
    }

    fn new_test_vm() -> AstVm {
        AstVm::new().with_max_iterations(1000)
    }

    impl<S: AsRef<[u8]>> TestSpec<S> {
        fn check(&self, test: impl Fn(&ast::Block, &CompilerContext<'_>)) {
            let mut scope = crate::Builder::new().build();
            let mut truth = scope.truth();
            let mut ast = truth.parse::<ast::Block>("<input>", self.source.as_ref()).unwrap();

            let ctx = truth.ctx();
            for &(alias, reg, ty) in &self.globals {
                ctx.define_global_reg_alias(Dummy, reg, alias.parse().unwrap());
                ctx.set_reg_ty(Dummy, reg, ty.into());
            }
            crate::passes::resolution::assign_languages(&mut ast.value, Dummy, ctx).unwrap();
            crate::passes::resolution::resolve_names(&ast.value, ctx).unwrap();
            crate::passes::resolution::aliases_to_raw(&mut ast.value, ctx).unwrap();
            test(&ast.value, &ctx)
        }
    }

    #[test]
    fn basic_variables() {
        TestSpec {
            globals: vec![("Y", RegId(-999), Ty::Int)],
            source: r#"{
                int x = 3;
                x = 2 + 3 * x + $Y;
                return x + 1;
            }"#,
        }.check(|ast, ctx| {
            let mut vm = new_test_vm();
            vm.set_reg(RegId(-999), Int(7));
    
            assert_eq!(vm.run(&ast.0, &ctx), Some(Int(19)));
        });
    }

    #[test]
    fn basic_instrs_and_time() {
        TestSpec {
            globals: vec![("X", RegId(100), Ty::Int), ("Y", RegId(101), Ty::Float)],
            source: r#"{
                ins_345(0, 6);
            +10:
                ins_12(X, Y + 1.0);
            }"#,
        }.check(|ast, ctx| {
            let mut vm = new_test_vm();
            vm.set_reg(RegId(100), Int(3));
            vm.set_reg(RegId(101), Float(7.0));
            vm.run(&ast.0, &ctx);

            assert_eq!(vm.instr_log, vec![
                LoggedCall { real_time: 0, opcode: 345, args: vec![Int(0), Int(6)] },
                LoggedCall { real_time: 10, opcode: 12, args: vec![Int(3), Float(8.0)] },
            ]);
        });
    }

    #[test]
    fn while_do_while() {
        let while_test = TestSpec {
            globals: vec![("X", RegId(100), Ty::Int), ("Y", RegId(101), Ty::Int)],
            source: r#"{
                X = 0;
                while (X < Y) {
                  +2:
                    X += 1;
                    ins_1();
                  +3:
                }
              +4:
                ins_44();
            }"#,
        };

        let do_while_test = TestSpec {
            globals: vec![("X", RegId(100), Ty::Int), ("Y", RegId(101), Ty::Int)],
            source: r#"{
                X = 0;
                do {
                  +2:
                    X += 1;
                    ins_1();
                  +3:
                } while (X < Y);
              +4:
                ins_44();
            }"#,
        };
        do_while_test.check(|ast, _| { dbg!(&ast); });

        for test in vec![&while_test, &do_while_test] {
            test.check(|ast, ctx| {
                let mut vm = new_test_vm();
                vm.set_reg(RegId(101), Int(3));
                vm.run(&ast.0, &ctx);

                assert_eq!(vm.instr_log, vec![
                    LoggedCall { real_time: 2, opcode: 1, args: vec![] },
                    LoggedCall { real_time: 7, opcode: 1, args: vec![] },
                    LoggedCall { real_time: 12, opcode: 1, args: vec![] },
                    LoggedCall { real_time: 19, opcode: 44, args: vec![] },
                ]);
            });
        }

        // now let Y = 0 so we can see the difference between 'do' and 'do while'
        for (test, expected_iters) in vec![
            (&while_test, 0),
            (&do_while_test, 1),
        ] {
            test.check(|ast, ctx| {
                let mut vm = new_test_vm();
                vm.set_reg(RegId(101), Int(0));
                vm.run(&ast.0, &ctx);

                assert_eq!(vm.instr_log.len(), expected_iters + 1);
                assert_eq!(vm.real_time, (5 * expected_iters + 4) as i32);
            });
        }
    }

    #[test]
    fn goto() {
        TestSpec {
            globals: vec![("X", RegId(100), Ty::Int)],
            source: r#"{
                X = 0;
                loop {
                    ins_10(); goto B;
                20: C:
                    ins_30(); goto exited;
                30: B:
                    ins_20();
                    if (X == 1) goto C @ 5;
                    X = 1;
                    goto B;
                }
            exited:
                ins_40();
            }"#,
        }.check(|ast, ctx| {
            let mut vm = new_test_vm();
            vm.run(&ast.0, &ctx);
            assert_eq!(vm.instr_log, vec![
                LoggedCall { real_time: 0, opcode: 10, args: vec![] },
                LoggedCall { real_time: 0, opcode: 20, args: vec![] },
                LoggedCall { real_time: 0, opcode: 20, args: vec![] },
                LoggedCall { real_time: 15, opcode: 30, args: vec![] },
                LoggedCall { real_time: 15, opcode: 40, args: vec![] },
            ]);
        });
    }

    #[test]
    fn times() {
        for possible_clobber in vec!["", "C = "] {
            TestSpec {
                globals: vec![("X", RegId(100), Ty::Int), ("C", RegId(101), Ty::Int)],
                source: format!(r#"{{
                    times({}X) {{
                        ins_11();
                    +10:
                    }}
                    +5:
                }}"#, possible_clobber),
            }.check(|ast, ctx| {
                for count in (0..3).rev() {
                    let mut vm = new_test_vm();
                    vm.set_reg(RegId(100), Int(count));
                    vm.run(&ast.0, &ctx);

                    assert_eq!(vm.instr_log.len(), count as usize);
                    assert_eq!(vm.real_time, count * 10 + 5);
                    assert_eq!(vm.time, 15);
                }
            });
        }
    }

    #[test]
    fn predecrement_jmp() {
        TestSpec {
            globals: vec![("C", RegId(101), Ty::Int)],
            source: r#"{
                C = 2;
            label:
                ins_11(C);
                +10:
                if (--C) goto label;
            }"#,
        }.check(|ast, ctx| {
            let mut vm = new_test_vm();
            vm.run(&ast.0, &ctx);

            assert_eq!(vm.get_reg(RegId(101)).unwrap(), Int(0));
            assert_eq!(vm.instr_log, vec![
                LoggedCall { real_time: 0, opcode: 11, args: vec![Int(2)] },
                LoggedCall { real_time: 10, opcode: 11, args: vec![Int(1)] },
            ]);
            assert_eq!(vm.real_time, 20);
        });
    }

    #[test]
    fn times_clobber_nice() {
        TestSpec {
            globals: vec![("X", RegId(100), Ty::Int), ("C", RegId(101), Ty::Int)],
            source: r#"{
                X = 2;
                times(C = X) {
                    ins_11(C);
                +10:
                }
            }"#,
        }.check(|ast, ctx| {
            let mut vm = new_test_vm();
            vm.run(&ast.0, &ctx);

            assert_eq!(vm.get_reg(RegId(101)).unwrap(), Int(0));
            assert_eq!(vm.instr_log, vec![
                LoggedCall { real_time: 0, opcode: 11, args: vec![Int(2)] },
                LoggedCall { real_time: 10, opcode: 11, args: vec![Int(1)] },
            ]);
            assert_eq!(vm.real_time, 20);
        });
    }

    #[test]
    fn times_clobber_naughty() {
        TestSpec {
            globals: vec![("X", RegId(100), Ty::Int), ("C", RegId(101), Ty::Int)],
            source: r#"{
                X = 4;
                times(C = X) {
                    ins_11(C);
                    C -= 1;  // further manipulate the counter! (le gasp)
                +10:
                }
            }"#,
        }.check(|ast, ctx| {
            let mut vm = new_test_vm();
            vm.run(&ast.0, &ctx);

            assert_eq!(vm.get_reg(RegId(101)).unwrap(), Int(0));
            assert_eq!(vm.instr_log, vec![
                LoggedCall { real_time: 0, opcode: 11, args: vec![Int(4)] },
                LoggedCall { real_time: 10, opcode: 11, args: vec![Int(2)] },
            ]);
            assert_eq!(vm.real_time, 20);
        });
    }

    #[test]
    fn cond_chain() {
        macro_rules! gen_spec {
            ($last_clause:literal) => {
                TestSpec {
                    globals: vec![("X", RegId(100), Ty::Int)],
                    source: concat!(r#"{
                        if (X == 1) {
                            ins_11(1);
                        10:
                        } else if (X == 2) {
                            ins_11(2);
                        20:
                        } "#, $last_clause, r#" {
                            ins_11(3);
                        30:
                        }
                        ins_200();
                    }"#),
                }
            };
        }
        let with_test = gen_spec!("else");
        let without_test = gen_spec!("else if (X == 3)");

        // both of these should have the same results for X in [1, 2, 3]
        for test in vec![&with_test, &without_test] {
            test.check(|ast, ctx| {
                for x in vec![1, 2, 3] {
                    let mut vm = new_test_vm();
                    vm.set_reg(RegId(100), Int(x));
                    vm.run(&ast.0, &ctx);

                    assert_eq!(vm.instr_log, vec![
                        LoggedCall { real_time: 0, opcode: 11, args: vec![Int(x)] },
                        LoggedCall { real_time: 10, opcode: 200, args: vec![] },
                    ]);
                    assert_eq!(vm.time, 30);
                    assert_eq!(vm.real_time, 10);
                }
            });
        }
    }

    #[test]
    fn type_cast() {
        TestSpec {
            globals: vec![("X", RegId(30), Ty::Int), ("Y", RegId(31), Ty::Int)],
            source: r#"{
                Y = 6.78;
                X = $Y * 2;
            }"#,
        }.check(|ast, ctx| {
            let mut vm = new_test_vm();
            vm.run(&ast.0, &ctx);
            assert_eq!(vm.get_reg(RegId(31)).unwrap(), Float(6.78));
            assert_eq!(vm.get_reg(RegId(30)).unwrap(), Int(12));
        });
    }

    #[test]
    #[should_panic(expected = "iteration limit")]
    fn iteration_limit() {
        TestSpec {
            globals: vec![],
            source: r#"{
                loop {}
            }"#,
        }.check(|ast, ctx| {
            let mut vm = new_test_vm().with_max_iterations(1000);
            vm.run(&ast.0, &ctx);
        });
    }

    #[test]
    fn math_funcs() {
        TestSpec {
            globals: vec![
                ("X", RegId(30), Ty::Float),
                ("SIN", RegId(31), Ty::Float), ("COS", RegId(32), Ty::Float), ("SQRT", RegId(33), Ty::Float),
            ],
            source: r#"{
                SIN = sin(X);
                COS = cos(X);
                SQRT = sqrt(X + 3.0);
            }"#,
        }.check(|ast, ctx| {
            let x = 5.2405;

            let mut vm = new_test_vm();
            vm.set_reg(RegId(30), Float(x));
            vm.run(&ast.0, &ctx);

            assert_eq!(vm.get_reg(RegId(31)).unwrap(), Float(x.sin()));
            assert_eq!(vm.get_reg(RegId(32)).unwrap(), Float(x.cos()));
            assert_eq!(vm.get_reg(RegId(33)).unwrap(), Float((x + 3.0).sqrt()));
        });
    }

    #[test]
    fn cast() {
        TestSpec {
            globals: vec![
                ("I", RegId(30), Ty::Int), ("F", RegId(31), Ty::Float),
                ("F_TO_I", RegId(32), Ty::Int), ("I_TO_F", RegId(33), Ty::Float),
            ],
            source: r#"{
                F_TO_I = _S(F * 7.0) - 2;
                I_TO_F = _f(I + 3) + 0.5;
            }"#,
        }.check(|ast, ctx| {
            let f = 5.2405;
            let i = 12;

            let mut vm = new_test_vm();
            vm.set_reg(RegId(30), Int(i));
            vm.set_reg(RegId(31), Float(f));
            vm.run(&ast.0, &ctx);

            assert_eq!(vm.get_reg(RegId(32)).unwrap(), Int((f * 7.0) as i32 - 2));
            assert_eq!(vm.get_reg(RegId(33)).unwrap(), Float((i + 3) as f32 + 0.5));
        });
    }

    #[test]
    fn string_arg() {
        TestSpec {
            globals: vec![],
            source: r#"{
                ins_11(3, 2, "seashells");
            }"#,
        }.check(|ast, ctx| {
            let mut vm = new_test_vm();
            vm.run(&ast.0, &ctx);

            assert_eq!(vm.instr_log[0].args.last().unwrap(), &ScalarValue::String("seashells".into()));
        });
    }
}
