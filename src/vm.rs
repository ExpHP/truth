use std::collections::HashMap;
use crate::ast;
use crate::pos::Sp;
use crate::ident::Ident;
use crate::var::VarId;
use crate::value::ScalarValue;

macro_rules! opt_match {
    ($x:expr, $pat:pat => $expr:expr) => {
        match $x { $pat => Some($expr), _ => None }
    };
}

/// A VM that runs on the AST, which can be used to help verify the validity of AST transforms
/// in unit tests.
///
/// Because it runs on a nested datastructure, it has no concept of a persistent instruction
/// pointer and cannot be paused or resumed.  It will always run the code until it falls off
/// past the last statement or hits a return.
#[derive(Debug, Clone, PartialEq)]
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
    pub call_log: Vec<LoggedCall>,
    var_values: HashMap<VarId, ScalarValue>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LoggedCall {
    pub real_time: i32,
    pub name: Ident,
    pub args: Vec<ScalarValue>,
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
            call_log: vec![],
            var_values: Default::default(),
        }
    }

    /// Run the statements until it hits the end or a `return`.  Returns the `return`ed value.
    pub fn run(&mut self, stmts: &[Sp<ast::Stmt>]) -> Option<ScalarValue> {
        match self._run(stmts) {
            RunResult::Nominal => None,
            RunResult::Return(value) => value,
            RunResult::IsJumping(goto) => panic!(
                "AST VM tried to jump to {} but this label did not exist within the same or outer scopes! \
                (note: for technical reasons, labels in inner scopes cannot be jumped to by this VM)",
                goto.destination,
            ),
        }
    }

    fn _run(&mut self, stmts: &[Sp<ast::Stmt>]) -> RunResult {
        let mut stmt_index = 0;

        'stmt: while stmt_index < stmts.len() {

            macro_rules! handle_goto {
                ($goto:expr) => { match $goto {
                    goto => match self.try_goto(stmts, goto) {
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
                    match self._run($block) {
                        RunResult::Nominal => {},
                        RunResult::Return(value) => return RunResult::Return(value),
                        RunResult::IsJumping(goto) => handle_goto!(&goto),
                    }
                };
            }

            if self.time < stmts[stmt_index].time {
                let time_diff = stmts[stmt_index].time - self.time;
                self.time += time_diff;
                self.real_time += time_diff;
            }

            // N.B. this can't easily be factored out into a method because it would require
            //      some way of storing or communicating a "instruction pointer", which
            //      doesn't exist due to the nested nature of the AST.
            match &stmts[stmt_index].body.value {
                ast::StmtBody::Jump(goto) => handle_goto!(goto),

                ast::StmtBody::CondJump { keyword, cond, jump } => {
                    if self.eval_cond(cond) == (keyword == &ast::CondKeyword::If) {
                        handle_goto!(jump);
                    }
                },

                ast::StmtBody::Return { value } => {
                    return RunResult::Return(value.as_ref().map(|x| self.eval(x)));
                },

                ast::StmtBody::CondChain(chain) => {
                    let ast::StmtCondChain { cond_blocks, else_block } = chain;

                    let mut branch_taken = false;
                    for ast::CondBlock { keyword, cond, block } in cond_blocks {
                        if self.eval_cond(cond) == (keyword == &ast::CondKeyword::If) {
                            branch_taken = true;
                            self.time = block.start_time();
                            handle_block!(&block.0);
                            break;
                        }
                    }

                    if !branch_taken {
                        if let Some(else_block) = else_block {
                            self.time = else_block.start_time();
                            handle_block!(&else_block.0);
                        }
                    }
                    self.time = chain.end_time();
                },

                ast::StmtBody::Loop { block } => {
                    loop {
                        handle_block!(&block.0);
                        self.time = block.start_time();
                    }
                },

                ast::StmtBody::While { is_do_while, cond, block } => {
                    if *is_do_while || self.eval_cond(cond) {
                        loop {
                            handle_block!(&block.0);
                            if self.eval_cond(cond) {
                                self.time = block.start_time();
                                continue;
                            }
                            break;
                        }
                    } else {
                        // nasty: in the zero-iterations case only, we jump over the loop
                        //    and therefore need to fix the time!
                        self.time = block.end_time();
                    }
                },

                ast::StmtBody::Times { count, block } => {
                    match self.eval(count) {
                        ScalarValue::Float(x) => panic!("float count {}", x),
                        ScalarValue::Int(0) => {
                            self.time = block.end_time();
                        },
                        ScalarValue::Int(count) => {
                            for i in 0..count {
                                handle_block!(&block.0);
                                if i + 1 < count {
                                    self.time = block.start_time();
                                }
                            }
                        },
                    }
                },

                ast::StmtBody::Expr(expr) => {
                    match &expr.value {
                        ast::Expr::Call { func, args } => {
                            let arg_values = args.iter().map(|arg| self.eval(arg)).collect::<Vec<_>>();
                            self.log_instruction(func, &arg_values);
                        },
                        _ => unimplemented!("VM statement expression: {:?}", expr)
                    }
                },

                ast::StmtBody::Assignment { var, op, value } => {
                    match op.value {
                        ast::AssignOpKind::Assign => {
                            let value = self.eval(value);
                            self.set_var_by_ast(var, value);
                        },
                        _ => {
                            let binop = op.corresponding_binop().expect("only Assign has no binop");
                            let value = sp!(op.span => binop).const_eval(
                                sp!(var.span => self.read_var_by_ast(var)),
                                sp!(value.span => self.eval(value)),
                            ).unwrap();
                            self.set_var_by_ast(var, value);
                        },
                    }
                },

                ast::StmtBody::Declaration { vars, .. } => {
                    for pair in vars.iter() {
                        let (var, expr) = &pair.value;
                        if let Some(expr) = expr {
                            let value = self.eval(expr);
                            self.set_var_by_ast(var, value);
                        }
                    }
                },

                ast::StmtBody::CallSub { .. } => unimplemented!("CallSub for AST VM"),

                ast::StmtBody::InterruptLabel(_) => {},

                ast::StmtBody::ScopeEnd(_) => {},

                ast::StmtBody::NoInstruction => {},
            }

            stmt_index += 1;
        }
        RunResult::Nominal
    }

    pub fn eval(&mut self, expr: &ast::Expr) -> ScalarValue {
        match expr {
            ast::Expr::Ternary { cond, left, right } => {
                match self.eval(cond) {
                    ScalarValue::Float(x) => panic!("type error: {:?}", x),
                    ScalarValue::Int(0) => self.eval(right),
                    ScalarValue::Int(_) => self.eval(left),
                }
            },
            ast::Expr::Binop(a, op, b) => op.const_eval(sp!(a.span => self.eval(a)), sp!(b.span => self.eval(b))).unwrap(),
            ast::Expr::Call { .. } => unimplemented!("func calls in VM exprs"),
            ast::Expr::Unop(op, x) => op.const_eval(sp!(x.span => self.eval(x))).unwrap(),
            ast::Expr::LitInt { value, .. } => ScalarValue::Int(*value),
            ast::Expr::LitFloat { value, .. } => ScalarValue::Float(*value),
            ast::Expr::LitString(s) => panic!("unexpected string value: {:?}", s),
            ast::Expr::Var(var) => self.read_var_by_ast(var),
        }
    }

    pub fn log_instruction(&mut self, name: &Ident, args: &[ScalarValue]) {
        self.call_log.push(LoggedCall {
            name: name.clone(),
            args: args.to_vec(),
            real_time: self.real_time,
        })
    }

    pub fn eval_cond(&mut self, cond: &ast::Cond) -> bool {
        match cond {
            ast::Cond::Decrement(var) => match self.read_var_by_ast(var) {
                ScalarValue::Float(x) => panic!("type error: {:?}", x),
                // REMINDER: unlike in C, `if (x--)` in ECL does not decrement past 0.
                ScalarValue::Int(0) => false,
                ScalarValue::Int(value) => {
                    self.set_var_by_ast(var, ScalarValue::Int(value - 1));
                    true
                },
            },
            ast::Cond::Expr(expr) => match self.eval(expr) {
                ScalarValue::Float(x) => panic!("type error: {:?}", x),
                ScalarValue::Int(value) => value != 0,
            }
        }
    }

    fn _var_key(&self, var: &ast::Var) -> VarId {
        match *var {
            ast::Var::Named { ref ident, .. } => panic!("AST VM requires name resolution (found {})", ident),
            ast::Var::Resolved { var_id, .. } => var_id,
        }
    }

    pub fn set_var(&mut self, var_id: VarId, value: ScalarValue) { self.var_values.insert(var_id, value); }
    pub fn get_var(&self, var_id: VarId) -> Option<ScalarValue> { self.var_values.get(&var_id).cloned() }

    fn set_var_by_ast(&mut self, var: &ast::Var, value: ScalarValue) {
        let key = self._var_key(var);
        self.var_values.insert(key, value);
    }

    fn read_var_by_ast(&self, var: &ast::Var) -> ScalarValue {
        let var_id = self._var_key(var);
        self.get_var(var_id).unwrap_or_else(|| panic!("read of uninitialized var: {:?}", var))
    }

    pub fn try_goto(&mut self, stmts: &[Sp<ast::Stmt>], goto: &ast::StmtGoto) -> Option<usize> {
        for (index, stmt) in stmts.iter().enumerate() {
            let mut labels = stmt.labels.iter().filter_map(|x| opt_match!(&x.value, ast::StmtLabel::Label(label) => label));
            if labels.any(|x| x == &goto.destination) {
                self.time = goto.time.unwrap_or(stmt.time);
                return Some(index);
            }
        }
        return None;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pos::Files;
    use crate::type_system::TypeSystem;
    use ScalarValue::{Int, Float};

    struct TestSpec {
        globals: Vec<(&'static str, i32)>,
        source: &'static str,
    }

    impl TestSpec {
        fn prepare(&self) -> ast::Block {
            let mut files = Files::new();
            let mut ast = files.parse::<ast::Block>("<input>", self.source.as_ref()).unwrap();

            let mut ty_ctx = TypeSystem::new();
            for &(name, reg) in &self.globals {
                ty_ctx.variables.declare_global_register_alias(name.parse().unwrap(), reg);
            }
            ty_ctx.resolve_names_block(&mut ast).unwrap();
            ast.value
        }
    }

    #[test]
    fn basic_variables() {
        let ast = TestSpec {
            globals: vec![("Y", -999)],
            source: r#"{
                int x = 3;
                x = 2 + 3 * x + $Y;
                return x + 1;
            }"#,
        }.prepare();

        let mut vm = AstVm::new();
        vm.set_var(VarId::Reg(-999), Int(7));

        assert_eq!(vm.run(&ast.0), Some(Int(19)));
    }

    #[test]
    fn basic_instrs_and_time() {
        let ast = TestSpec {
            globals: vec![("X", 100), ("Y", 101)],
            source: r#"{
                ins_345(0, 6);
            +10:
                foo(X, Y + 1.0);
            }"#,
        }.prepare();

        let mut vm = AstVm::new();
        vm.set_var(VarId::Reg(100), Int(3));
        vm.set_var(VarId::Reg(101), Float(7.0));
        vm.run(&ast.0);

        assert_eq!(vm.call_log, vec![
            LoggedCall { real_time: 0, name: "ins_345".parse().unwrap(), args: vec![Int(0), Int(6)] },
            LoggedCall { real_time: 10, name: "foo".parse().unwrap(), args: vec![Int(3), Float(8.0)] },
        ]);
    }

    #[test]
    fn while_do_while() {
        let while_ast = TestSpec {
            globals: vec![("X", 100), ("Y", 101)],
            source: r#"{
                X = 0;
                while (X < Y) {
                  +2:
                    X += 1;
                    lmao();
                  +3:
                }
              +4:
                end();
            }"#,
        }.prepare();

        let do_while_ast = TestSpec {
            globals: vec![("X", 100), ("Y", 101)],
            source: r#"{
                X = 0;
                do {
                  +2:
                    X += 1;
                    lmao();
                  +3:
                } while (X < Y);
              +4:
                end();
            }"#,
        }.prepare();
        dbg!(&do_while_ast);

        for ast in vec![&while_ast, &do_while_ast] {
            let mut vm = AstVm::new();
            vm.set_var(VarId::Reg(101), Int(3));
            vm.run(&ast.0);

            assert_eq!(vm.call_log, vec![
                LoggedCall { real_time: 2, name: "lmao".parse().unwrap(), args: vec![] },
                LoggedCall { real_time: 7, name: "lmao".parse().unwrap(), args: vec![] },
                LoggedCall { real_time: 12, name: "lmao".parse().unwrap(), args: vec![] },
                LoggedCall { real_time: 19, name: "end".parse().unwrap(), args: vec![] },
            ]);
        }

        // now let Y = 0 so we can see the difference between 'do' and 'do while'
        for (ast, expected_iters) in vec![(&while_ast, 0), (&do_while_ast, 1)] {
            let mut vm = AstVm::new();
            vm.set_var(VarId::Reg(101), Int(0));
            vm.run(&ast.0);

            assert_eq!(vm.call_log.len(), expected_iters + 1);
            assert_eq!(vm.real_time, (5 * expected_iters + 4) as i32);
        }
    }

    #[test]
    fn goto() {
        let ast = TestSpec {
            globals: vec![("X", 100)],
            source: r#"{
                X = 0;
                loop {
                    a(); goto B;
                20: C:
                    c(); goto exited;
                30: B:
                    b();
                    if (X == 1) goto C @ 5;
                    X = 1;
                    goto B;
                }
            exited:
                d();
            }"#,
        }.prepare();

        let mut vm = AstVm::new();
        vm.run(&ast.0);
        assert_eq!(vm.call_log, vec![
            LoggedCall { real_time: 0, name: "a".parse().unwrap(), args: vec![] },
            LoggedCall { real_time: 0, name: "b".parse().unwrap(), args: vec![] },
            LoggedCall { real_time: 0, name: "b".parse().unwrap(), args: vec![] },
            LoggedCall { real_time: 15, name: "c".parse().unwrap(), args: vec![] },
            LoggedCall { real_time: 15, name: "d".parse().unwrap(), args: vec![] },
        ]);
    }

    #[test]
    fn times() {
        let ast = TestSpec {
            globals: vec![("X", 100)],
            source: r#"{
                times(X) {
                    a();
                +10:
                }
                +5:
            }"#,
        }.prepare();

        for count in (0..3).rev() {
            let mut vm = AstVm::new();
            vm.set_var(VarId::Reg(100), Int(count));
            vm.run(&ast.0);

            assert_eq!(vm.call_log.len(), count as usize);
            assert_eq!(vm.real_time, count * 10 + 5);
            assert_eq!(vm.time, 15);
        }
    }

    #[test]
    fn cond_chain() {
        macro_rules! gen_spec {
            ($last_clause:literal) => {
                TestSpec {
                    globals: vec![("X", 100)],
                    source: concat!(r#"{
                        if (X == 1) {
                            a(1);
                        10:
                        } else if (X == 2) {
                            a(2);
                        20:
                        } "#, $last_clause, r#" {
                            a(3);
                        30:
                        }
                        b();
                    }"#),
                }
            };
        }
        let with_else = gen_spec!("else").prepare();
        let without_else = gen_spec!("else if (X == 3)").prepare();

        // both of these should have the same results for X in [1, 2, 3]
        for ast in vec![&with_else, &without_else] {
            for x in vec![1, 2, 3] {
                let mut vm = AstVm::new();
                vm.set_var(VarId::Reg(100), Int(x));
                vm.run(&ast.0);

                assert_eq!(vm.call_log, vec![
                    LoggedCall { real_time: 0, name: "a".parse().unwrap(), args: vec![Int(x)] },
                    LoggedCall { real_time: 10, name: "b".parse().unwrap(), args: vec![] },
                ]);
                assert_eq!(vm.time, 30);
                assert_eq!(vm.real_time, 10);
            }
        }
    }
}
