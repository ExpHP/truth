use std::collections::HashMap;
use crate::ast;
use crate::pos::Sp;
use crate::ident::Ident;
use crate::var::VarId;
use crate::passes::const_simplify::ScalarValue;

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
#[derive(Debug, Clone)]
pub struct AstVm {
    /// Current script time in the VM.
    pub time: i32,
    /// Total amount of time the VM has been running.
    pub real_time: i32,
    /// Log of all opaque instructions that have executed.
    /// (anything using special syntax like operators, assignments and control flow are NOT logged)
    pub call_log: Vec<LoggedCall>,
    var_values: HashMap<VarId, ScalarValue>,
}

#[derive(Debug, Clone)]
pub struct LoggedCall {
    pub time: i32,
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

            if stmts[stmt_index].time > self.time {
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

                ast::StmtBody::CondChain(ast::StmtCondChain { cond_blocks, else_block }) => {
                    let mut branch_taken = false;
                    for ast::CondBlock { keyword, cond, block } in cond_blocks {
                        if self.eval_cond(cond) == (keyword == &ast::CondKeyword::If) {
                            branch_taken = true;
                            handle_block!(&block.0);
                            break;
                        }
                    }

                    if !branch_taken {
                        if let Some(else_block) = else_block {
                            handle_block!(&else_block.0);
                        }
                    }
                },

                ast::StmtBody::Loop { block } => {
                    loop { handle_block!(&block.0); }
                },

                ast::StmtBody::While { is_do_while, cond, block } => {
                    if *is_do_while || self.eval_cond(cond) {
                        loop {
                            handle_block!(&block.0);
                            if self.eval_cond(cond) {
                                continue;
                            }
                            break;
                        }
                    }
                },

                ast::StmtBody::Times { count, block } => {
                    match self.eval(count) {
                        ScalarValue::Float(x) => panic!("float count {}", x),
                        ScalarValue::Int(count) => {
                            for _ in 0..count {
                                handle_block!(&block.0);
                            }
                        }
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
                            self.set_var(var, value);
                        },
                        _ => {
                            let binop = op.corresponding_binop().expect("only Assign has no binop");
                            let value = sp!(op.span => binop).const_eval(
                                sp!(var.span => self.read_var(var)),
                                sp!(value.span => self.eval(value)),
                            ).unwrap();
                            self.set_var(var, value);
                        },
                    }
                },

                ast::StmtBody::Declaration { vars, .. } => {
                    for (var, expr) in vars.iter() {
                        if let Some(expr) = expr {
                            let value = self.eval(expr);
                            self.set_var(var, value);
                        }
                    }
                },

                ast::StmtBody::CallSub { .. } => unimplemented!("CallSub for AST VM"),

                ast::StmtBody::InterruptLabel(_) => {},

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
            ast::Expr::Var(var) => self.read_var(var),
        }
    }

    pub fn log_instruction(&mut self, name: &Ident, args: &[ScalarValue]) {
        self.call_log.push(LoggedCall {
            name: name.clone(),
            args: args.to_vec(),
            time: self.time,
        })
    }

    pub fn eval_cond(&mut self, cond: &ast::Cond) -> bool {
        match cond {
            ast::Cond::Decrement(var) => match self.read_var(var) {
                ScalarValue::Float(x) => panic!("type error: {:?}", x),
                // REMINDER: unlike in C, `if (x--)` in ECL does not decrement past 0.
                ScalarValue::Int(0) => false,
                ScalarValue::Int(value) => {
                    self.set_var(var, ScalarValue::Int(value - 1));
                    true
                },
            },
            ast::Cond::Expr(expr) => match self.eval(expr) {
                ScalarValue::Float(x) => panic!("type error: {:?}", x),
                ScalarValue::Int(value) => value != 0,
            }
        }
    }

    fn _var_key(&mut self, var: &ast::Var) -> VarId {
        match *var {
            ast::Var::Named { ref ident, .. } => panic!("AST VM requires name resolution (found {})", ident),
            ast::Var::Resolved { var_id, .. } => var_id,
        }
    }

    pub fn set_var(&mut self, var: &ast::Var, value: ScalarValue) {
        let key = self._var_key(var);
        self.var_values.insert(key, value);
    }

    pub fn read_var(&mut self, var: &ast::Var) -> ScalarValue {
        let key = self._var_key(var);
        self.var_values.get(&key).cloned().unwrap_or_else(|| panic!("read of uninitialized var: {:?}", var))
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
