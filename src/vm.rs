use crate::ast;
use crate::pos::Sp;
use crate::ident::Ident;
use crate::scope::VarId;
use std::collections::HashMap;

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
    var_values: HashMap<AnyVarId, Value>,
}

#[derive(Debug, Clone)]
pub struct LoggedCall {
    pub time: i32,
    pub name: Ident,
    pub args: Vec<Value>,
}

#[must_use]
enum RunResult {
    /// Nothing is out of the ordinary.
    Nominal,
    /// A `return` was encountered.
    Return(Option<Value>),
    /// A nested run call is jumping to an outer label.
    ///
    /// (for technical reasons, you can't jump to an inner label)
    IsJumping(ast::StmtGoto),
}

// FIXME use in const eval
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Value { Int(i32), Float(f32) }

// FIXME: make this the new VarId type and rename VarId to LocalId.
//        Put it on the AST to reduce ast::Var to two variants.
//        ...Also integrate it into TypeSystem.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AnyVarId {
    Local(VarId),
    Reg(i32),
}

impl AstVm {
    /// Run the statements until it hits the end or a `return`.  Returns the `return`ed value.
    pub fn run(&mut self, stmts: &[Sp<ast::Stmt>]) -> Option<Value> {
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
                        Value::Float(x) => panic!("float count {}", x),
                        Value::Int(count) => {
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
                            let value = apply_binop(binop, self.read_var(var), self.eval(value));
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

    pub fn eval(&mut self, expr: &ast::Expr) -> Value {
        match expr {
            ast::Expr::Ternary { cond, left, right } => {
                match self.eval(cond) {
                    Value::Float(x) => panic!("type error: {:?}", x),
                    Value::Int(0) => self.eval(right),
                    Value::Int(_) => self.eval(left),
                }
            },
            ast::Expr::Binop(a, op, b) => apply_binop(op.value, self.eval(a), self.eval(b)),
            ast::Expr::Call { .. } => unimplemented!("func calls in VM exprs"),
            ast::Expr::Unop(op, x) => apply_unop(op.value, self.eval(x)),
            ast::Expr::LitInt { value, .. } => Value::Int(*value),
            ast::Expr::LitFloat { value, .. } => Value::Float(*value),
            ast::Expr::LitString(s) => panic!("unexpected string value: {:?}", s),
            ast::Expr::Var(var) => self.read_var(var),
        }
    }

    pub fn log_instruction(&mut self, name: &Ident, args: &[Value]) {
        self.call_log.push(LoggedCall {
            name: name.clone(),
            args: args.to_vec(),
            time: self.time,
        })
    }

    pub fn eval_cond(&mut self, cond: &ast::Cond) -> bool {
        match cond {
            ast::Cond::Decrement(var) => match self.read_var(var) {
                Value::Float(x) => panic!("type error: {:?}", x),
                // REMINDER: unlike in C, `if (x--)` in ECL does not decrement past 0.
                Value::Int(0) => false,
                Value::Int(value) => {
                    self.set_var(var, Value::Int(value - 1));
                    true
                },
            },
            ast::Cond::Expr(expr) => match self.eval(expr) {
                Value::Float(x) => panic!("type error: {:?}", x),
                Value::Int(value) => value != 0,
            }
        }
    }

    fn _var_key(&mut self, var: &ast::Var) -> AnyVarId {
        match var {
            ast::Var::Named { ident, .. } => panic!("AST VM requires name resolution (found {})", ident),
            &ast::Var::Register { reg, .. } => AnyVarId::Reg(reg),
            &ast::Var::Local { var_id, .. } => AnyVarId::Local(var_id),
        }
    }

    pub fn set_var(&mut self, var: &ast::Var, value: Value) {
        let key = self._var_key(var);
        self.var_values.insert(key, value);
    }

    pub fn read_var(&mut self, var: &ast::Var) -> Value {
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

fn apply_binop(op: ast::BinopKind, a: Value, b: Value) -> Value {
    match (a, b) {
        (Value::Int(a), Value::Int(b)) => Value::Int(op.const_eval_int(a, b)),
        (Value::Float(_), Value::Float(_)) => unimplemented!("FIXME: needs const eval to use Value"),
        _ => panic!("mismatched types to {}: {:?}, {:?}", op, a, b),
    }
}

fn apply_unop(op: ast::UnopKind, a: Value) -> Value {
    match a {
        Value::Int(a) => Value::Int(op.const_eval_int(a)),
        Value::Float(_) => unimplemented!("FIXME: needs const eval to use Value"),
    }
}
