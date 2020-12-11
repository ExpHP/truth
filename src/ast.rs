#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stmt {
    pub labels: Vec<StmtLabel>,
    pub body: StmtBody,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StmtLabel {
    // TODO
}

/// Represents a statement, including the ';' if required, but
/// without any labels.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StmtBody {
    Jump {
        destination: Ident,
        time: Option<i32>,
    },
    CondJump {
        kind: CondKind,
        cond: Box<Expr>,
        destination: Ident,
        time: Option<i32>,
    },
    CondChain(StmtCondChain),
    While {
        is_do_while: bool,
        cond: Box<Expr>,
        block: Vec<Stmt>,
    },
    Times {
        count: Box<Expr>,
        block: Vec<Stmt>,
    },
    /// Expression followed by a semicolon.
    ///
    /// This is primarily for void-type "expressions" like raw instruction
    /// calls (which are grammatically indistinguishable from value-returning
    /// function calls), but may also represent a stack push in ECL.
    Expr(Box<Expr>),
}

// FIXME: This has been extracted just because the parser needs to build one incrementally.
//        Make a more sensible design.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StmtCondChain {
    pub cond_blocks: Vec<CondBlock>,
    pub else_block: Option<Vec<Stmt>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CondBlock {
    pub kind: CondKind,
    pub cond: Box<Expr>,
    pub block: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Ternary {
        cond: Box<Expr>,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Binop(Box<Expr>, BinopKind, Box<Expr>),
    Unop(UnopKind, Box<Expr>),
    LitInt(i32),
    Var(Var),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Var {
    Named {
        ty: Option<TypeKind>,
        ident: Ident,
    },
    Unnamed {
        ty: TypeKind,
        number: i32,
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CondKind {
    If, Unless,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinopKind {
    Add, Sub, Mul, Div, Rem,
    Eq, Ne, Lt, Le, Gt, Ge,
    BitOr, BitXor, BitAnd,
    LogicOr, LogicAnd,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnopKind {
    Not, Neg,
}
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeKind {
    Int,
    Float,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ident {
    pub ident: String,
}

impl UnopKind {
    pub fn eval_const_int(&self, x: i32) -> i32 {
        match self {
            UnopKind::Neg => -x,
            UnopKind::Not => (x != 0) as i32,
        }
    }
}

impl BinopKind {
    pub fn eval_const_int(&self, a: i32, b: i32) -> i32 {
        match self {
            BinopKind::Add => i32::wrapping_add(a, b),
            BinopKind::Sub => i32::wrapping_sub(a, b),
            BinopKind::Mul => i32::wrapping_mul(a, b),
            BinopKind::Div => i32::wrapping_div(a, b),
            BinopKind::Rem => i32::wrapping_rem(a, b),
            BinopKind::Eq => (a == b) as i32,
            BinopKind::Ne => (a != b) as i32,
            BinopKind::Lt => (a < b) as i32,
            BinopKind::Le => (a <= b) as i32,
            BinopKind::Gt => (a > b) as i32,
            BinopKind::Ge => (a >= b) as i32,
            BinopKind::LogicOr => if a == 0 { b } else { a },
            BinopKind::LogicAnd => if a == 0 { 0 } else { b },
            BinopKind::BitXor => a ^ b,
            BinopKind::BitAnd => a & b,
            BinopKind::BitOr => a | b,
        }
    }
}

impl Expr {
    pub fn const_eval_int(&self) -> Option<i32> {
        match self {
            &Expr::Ternary { ref cond, ref left, ref right } => {
                match cond.const_eval_int()? {
                    0 => right.const_eval_int(),
                    _ => left.const_eval_int(),
                }
            },
            &Expr::Binop(ref a, op, ref b) => Some(op.eval_const_int(a.const_eval_int()?, b.const_eval_int()?)),
            &Expr::Unop(op, ref x) => Some(op.eval_const_int(x.const_eval_int()?)),
            &Expr::LitInt(x) => Some(x),
            &Expr::Var(_) => None,
        }
    }
}

impl Var {
    pub fn ty(&self) -> Option<TypeKind> {
        match self {
            &Var::Unnamed { ty, .. } => Some(ty),
            &Var::Named { ty, .. } => ty,
        }
    }
}

impl From<&str> for Ident {
    fn from(s: &str) -> Ident {
        Ident { ident: s.into() }
    }
}
