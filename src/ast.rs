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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Ternary {
        cond: Box<Expr>,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Binop(Box<Expr>, BinopKind, Box<Expr>),
    Unop(UnopKind, Box<Expr>),
    LitInt(i128),
//    Ident(Vec<u8>),
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
pub enum TypeKind {
    Int,
    Float,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ident {
    ident: String,
}

impl UnopKind {
    pub fn eval_const_int(&self, x: i128) -> i128 {
        match self {
            UnopKind::Neg => -x,
            UnopKind::Not => (x != 0) as i128,
        }
    }
}

impl BinopKind {
    pub fn eval_const_int(&self, a: i128, b: i128) -> i128 {
        match self {
            BinopKind::Add => a + b,
            BinopKind::Sub => a - b,
            BinopKind::Mul => a * b,
            BinopKind::Div => a / b,
            BinopKind::Rem => a % b,
            BinopKind::Eq => (a == b) as i128,
            BinopKind::Ne => (a != b) as i128,
            BinopKind::Lt => (a < b) as i128,
            BinopKind::Le => (a <= b) as i128,
            BinopKind::Gt => (a > b) as i128,
            BinopKind::Ge => (a >= b) as i128,
            BinopKind::LogicOr => if a == 0 { b } else { a },
            BinopKind::LogicAnd => if a == 0 { 0 } else { b },
            BinopKind::BitXor => a ^ b,
            BinopKind::BitAnd => a & b,
            BinopKind::BitOr => a | b,
        }
    }
}

impl Expr {
    pub fn const_eval_int(&self) -> i128 {
        match self {
            &Expr::Ternary { ref cond, ref left, ref right } => {
                match cond.const_eval_int() {
                    0 => right.const_eval_int(),
                    _ => left.const_eval_int(),
                }
            },
            &Expr::Binop(ref a, op, ref b) => op.eval_const_int(a.const_eval_int(), b.const_eval_int()),
            &Expr::Unop(op, ref x) => op.eval_const_int(x.const_eval_int()),
            &Expr::LitInt(x) => x,
        }
    }
}
