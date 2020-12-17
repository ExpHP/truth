use std::fmt;
use bstr::{BString};

use crate::meta::Meta;

/// Represents a complete script file.
#[derive(Debug, Clone, PartialEq)]
pub struct Script {
    pub items: Vec<Item>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    Func {
        inline: bool,
        keyword: FuncKeyword,
        name: Ident,
        params: Vec<(VarTypeKeyword, Ident)>,
        /// `Some` for definitions, `None` for declarations.
        code: Option<Block>,
    },
    AnmScript {
        number: Option<i32>,
        name: Ident,
        code: Block,
    },
    Meta {
        keyword: MetaKeyword,
        name: Option<Ident>,
        meta: Meta,
    },
    FileList {
        keyword: FileListKeyword,
        files: Vec<LitString>
    },
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FuncKeyword {
    Type(TypeKind),
    Sub,
    Timeline,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FileListKeyword {
    Anim, Ecli,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MetaKeyword {
    /// `entry` block for a texture in ANM.
    Entry,
}

// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub struct Stmt {
    pub labels: Vec<StmtLabel>,
    pub body: StmtBody,
}

#[derive(Debug, Clone, PartialEq)]
pub enum StmtLabel {
    AddTime(i32),
    SetTime(i32),
    Label(Ident),
    Difficulty {
        /// If `true`, the difficulty reverts to `"*"` after the next statement.
        temporary: bool,
        flags: DifficultyLabel,
    },
}

/// Represents a statement, including the ';' if required, but
/// without any labels.
#[derive(Debug, Clone, PartialEq)]
pub enum StmtBody {
    Jump(StmtGoto),
    CondJump {
        kind: CondKind,
        cond: Box<Expr>,
        jump: StmtGoto,
    },
    Return {
        value: Option<Box<Expr>>,
    },
    CondChain(StmtCondChain),
    While {
        is_do_while: bool,
        cond: Box<Expr>,
        block: Block,
    },
    Times {
        count: Box<Expr>,
        block: Block,
    },
    /// Expression followed by a semicolon.
    ///
    /// This is primarily for void-type "expressions" like raw instruction
    /// calls (which are grammatically indistinguishable from value-returning
    /// function calls), but may also represent a stack push in ECL.
    Expr(Box<Expr>),
    Assignment {
        var: Var,
        op: AssignOpKind,
        value: Box<Expr>,
    },
    Declaration {
        /// This is never `Void`. `None` means unspecified type (`var`).
        ty: VarTypeKeyword,
        vars: Vec<(Ident, Option<Box<Expr>>)>,
    },
    /// An explicit subroutine call. (ECL only)
    ///
    /// Will always have at least one of either the `@` or `async`.
    /// (otherwise, it will fall under `Expr` instead)
    CallSub {
        at_symbol: bool,
        async_: Option<CallAsyncKind>,
        func: Ident,
        args: Vec<Box<Expr>>,
    }
}

/// The body of a `goto` statement, without the `;`.
#[derive(Debug, Clone, PartialEq)]
pub struct StmtGoto {
    pub destination: Ident,
    pub time: Option<i32>,
}

// FIXME: This has been extracted just because the parser needs to build one incrementally.
//        Make a more sensible design.
#[derive(Debug, Clone, PartialEq)]
pub struct StmtCondChain {
    pub cond_blocks: Vec<CondBlock>,
    pub else_block: Option<Block>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CondBlock {
    pub kind: CondKind,
    pub cond: Box<Expr>,
    pub block: Block,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CallAsyncKind {
    CallAsync,
    CallAsyncId(Box<Expr>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CondKind {
    If, Unless,
}

// TODO: Parse
pub type DifficultyLabel = BString;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AssignOpKind {
    Assign,
    Add, Sub, Mul, Div, Rem,
    BitOr, BitXor, BitAnd,
}

/// A braced series of statements, typically written at an increased
/// indentation level.
#[derive(Debug, Clone, PartialEq)]
pub struct Block(pub Vec<Stmt>);

// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Ternary {
        cond: Box<Expr>,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Binop(Box<Expr>, BinopKind, Box<Expr>),
    Call {
        func: Ident,
        args: Vec<Box<Expr>>,
    },
    Decrement {
        var: Var,
    },
    Unop(UnopKind, Box<Expr>),
    LitInt(i32),
    LitFloat(f32),
    LitString(LitString),
    Var(Var),
}

#[derive(Debug, Clone, PartialEq)]
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

impl UnopKind {
    pub fn eval_const_int(&self, x: i32) -> i32 {
        match self {
            UnopKind::Neg => i32::wrapping_neg(x),
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
            &Expr::Call { .. } => None,
            &Expr::Ternary { ref cond, ref left, ref right } => {
                match cond.const_eval_int()? {
                    0 => right.const_eval_int(),
                    _ => left.const_eval_int(),
                }
            },
            &Expr::Binop(ref a, op, ref b) => Some(op.eval_const_int(a.const_eval_int()?, b.const_eval_int()?)),
            &Expr::Unop(op, ref x) => Some(op.eval_const_int(x.const_eval_int()?)),
            &Expr::Decrement { .. } => None,
            &Expr::LitInt(x) => Some(x),
            &Expr::LitFloat(_) => None,
            &Expr::LitString(_) => None,
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VarTypeKeyword {
    Int,
    Float,
    Var,
}

// =============================================================================

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeKind {
    Int,
    Float,
    Void,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ident {
    pub ident: String,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LitString {
    pub string: BString,
}

impl From<&str> for Ident {
    fn from(s: &str) -> Ident {
        Ident { ident: s.into() }
    }
}

impl std::borrow::Borrow<str> for Ident {
    fn borrow(&self) -> &str {
        &self.ident
    }
}


impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.ident[..])
    }
}
