use bstr::{BString};

use crate::meta;
use crate::ident::Ident;
use crate::pos::Sp;
use crate::error::CompileError;
use crate::type_system;

// Quick little util for stringly enums.
macro_rules! string_enum {
    (
        $(#[$($Enum_attr:tt)+])*
        $vis:vis enum $Enum:ident {
            $(
                $(#[doc = $variant_doc:literal])*
                #[str = $variant_str:literal] $Variant:ident,
            )*
        }
    ) => {
        $(#[$($Enum_attr)+])*
        $vis enum $Enum {
            $( $(#[doc = $variant_doc])* $Variant, )*
        }

        // used mainly for error messages
        impl ::std::fmt::Display for $Enum {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                ::std::fmt::Display::fmt(match self {
                    $( $Enum::$Variant => $variant_str, )*
                }, f)
            }
        }

        impl crate::fmt::Format for $Enum {
            fn fmt<W: ::std::io::Write>(&self, out: &mut crate::fmt::Formatter<W>) -> crate::fmt::Result {
                out.fmt(format_args!("{}", self))
            }
        }
    }
}

// =============================================================================

/// Represents a complete script file.
#[derive(Debug, Clone, PartialEq)]
pub struct Script {
    pub mapfiles: Vec<Sp<LitString>>,
    pub items: Vec<Sp<Item>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    Func {
        inline: bool,
        keyword: FuncKeyword,
        name: Ident,
        params: Vec<(VarDeclKeyword, Ident)>,
        /// `Some` for definitions, `None` for declarations.
        code: Option<Block>,
    },
    AnmScript {
        number: Option<Sp<i32>>,
        name: Sp<Ident>,
        code: Block,
    },
    Meta {
        keyword: Sp<MetaKeyword>,
        name: Option<Sp<Ident>>,
        fields: Sp<meta::Fields>,
    },
    FileList {
        keyword: FileListKeyword,
        files: Vec<LitString>
    },
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FuncKeyword {
    Type(FuncReturnType),
    Sub,
    Timeline,
}

string_enum!{
    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum FuncReturnType {
        #[str = "int"] Int,
        #[str = "float"] Float,
        #[str = "void"] Void,
    }
}

string_enum!{
    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum FileListKeyword {
        #[str = "anim"] Anim,
        #[str = "ecli"] Ecli,
    }
}

string_enum! {
    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum MetaKeyword {
        /// `entry` block for a texture in ANM.
        #[str = "entry"] Entry,
        #[str = "meta"] Meta,
    }
}

// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub struct Stmt {
    pub time: i32,
    pub labels: Vec<Sp<StmtLabel>>,
    pub body: Sp<StmtBody>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum StmtLabel {
    Label(Sp<Ident>),
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
        keyword: Sp<CondKeyword>,
        cond: Sp<Cond>,
        jump: StmtGoto,
    },
    Return {
        value: Option<Sp<Expr>>,
    },
    CondChain(StmtCondChain),
    Loop {
        block: Block,
    },
    While {
        is_do_while: bool,
        cond: Sp<Cond>,
        block: Block,
    },
    Times {
        count: Sp<Expr>,
        block: Block,
    },
    /// Expression followed by a semicolon.
    ///
    /// This is primarily for void-type "expressions" like raw instruction
    /// calls (which are grammatically indistinguishable from value-returning
    /// function calls), but may also represent a stack push in ECL.
    Expr(Sp<Expr>),
    Assignment {
        var: Sp<Var>,
        op: Sp<AssignOpKind>,
        value: Sp<Expr>,
    },
    Declaration {
        ty: VarDeclKeyword,
        vars: Vec<(Ident, Option<Sp<Expr>>)>,
    },
    /// An explicit subroutine call. (ECL only)
    ///
    /// Will always have at least one of either the `@` or `async`.
    /// (otherwise, it will fall under `Expr` instead)
    CallSub {
        at_symbol: bool,
        async_: Option<CallAsyncKind>,
        func: Sp<Ident>,
        args: Vec<Sp<Expr>>,
    },
    /// An interrupt label: `interrupt[2]:`.
    ///
    /// Because this compiles to an expression, we store it as a statement in the AST rather than
    /// as a label.
    InterruptLabel(Sp<i32>),
    /// A virtual instruction that completely disappears during compilation.
    ///
    /// This is a trivial statement that doesn't even compile to a `nop();`.
    /// It is inserted at the beginning and end of code blocks in order to help implement some
    /// of the following things:
    ///
    /// * A time label at the end of a block.
    /// * A time label at the beginning of a loop's body.
    ///
    /// Note that these may also appear in the middle of a block in the AST if a transformation
    /// pass has e.g. inlined the contents of one block into another.
    NoInstruction,
}

/// The body of a `goto` statement, without the `;`.
#[derive(Debug, Clone, PartialEq)]
pub struct StmtGoto {
    pub destination: Sp<Ident>,
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
    pub keyword: CondKeyword,
    pub cond: Sp<Cond>,
    pub block: Block,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Cond {
    Decrement(Sp<Var>),
    Expr(Sp<Expr>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum CallAsyncKind {
    CallAsync,
    CallAsyncId(Box<Sp<Expr>>),
}

string_enum! {
    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum CondKeyword {
        #[str = "if"] If,
        // TODO: not currently implemented.  All places that would be affected explicitly match on
        //       the CondKeyword so that we can't miss them if/when the feature is added.
        // #[str = "unless"] Unless,
    }
}

// TODO: Parse
pub type DifficultyLabel = BString;

string_enum! {
    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum AssignOpKind {
        #[str = "="] Assign,
        #[str = "+="] Add,
        #[str = "-="] Sub,
        #[str = "*="] Mul,
        #[str = "/="] Div,
        #[str = "%="] Rem,
        #[str = "|="] BitOr,
        #[str = "^="] BitXor,
        #[str = "&="] BitAnd,
    }
}

/// A braced series of statements, typically written at an increased
/// indentation level.
#[derive(Debug, Clone, PartialEq)]
pub struct Block(pub Vec<Sp<Stmt>>);

// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Ternary {
        cond: Box<Sp<Expr>>,
        left: Box<Sp<Expr>>,
        right: Box<Sp<Expr>>,
    },
    Binop(Box<Sp<Expr>>, Sp<BinopKind>, Box<Sp<Expr>>),
    Call {
        func: Sp<Ident>,
        args: Vec<Sp<Expr>>,
    },
    Unop(Sp<UnopKind>, Box<Sp<Expr>>),
    LitInt {
        value: i32,
        /// A hint to the formatter that it should use hexadecimal.
        /// (may not necessarily represent the original radix of a parsed token)
        hex: bool,
    },
    LitFloat { value: f32 },
    LitString(LitString),
    Var(Sp<Var>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Var {
    Named {
        ty: Option<VarReadType>,
        ident: Ident,
    },
    Unnamed {
        ty: VarReadType,
        number: i32,
    }
}

string_enum! {
    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum BinopKind {
        #[str = "+"] Add,
        #[str = "-"] Sub,
        #[str = "*"] Mul,
        #[str = "/"] Div,
        #[str = "%"] Rem,
        #[str = "=="] Eq,
        #[str = "!="] Ne,
        #[str = "<"] Lt,
        #[str = "<="] Le,
        #[str = ">"] Gt,
        #[str = ">="] Ge,
        #[str = "|"] BitOr,
        #[str = "^"] BitXor,
        #[str = "&"] BitAnd,
        #[str = "||"] LogicOr,
        #[str = "&&"] LogicAnd,
    }
}

string_enum! {
    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum UnopKind {
        #[str = "!"] Not,
        #[str = "-"] Neg,
    }
}

impl From<i32> for Expr {
    fn from(value: i32) -> Expr { Expr::LitInt { value, hex: false } }
}
impl From<f32> for Expr {
    fn from(value: f32) -> Expr { Expr::LitFloat { value } }
}

// =============================================================================

impl Var {
    pub fn ty(&self) -> Option<VarReadType> {
        match self {
            &Var::Unnamed { ty, .. } => Some(ty),
            &Var::Named { ty, .. } => ty,
        }
    }
}

string_enum! {
    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum VarDeclKeyword {
        #[str = "int"] Int,
        #[str = "float"] Float,
        #[str = "var"] Var,
    }
}

/// The hinted type of a variable at a usage site.
///
/// E.g. a variable's type may be hinted with the use of `$` or `%` prefixes.
/// (or it might not be hinted, meaning its type must be determined through other means)
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VarReadType {
    Int,
    Float,
}

impl From<type_system::ScalarType> for VarReadType {
    fn from(x: type_system::ScalarType) -> VarReadType {
        match x {
            type_system::ScalarType::Int => VarReadType::Int,
            type_system::ScalarType::Float => VarReadType::Float,
        }
    }
}

impl From<VarReadType> for type_system::ScalarType {
    fn from(x: VarReadType) -> type_system::ScalarType {
        match x {
            VarReadType::Int => type_system::ScalarType::Int,
            VarReadType::Float => type_system::ScalarType::Float,
        }
    }
}

/// A literal string, which may be encoded in UTF-8 or Shift-JIS.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LitString<S=BString> {
    pub string: S,
}

impl<S: AsRef<[u8]>> Sp<LitString<S>> {
    /// Interpret as a path.
    ///
    /// This will assume a UTF-8 encoding, and thus may fail on Shift-JIS encoded strings.
    /// It has to do this because Windows path APIs are encoding-aware.
    pub fn as_path(&self) -> Result<&std::path::Path, CompileError> {
        match std::str::from_utf8(self.string.as_ref()) {
            Err(_) => Err(error!(
                message("cannot parse path as UTF-8"),
                primary(self, "not valid UTF-8"),
                note("paths are always read as UTF-8 regardless of the encoding of the file"),
            )),
            Ok(p) => Ok(p.as_ref()),
        }
    }
}

macro_rules! generate_visitor_stuff {
    ($Visit: ident $(,$mut: tt)?) => {
        /// Recursive AST traversal trait.
        pub trait $Visit {
            fn visit_item(&mut self, e: & $($mut)? Sp<Item>) { walk_item(self, e) }
            /// This is called only on the outermost blocks of each function.
            fn visit_func_body(&mut self, e: & $($mut)? Block) { self.visit_block(e) }
            fn visit_block(&mut self, e: & $($mut)? Block) { walk_block(self, e) }
            fn visit_stmt(&mut self, e: & $($mut)? Sp<Stmt>) { walk_stmt(self, e) }
            fn visit_stmt_body(&mut self, e: & $($mut)? Sp<StmtBody>) { walk_stmt_body(self, e) }
            fn visit_expr(&mut self, e: & $($mut)? Sp<Expr>) { walk_expr(self, e) }
        }

        pub fn walk_script<V>(v: &mut V, x: & $($mut)? Script)
        where V: ?Sized + $Visit,
        {
            for item in & $($mut)? x.items {
                v.visit_item(item)
            }
        }

        pub fn walk_item<V>(v: &mut V, x: & $($mut)? Sp<Item>)
        where V: ?Sized + $Visit,
        {
            match & $($mut)? x.value {
                Item::Func {
                    code, inline: _, keyword: _, name: _, params: _,
                } => {
                    if let Some(code) = code {
                        v.visit_func_body(code);
                    }
                },
                Item::AnmScript { number: _, name: _, code } => {
                    v.visit_func_body(code);
                },
                Item::Meta { .. } => {},
                Item::FileList { .. } => {},
            }
        }

        pub fn walk_block<V>(v: &mut V, x: & $($mut)? Block)
        where V: ?Sized + $Visit,
        {
            for stmt in & $($mut)? x.0 {
                v.visit_stmt(stmt);
            }
        }

        pub fn walk_stmt<V>(v: &mut V, x: & $($mut)? Sp<Stmt>)
        where V: ?Sized + $Visit,
        {
            v.visit_stmt_body(& $($mut)? x.body);
        }

        pub fn walk_stmt_body<V>(v: &mut V, x: & $($mut)? Sp<StmtBody>)
        where V: ?Sized + $Visit,
        {
            match & $($mut)? x.value {
                StmtBody::Jump(_) => {},
                StmtBody::Return { value } => {
                    if let Some(value) = value {
                        v.visit_expr(value);
                    }
                },
                StmtBody::Loop { block } => v.visit_block(block),
                StmtBody::CondJump { cond, keyword: _, jump: _ } => {
                    walk_cond(v, cond);
                },
                StmtBody::CondChain(chain) => {
                    let StmtCondChain { cond_blocks, else_block } = chain;
                    for CondBlock { cond, block, keyword: _ } in cond_blocks {
                        walk_cond(v, cond);
                        v.visit_block(block);
                    }
                    if let Some(block) = else_block {
                        v.visit_block(block);
                    }
                },
                StmtBody::While { is_do_while: true, cond, block } => {
                    walk_cond(v, cond);
                    v.visit_block(block);
                },
                StmtBody::While { is_do_while: false, cond, block } => {
                    v.visit_block(block);
                    walk_cond(v, cond);
                },
                StmtBody::Times { count, block } => {
                    v.visit_expr(count);
                    v.visit_block(block);
                },
                StmtBody::Expr(e) => {
                    v.visit_expr(e);
                },
                StmtBody::Assignment { var: _, op: _, value } => {
                    v.visit_expr(value);
                },
                StmtBody::Declaration { ty: _, vars } => {
                    for (_ident, value) in vars {
                        if let Some(value) = value {
                            v.visit_expr(value);
                        }
                    }
                },
                StmtBody::CallSub { at_symbol: _, async_: _, func: _, args } => {
                    for arg in args {
                        v.visit_expr(arg);
                    }
                },
                StmtBody::InterruptLabel(_) => {},
                StmtBody::NoInstruction => {},
            }
        }

        fn walk_cond<V>(v: &mut V, e: & $($mut)? Sp<Cond>)
        where V: ?Sized + $Visit,
        {
            match & $($mut)? e.value {
                Cond::Decrement(_) => {},
                Cond::Expr(e) => walk_expr(v, e),
            }
        }

        pub fn walk_expr<V>(v: &mut V, e: & $($mut)? Sp<Expr>)
        where V: ?Sized + $Visit,
        {
            match & $($mut)? e.value {
                Expr::Ternary { cond, left, right } => {
                    v.visit_expr(cond);
                    v.visit_expr(left);
                    v.visit_expr(right);
                },
                Expr::Binop(a, _op, b) => {
                    v.visit_expr(a);
                    v.visit_expr(b);
                },
                Expr::Call { func: _, args } => {
                    for arg in args {
                        v.visit_expr(arg);
                    }
                },
                Expr::Unop(_op, x) => v.visit_expr(x),
                Expr::LitInt { value: _, hex: _ } => {},
                Expr::LitFloat { value: _ } => {},
                Expr::LitString(_s) => {},
                Expr::Var(_v) => {},
            }
        }
    };
}

mod mut_ {
    use super::*;
    generate_visitor_stuff!(VisitMut, mut);
}
pub use self::mut_::{
    VisitMut,
    walk_script as walk_mut_script,
    walk_item as walk_mut_item,
    walk_block as walk_mut_block,
    walk_stmt as walk_mut_stmt,
    walk_stmt_body as walk_mut_stmt_body,
    walk_expr as walk_mut_expr,
};
mod ref_ {
    use super::*;
    generate_visitor_stuff!(Visit);
}
pub use self::ref_::{
    Visit, walk_script, walk_item, walk_block, walk_stmt,
    walk_stmt_body, walk_expr,
};
