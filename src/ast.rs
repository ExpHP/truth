use bstr::{BString};
use std::fmt;

use crate::meta;
use crate::resolve::{ResolveId, RegId};
use crate::ident::{Ident, ResIdent};
use crate::pos::{Sp, Span};
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

/// Type used in the AST for the span of a single token with no useful data.
///
/// This can be used for things like keywords.  We use [`Sp`]`<()>` instead of [`Span`]
/// because the latter would have an impact on equality tests.
pub type TokenSpan = Sp<()>;

/// Represents a complete script file.
#[derive(Debug, Clone, PartialEq)]
pub struct Script {
    pub mapfiles: Vec<Sp<LitString>>,
    pub image_sources: Vec<Sp<LitString>>,
    pub items: Vec<Sp<Item>>,
}

impl Script {
    pub fn expect_no_image_sources(&self) -> Result<(), CompileError> {
        if let Some(path) = self.image_sources.get(0) {
            Err(error!(
                message("unexpected image_source"),
                primary(path.span, "image_source not valid in this format"),
            ))
        } else { Ok(()) }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    Func {
        inline: Option<TokenSpan>,
        keyword: Sp<FuncKeyword>,
        ident: Sp<ResIdent>,
        params: Vec<(Sp<VarDeclKeyword>, Sp<ResIdent>)>,
        /// `Some` for definitions, `None` for declarations.
        code: Option<Block>,
    },
    AnmScript {
        keyword: TokenSpan,
        number: Option<Sp<i32>>,
        ident: Sp<Ident>,
        code: Block,
    },
    Meta {
        keyword: Sp<MetaKeyword>,
        ident: Option<Sp<Ident>>,
        fields: Sp<meta::Fields>,
    },
    FileList {
        keyword: Sp<FileListKeyword>,
        files: Vec<Sp<LitString>>
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
    pub body: StmtBody,
}

// FIXME: awkward now that `label:` is implemented as a statement instead
#[derive(Debug, Clone, PartialEq)]
pub enum StmtLabel {
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
    // FIXME: rename to Goto
    Jump(StmtGoto),
    // FIXME: rename to CondGoto
    CondJump {
        keyword: Sp<CondKeyword>,
        cond: Sp<Cond>,
        jump: StmtGoto,
    },
    Return {
        keyword: TokenSpan,
        value: Option<Sp<Expr>>,
    },
    CondChain(StmtCondChain),
    Loop {
        keyword: TokenSpan,
        block: Block,
    },
    While {
        while_keyword: TokenSpan,
        do_keyword: Option<TokenSpan>,
        cond: Sp<Cond>,
        block: Block,
    },
    Times {
        keyword: TokenSpan,
        clobber: Option<Sp<Var>>,
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
        keyword: Sp<VarDeclKeyword>,
        vars: Vec<Sp<(Sp<Var>, Option<Sp<Expr>>)>>,
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
    /// Because this compiles to an instruction, we store it as a statement in the AST rather than
    /// as a label.
    InterruptLabel(Sp<i32>),

    /// A virtual instruction representing a label that can be jumped to.
    Label(Sp<Ident>),

    /// A virtual instruction that marks the end of a variable's lexical scope.
    ///
    /// Blocks are eliminated during early compilation passes, leaving behind these as the only
    /// remaining way of identifying the end of a variable's scope.  They are used during lowering
    /// to determine when to release resources (like registers) held by locals.
    ScopeEnd(ResolveId),

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


impl StmtBody {
    pub fn descr(&self) -> &'static str { match self {
        StmtBody::Jump { .. } => "goto",
        StmtBody::CondJump { .. } => "conditional goto",
        StmtBody::Return { .. } => "return statement",
        StmtBody::CondChain { .. } => "conditional chain",
        StmtBody::Loop { .. } => "loop",
        StmtBody::While { .. } => "while(..)",
        StmtBody::Times { .. } => "times(..)",
        StmtBody::Expr { .. } => "expression statement",
        StmtBody::Assignment { .. } => "assignment",
        StmtBody::Declaration { .. } => "var declaration",
        StmtBody::CallSub { .. } => "sub call",
        StmtBody::InterruptLabel { .. } => "interrupt label",
        StmtBody::Label { .. } => "label",
        StmtBody::ScopeEnd { .. } => "<ScopeEnd>",
        StmtBody::NoInstruction { .. } => "<NoInstruction>",
    }}
}

/// The body of a `goto` statement, without the `;`.
#[derive(Debug, Clone, PartialEq)]
pub struct StmtGoto {
    pub destination: Sp<Ident>,
    pub time: Option<i32>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StmtCondChain {
    // FIXME why do these have spans
    pub cond_blocks: Vec<Sp<CondBlock>>,
    pub else_block: Option<Block>,
}

impl StmtCondChain {
    pub fn last_block(&self) -> &Block {
        self.else_block.as_ref()
            .unwrap_or_else(|| &self.cond_blocks.last().unwrap().block)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CondBlock {
    pub keyword: Sp<CondKeyword>,
    pub cond: Sp<Cond>,
    pub block: Block,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Cond {
    Expr(Sp<Expr>),
    /// This is how jmpDec works in register-based languages.
    ///
    /// (stack-based ECL instead has a decrement operator that is postdec)
    PreDecrement(Sp<Var>),
}

impl From<Sp<Expr>> for Sp<Cond> {
    fn from(expr: Sp<Expr>) -> Sp<Cond> { sp!(expr.span => Cond::Expr(expr)) }
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
        #[str = "unless"] Unless,
    }
}

impl CondKeyword {
    pub fn negate(self) -> Self { match self {
        CondKeyword::If => CondKeyword::Unless,
        CondKeyword::Unless => CondKeyword::If,
    }}
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

impl AssignOpKind {
    pub fn corresponding_binop(self) -> Option<BinopKind> {
        match self {
            token![=] => None,
            token![+=] => Some(token![+]),
            token![-=] => Some(token![-]),
            token![*=] => Some(token![*]),
            token![/=] => Some(token![/]),
            token![%=] => Some(token![%]),
            token![|=] => Some(token![|]),
            token![^=] => Some(token![^]),
            token![&=] => Some(token![&]),
        }
    }
}

/// A braced series of statements, typically written at an increased indentation level.
///
/// Every Block always has at least two [`Stmt`]s, as on creation it is bookended by dummy
/// statements to ensure it has a well-defined start and end time.
#[derive(Debug, Clone, PartialEq)]
pub struct Block(pub Vec<Sp<Stmt>>);

impl Block {
    /// Effective time label before the first statement in the loop body.
    pub fn start_time(&self) -> i32 { self.first_stmt().time }

    /// Effective time label after the final statement in the loop body.
    pub fn end_time(&self) -> i32 { self.last_stmt().time }

    /// Zero-length span at beginning of block interior.
    pub fn start_span(&self) -> Span { self.first_stmt().span.start_span() }

    /// Zero-length span at end of block interior.
    pub fn end_span(&self) -> Span { self.last_stmt().span.end_span() }

    pub fn first_stmt(&self) -> &Sp<Stmt> {
        self.0.get(0).expect("(bug?) unexpected empty block!")
    }

    pub fn last_stmt(&self) -> &Sp<Stmt> {
        self.0.last().expect("(bug?) unexpected empty block!")
    }
}

// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Ternary {
        cond: Box<Sp<Expr>>,
        question: Sp<()>,
        left: Box<Sp<Expr>>,
        colon: Sp<()>,
        right: Box<Sp<Expr>>,
    },
    Binop(Box<Sp<Expr>>, Sp<BinopKind>, Box<Sp<Expr>>),
    Call {
        // note: deliberately called 'name' instead of 'ident' so that you can
        //       match both this and the inner ident without shadowing
        name: Sp<CallableName>,
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

impl Expr {
    pub fn zero(ty: type_system::ScalarType) -> Self { match ty {
        type_system::ScalarType::Int => 0.into(),
        type_system::ScalarType::Float => 0.0.into(),
        type_system::ScalarType::String => panic!("Expr::zero() called on type String"),
    }}
    pub fn descr(&self) -> &'static str { match self {
        Expr::Ternary { .. } => "ternary",
        Expr::Binop { .. } => "binary operator",
        Expr::Call { .. } => "call expression",
        Expr::Unop { .. } => "unary operator",
        Expr::LitInt { .. } => "literal integer",
        Expr::LitFloat { .. } => "literal float",
        Expr::LitString { .. } => "literal string",
        Expr::Var { .. } => "var expression",
    }}
}

/// An identifier in a function call.
///
/// Raw instructions (`ins_`) are separately recognized so that they don't have to take part
/// in name resolution.  This makes it easier to use the AST VM [`crate::vm::AstVm`].
#[derive(Debug, Clone, PartialEq)]
pub enum CallableName {
    Normal { ident: ResIdent },
    Ins { opcode: u16 },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Var {
    /// A variable mentioned by name, possibly with a type sigil.
    Named {
        ty_sigil: Option<VarReadType>,
        ident: ResIdent,
    },
    /// A raw register access. (e.g. `[10004.0]`)
    Reg {
        ty_sigil: VarReadType,
        reg: RegId,
    },
}

impl Var {
    pub fn eq_upto_ty(&self, other: &Var) -> bool {
        match (self, other) {
            (Var::Named { ident: a, .. }, Var::Named { ident: b, .. }) => a.expect_res() == b.expect_res(),
            (Var::Reg { reg: a, .. }, Var::Reg { reg: b, .. }) => a == b,
            _ => false,
        }
    }

    /// Get the *explicitly annotated* read type.  If there isn't one, returns `None`.
    ///
    /// Because this does not use the type system, it is unable to determine anything in the case
    /// that there is no type sigil.  [`crate::type_system::TypeSystem::var_read_ty_from_ast`] for a
    /// more reliable way of determining the type of a [`Var`].
    pub fn read_ty(&self) -> Option<VarReadType> {
        match *self {
            Var::Named { ty_sigil, .. } => ty_sigil,
            Var::Reg { ty_sigil, .. } => Some(ty_sigil),
        }
    }

    pub fn set_ty_sigil(&mut self, ty_sigil: Option<VarReadType>) {
        match self {
            Var::Named { ty_sigil: ptr, .. } => *ptr = ty_sigil,
            Var::Reg { ty_sigil: ptr, .. } => *ptr = ty_sigil.expect("can't erase type sigil of register"),
        }
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

impl BinopKind {
    pub fn is_comparison(self) -> bool {
        matches!(self, token![==] | token![!=] | token![<] | token![<=] | token![>] | token![>=])
    }

    pub fn negate_comparison(self) -> Option<BinopKind> { match self {
        token![==] => Some(token![!=]),
        token![!=] => Some(token![==]),
        token![<=] => Some(token![>]),
        token![>=] => Some(token![<]),
        token![<] => Some(token![>=]),
        token![>] => Some(token![<=]),
        _ => None,
    }}
}

string_enum! {
    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum UnopKind {
        #[str = "!"] Not,
        #[str = "-"] Neg,
        #[str = "sin"] Sin,
        #[str = "cos"] Cos,
        #[str = "sqrt"] Sqrt,
        #[str = "_S"] CastI,
        #[str = "_f"] CastF,
    }
}

impl UnopKind {
    pub fn is_cast(&self) -> bool {
        matches!(self, token![_S] | token![_f])
    }
}

impl From<i32> for Expr {
    fn from(value: i32) -> Expr { Expr::LitInt { value, hex: false } }
}
impl From<f32> for Expr {
    fn from(value: f32) -> Expr { Expr::LitFloat { value } }
}
impl From<BString> for Expr {
    fn from(string: BString) -> Expr { Expr::LitString(LitString { string }) }
}

impl From<Sp<i32>> for Sp<Expr> {
    fn from(num: Sp<i32>) -> Sp<Expr> { sp!(num.span => Expr::from(num.value)) }
}
impl From<Sp<f32>> for Sp<Expr> {
    fn from(num: Sp<f32>) -> Sp<Expr> { sp!(num.span => Expr::from(num.value)) }
}
impl From<Sp<Var>> for Sp<Expr> {
    fn from(var: Sp<Var>) -> Sp<Expr> { sp!(var.span => Expr::Var(var)) }
}
impl From<Sp<BString>> for Sp<Expr> {
    fn from(string: Sp<BString>) -> Sp<Expr> { sp!(string.span => Expr::from(string.value)) }
}

// =============================================================================

string_enum! {
    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum VarDeclKeyword {
        #[str = "int"] Int,
        #[str = "float"] Float,
        #[str = "var"] Var,
    }
}

impl VarDeclKeyword {
    pub fn ty(self) -> Option<type_system::ScalarType> {
        match self {
            VarDeclKeyword::Int => Some(type_system::ScalarType::Int),
            VarDeclKeyword::Float => Some(type_system::ScalarType::Float),
            VarDeclKeyword::Var => None,
        }
    }
}

/// The hinted type of a variable at a usage site, which can differ from its inherent type.
///
/// E.g. a variable's type may be hinted with the use of `$` or `%` prefixes.
/// (or it might not be hinted, meaning its type must be determined through other means)
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VarReadType {
    Int,
    Float,
}

impl VarReadType {
    pub fn from_ty(x: type_system::ScalarType) -> Option<VarReadType> {
        match x {
            type_system::ScalarType::Int => Some(VarReadType::Int),
            type_system::ScalarType::Float => Some(VarReadType::Float),
            type_system::ScalarType::String => None,
        }
    }

    pub fn sigil(self) -> &'static str {
        match self {
            VarReadType::Int => "$",
            VarReadType::Float => "%",
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

// =============================================================================

impl std::fmt::Display for CallableName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CallableName::Normal { ident } => fmt::Display::fmt(ident, f),
            CallableName::Ins { opcode } => write!(f, "ins_{}", opcode),
        }
    }
}

// =============================================================================

/// Trait for using [`Visit`] and [`VisitMut`] in a generic context.
///
/// The methods on this trait very simply just statically dispatch to the appropriate method
/// on those other traits.  E.g. if the node is an [`Item`] then [`Visitable::visit_with`] will
/// call the [`Visit::visit_item`] method, and etc.
///
/// The public API for most passes in [`crate::passes`] is a function with a bound on this trait,
/// because this is a lot nicer than directly exposing the visitors.  In particular, it saves the
/// caller from needing to import traits, or from having to worry about whether the visitor has a
/// method that they need to call in order to find out if an error occurred.
///
/// Note: For [`Block`], this specifically dispatches to [`Visit::visit_root_block`].
pub trait Visitable {
    /// Calls the method of [`Visit`] appropriate to this type, e.g. [`Visit::visit_expr`]
    /// if `Self` is an `Expr`.
    fn visit_with<V: Visit>(&self, f: &mut V);

    /// Calls the method of [`VisitMut`] appropriate to this type, e.g. [`VisitMut::visit_expr`]
    /// if `Self` is an `Expr`.
    fn visit_mut_with<V: VisitMut>(&mut self, f: &mut V);
}

macro_rules! generate_visitor_stuff {
    ($Visit:ident, Visitable::$visit:ident $(,$mut:tt)?) => {
        /// Recursive AST traversal trait.
        pub trait $Visit {
            fn visit_script(&mut self, e: & $($mut)? Script) { walk_script(self, e) }
            fn visit_item(&mut self, e: & $($mut)? Sp<Item>) { walk_item(self, e) }
            /// This is called only on the outermost blocks of each function.
            ///
            /// Overriding this is useful for things that need to know the full contents of a function
            /// (e.g. things that deal with labels). It also lets the visitor know if it is about to
            /// enter a nested function (if those ever become a thing).
            ///
            /// The implementation of [`Visitable`] for [`Block`] calls this instead of [`Self::visit_block`].
            /// The reasoning behind this is that any visitor which does override [`Self::visit_root_block`] is
            /// likely to only ever be used on blocks that do in fact represent a full function body.
            ///
            /// The default definition simply delegates to [`Self::visit_block`].
            fn visit_root_block(&mut self, e: & $($mut)? Block) { self.visit_block(e) }
            fn visit_block(&mut self, e: & $($mut)? Block) { walk_block(self, e) }
            fn visit_cond(&mut self, e: & $($mut)? Sp<Cond>) { walk_cond(self, e) }
            fn visit_stmt(&mut self, e: & $($mut)? Sp<Stmt>) { walk_stmt(self, e) }
            fn visit_goto(&mut self, e: & $($mut)? StmtGoto) { walk_goto(self, e) }
            fn visit_expr(&mut self, e: & $($mut)? Sp<Expr>) { walk_expr(self, e) }
            fn visit_var(&mut self, e: & $($mut)? Sp<Var>) { walk_var(self, e) }
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
                    code, inline: _, keyword: _, ident: _, params: _,
                } => {
                    if let Some(code) = code {
                        v.visit_root_block(code);
                    }
                },
                Item::AnmScript { keyword: _, number: _, ident: _, code } => {
                    v.visit_root_block(code);
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
            match & $($mut)? x.body {
                StmtBody::Jump(goto) => {
                    v.visit_goto(goto);
                },
                StmtBody::Return { value, keyword: _ } => {
                    if let Some(value) = value {
                        v.visit_expr(value);
                    }
                },
                StmtBody::Loop { block, keyword: _ } => v.visit_block(block),
                StmtBody::CondJump { cond, jump, keyword: _ } => {
                    v.visit_cond(cond);
                    v.visit_goto(jump);
                },
                StmtBody::CondChain(chain) => {
                    let StmtCondChain { cond_blocks, else_block } = chain;
                    for sp_pat!(CondBlock { cond, block, keyword: _ }) in cond_blocks {
                        v.visit_cond(cond);
                        v.visit_block(block);
                    }
                    if let Some(block) = else_block {
                        v.visit_block(block);
                    }
                },
                StmtBody::While { do_keyword: Some(_), while_keyword: _, cond, block } => {
                    v.visit_cond(cond);
                    v.visit_block(block);
                },
                StmtBody::While { do_keyword: None, while_keyword: _, cond, block } => {
                    v.visit_block(block);
                    v.visit_cond(cond);
                },
                StmtBody::Times { clobber, count, block, keyword: _ } => {
                    if let Some(clobber) = clobber {
                        v.visit_var(clobber);
                    }
                    v.visit_expr(count);
                    v.visit_block(block);
                },
                StmtBody::Expr(e) => {
                    v.visit_expr(e);
                },
                StmtBody::Assignment { var, op: _, value } => {
                    v.visit_var(var);
                    v.visit_expr(value);
                },
                StmtBody::Declaration { keyword: _, vars } => {
                    for sp_pat![(var, value)] in vars {
                        v.visit_var(var);
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
                StmtBody::Label(_) => {},
                StmtBody::InterruptLabel(_) => {},
                StmtBody::ScopeEnd(_) => {},
                StmtBody::NoInstruction => {},
            }
        }

        pub fn walk_goto<V>(_: &mut V, _: & $($mut)? StmtGoto)
        where V: ?Sized + $Visit,
        {
        }

        fn walk_cond<V>(v: &mut V, e: & $($mut)? Sp<Cond>)
        where V: ?Sized + $Visit,
        {
            match & $($mut)? e.value {
                Cond::PreDecrement(var) => v.visit_var(var),
                Cond::Expr(e) => v.visit_expr(e),
            }
        }

        pub fn walk_expr<V>(v: &mut V, e: & $($mut)? Sp<Expr>)
        where V: ?Sized + $Visit,
        {
            match & $($mut)? e.value {
                Expr::Ternary { cond, left, right, question: _, colon: _ } => {
                    v.visit_expr(cond);
                    v.visit_expr(left);
                    v.visit_expr(right);
                },
                Expr::Binop(a, _op, b) => {
                    v.visit_expr(a);
                    v.visit_expr(b);
                },
                Expr::Call { name: _, args } => {
                    for arg in args {
                        v.visit_expr(arg);
                    }
                },
                Expr::Unop(_op, x) => v.visit_expr(x),
                Expr::LitInt { value: _, hex: _ } => {},
                Expr::LitFloat { value: _ } => {},
                Expr::LitString(_s) => {},
                Expr::Var(var) => v.visit_var(var),
            }
        }

        pub fn walk_var<V>(_v: &mut V, x: & $($mut)? Sp<Var>)
        where V: ?Sized + $Visit,
        {
            match & $($mut)? x.value {
                Var::Named { ty_sigil: _, ident: _ } => {},
                Var::Reg { ty_sigil: _, reg: _ } => {},
            }
        }
    };
}

macro_rules! impl_visitable {
    ($Node:ty, $visit_node:ident) => {
        impl Visitable for $Node {
            fn visit_with<V: Visit>(&self, v: &mut V) { <V as Visit>::$visit_node(v, self) }
            fn visit_mut_with<V: VisitMut>(&mut self, v: &mut V) { <V as VisitMut>::$visit_node(v, self) }
        }
    }
}
impl_visitable!(Script, visit_script);
impl_visitable!(Sp<Item>, visit_item);
impl_visitable!(Block, visit_root_block);
impl_visitable!(Sp<Cond>, visit_cond);
impl_visitable!(Sp<Stmt>, visit_stmt);
impl_visitable!(Sp<Expr>, visit_expr);
impl_visitable!(StmtGoto, visit_goto);
impl_visitable!(Sp<Var>, visit_var);

mod mut_ {
    use super::*;
    generate_visitor_stuff!(VisitMut, Visitable::visit_mut, mut);
}
pub use self::mut_::{
    VisitMut,
    walk_script as walk_script_mut,
    walk_item as walk_item_mut,
    walk_block as walk_block_mut,
    walk_stmt as walk_stmt_mut,
    walk_goto as walk_goto_mut,
    walk_expr as walk_expr_mut,
};
mod ref_ {
    use super::*;
    generate_visitor_stuff!(Visit, Visitable::visit);
}
pub use self::ref_::{
    Visit, walk_script, walk_item, walk_block, walk_stmt, walk_goto, walk_expr,
};

