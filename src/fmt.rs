use bstr::{BStr, BString, ByteSlice, ByteVec};
use std::io::{self, Write};
use crate::ast;

// We can't impl Display because that's UTF-8 based.
pub trait Format {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()>;
}

// We can't do stuff like `write!("{} {}({})", x, y, z)` so here's the next best thing.
macro_rules! fmt {
    ($out:expr, $($e:expr),+$(,)?) => {
        (|| -> std::io::Result<()> {
            $( Format::fmt(&$e, $out)?; )+
            Ok(())
        })()
    }
}

//==============================================================================
// Base impls

impl<T: Format + ?Sized> Format for &T {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        Format::fmt(*self, out)
    }
}
impl<T: Format + ?Sized> Format for Box<T> {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        Format::fmt(&**self, out)
    }
}
impl Format for BString {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        out.write_all(self.as_ref())
    }
}
impl Format for BStr {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        out.write_all(self.as_ref())
    }
}
impl Format for str {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        out.write_all(self.as_ref())
    }
}

//==============================================================================
// Helpers

pub struct Separated<'a, T>(&'a [T], &'a str);
impl<'a, T: Format> Format for Separated<'a, T> {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        let Separated(seq, sep) = *self;

        let mut iter = seq.iter();
        if let Some(first) = iter.next() {
            fmt!(out, first)?;
        }
        for x in iter {
            fmt!(out, sep, x)?;
        }
        Ok(())
    }
}

pub struct Pair<A, B>(A, B);
impl<A: Format, B: Format> Format for Pair<A, B> {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        fmt!(out, self.0, " ", self.1)
    }
}

//==============================================================================
// Items

impl Format for ast::Script {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        let ast::Script { items } = self;
        fmt!(out, Separated(items, ""))
    }
}

impl Format for ast::Item {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        match self {
            ast::Item::Func { inline, keyword, name, params, code, } => {
                let inline_keyword = if *inline { "inline " } else { "" };
                let params = params.iter().map(|(ty, param)| Pair(ty, param)).collect::<Vec<_>>();

                fmt!(out, inline_keyword, keyword, " ")?;
                fmt!(out, name, "(", Separated(&params, ", "), ")")?;
                match code {
                    None => fmt!(out, ";"),
                    Some(code) => fmt!(out, " ", code),
                }
            },
            ast::Item::FileList { keyword, files } => {
                fmt!(out, keyword, "{ ")?;
                for file in files {
                    fmt!(out, file, "; ")?;
                }
                fmt!(out, "}")
            },
        }
    }
}

impl Format for ast::FuncKeyword {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        match *self {
            ast::FuncKeyword::Type(ty) => fmt!(out, ty),
            ast::FuncKeyword::Sub => fmt!(out, "sub"),
            ast::FuncKeyword::Timeline => fmt!(out, "timeline"),
            ast::FuncKeyword::Script => fmt!(out, "script"),
        }
    }
}

impl Format for ast::FileListKeyword {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        fmt!(out, match self {
            ast::FileListKeyword::Anim => "anim",
            ast::FileListKeyword::Ecli => "ecli",
        })
    }
}

// =============================================================================
// Statements

impl Format for ast::Stmt {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        let ast::Stmt { labels, body } = self;
        for label in labels {
            fmt!(out, label, " ")?;
        }
        fmt!(out, body)
    }
}

impl Format for ast::StmtLabel {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        match *self {
            ast::StmtLabel::AddTime(dt) => fmt!(out, "+", dt, ":"),
            ast::StmtLabel::SetTime(t) => fmt!(out, t, ":"),
            ast::StmtLabel::Label(ref ident) => fmt!(out, ident, ":"),
            ast::StmtLabel::Difficulty { temporary, ref flags } => {
                let colon = if temporary { ":" } else { "" };
                fmt!(out, "!", flags.as_bstr(), colon)
            },
        }
    }
}

impl Format for ast::StmtBody {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        match self {
            ast::StmtBody::Jump(jump) => fmt!(out, jump, ";"),
            ast::StmtBody::Return { value } => {
                fmt!(out, "return")?;
                if let Some(value) = value {
                    fmt!(out, " ", value)?;
                }
                fmt!(out, ";")
            },
            ast::StmtBody::CondJump { kind, cond, jump } => {
                fmt!(out, kind, " (", cond, ") ", jump, ";")
            },
            ast::StmtBody::CondChain(chain) => fmt!(out, chain),
            ast::StmtBody::While { is_do_while: true, cond, block } => {
                fmt!(out, "do ", block, " while (", cond, ");")
            },
            ast::StmtBody::While { is_do_while: false, cond, block } => {
                fmt!(out, "while (", cond, ") ", block)
            },
            ast::StmtBody::Times { count, block } => {
                fmt!(out, "times(", count, ") ", block)
            },
            ast::StmtBody::Expr(e) => fmt!(out, e, ";"),
            ast::StmtBody::Assignment { var, op, value } => {
                fmt!(out, var, " ", op, " ", value, ";")
            },
            ast::StmtBody::Declaration { ty, vars } => {
                fmt!(out, ty, " ")?;

                let mut first = true;
                for (ident, expr) in vars {
                    if !first {
                        fmt!(out, ",")?;
                    }
                    first = false;

                    fmt!(out, ident)?;
                    if let Some(expr) = expr {
                        fmt!(out, " = ", expr)?;
                    }
                }
                fmt!(out, ";")
            },
            ast::StmtBody::CallSub { at_symbol, async_, func, args } => {
                fmt!(out, if *at_symbol { "@" } else { "" })?;
                fmt!(out, func, "(", Separated(args, ", "), ")")?;
                if let Some(async_) = async_ {
                    fmt!(out, " ", async_)?;
                }
                fmt!(out, ";")
            }
        }
    }
}

impl Format for ast::StmtGoto {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        let ast::StmtGoto { destination, time } = self;
        fmt!(out, "goto ", destination)?;
        if let Some(time) = time {
            fmt!(out, "@ ", time)?;
        }
        Ok(())
    }
}

impl Format for ast::StmtCondChain {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        let ast::StmtCondChain { cond_blocks, else_block } = self;
        let mut iter = cond_blocks.iter();

        fmt!(out, iter.next().expect("no if's in if-chain?!"))?;
        for cond_block in iter {
            fmt!(out, " else ", cond_block)?; // else ifs
        }
        if let Some(else_block) = else_block {
            fmt!(out, " else ", else_block)?;
        }
        Ok(())
    }
}

impl Format for ast::CondBlock {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        let ast::CondBlock { kind, cond, block } = self;
        fmt!(out, kind, " (", cond, ") ", block)
    }
}

impl Format for ast::CallAsyncKind {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        match *self {
            ast::CallAsyncKind::CallAsync => fmt!(out, "async"),
            ast::CallAsyncKind::CallAsyncId(ref e) => fmt!(out, "async ", e),
        }
    }
}

impl Format for ast::CondKind {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        fmt!(out, match self {
            ast::CondKind::If => "if",
            ast::CondKind::Unless => "unless",
        })
    }
}

impl Format for ast::AssignOpKind {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        fmt!(out, match self {
            ast::AssignOpKind::Assign => "=",
            ast::AssignOpKind::Add => "+=",
            ast::AssignOpKind::Sub => "-=",
            ast::AssignOpKind::Mul => "*=",
            ast::AssignOpKind::Div => "/=",
            ast::AssignOpKind::Rem => "%=",
            ast::AssignOpKind::BitOr => "|=",
            ast::AssignOpKind::BitXor => "^=",
            ast::AssignOpKind::BitAnd => "&=",
        })
    }
}

impl Format for ast::Block {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        let ast::Block(statements) = self;
        fmt!(out, "{ ", Separated(statements, ""), " }")
    }
}

// =============================================================================
// Expressions

impl Format for ast::Expr {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        match self {
            ast::Expr::Ternary { cond, left, right } => {
                fmt!(out, "(", cond, " ? ", left, " : ", right, ")")
            },
            ast::Expr::Binop(a, op, b) => fmt!(out, "(", a, " ", op, " ", b, ")"),
            ast::Expr::Call { func, args } => {
                fmt!(out, func, "(", Separated(args, ", "), ")")
            },
            ast::Expr::Decrement { var } => {
                fmt!(out, var, "--")
            },
            ast::Expr::Unop(op, x) => fmt!(out, "(", op, x, ")"),
            ast::Expr::LitInt(x) => fmt!(out, x),
            ast::Expr::LitFloat(x) => fmt!(out, x),
            ast::Expr::LitString(x) => fmt!(out, x),
            ast::Expr::Var(x) => fmt!(out, x),
        }
    }
}

impl Format for ast::Var {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        match self {
            ast::Var::Named { ty, ident } => match ty {
                None => fmt!(out, ident),
                Some(ast::TypeKind::Int) => fmt!(out, "$", ident),
                Some(ast::TypeKind::Float) => fmt!(out, "%", ident),
                Some(ast::TypeKind::Void) => panic!("unexpected void variable"),
            },
            ast::Var::Unnamed { ty, number } => match ty {
                ast::TypeKind::Int => fmt!(out, "[", number, "]"),
                ast::TypeKind::Float => fmt!(out, "[", *number as f32, "]"),
                ast::TypeKind::Void => panic!("unexpected void variable"),
            },
        }
    }
}

impl Format for ast::VarTypeKeyword {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        fmt!(out, match self {
            ast::VarTypeKeyword::Int => "int",
            ast::VarTypeKeyword::Float => "float",
            ast::VarTypeKeyword::Var => "var",
        })
    }
}

impl Format for ast::BinopKind {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        fmt!(out, match self {
            ast::BinopKind::Add => "+",
            ast::BinopKind::Sub => "-",
            ast::BinopKind::Mul => "*",
            ast::BinopKind::Div => "/",
            ast::BinopKind::Rem => "%",
            ast::BinopKind::Eq => "==",
            ast::BinopKind::Ne => "!=",
            ast::BinopKind::Lt => "<",
            ast::BinopKind::Le => "<=",
            ast::BinopKind::Gt => ">",
            ast::BinopKind::Ge => ">=",
            ast::BinopKind::BitOr => "|",
            ast::BinopKind::BitXor => "^",
            ast::BinopKind::BitAnd => "&",
            ast::BinopKind::LogicOr => "||",
            ast::BinopKind::LogicAnd => "&&",
        })
    }
}

impl Format for ast::UnopKind {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        fmt!(out, match self {
            ast::UnopKind::Not => "!",
            ast::UnopKind::Neg => "-",
        })
    }
}

// =============================================================================
// Basic tokens

impl Format for ast::TypeKind {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        fmt!(out, match self {
            ast::TypeKind::Int => "int",
            ast::TypeKind::Float => "float",
            ast::TypeKind::Void => "void",
        })
    }
}

impl Format for ast::Ident {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        let ast::Ident { ident } = self;
        fmt!(out, &ident)
    }
}

impl Format for ast::LitString {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        let mut tmp = BString::from(Vec::with_capacity(2*self.string.len()+1));
        for byte in self.string.bytes() {
            match byte {
                b'\0' => tmp.push_str(br#"\0"#),
                b'\"' => tmp.push_str(br#"\""#),
                b'\\' => tmp.push_str(br#"\\"#),
                b'\n' => tmp.push_str(br#"\n"#),
                b'\r' => tmp.push_str(br#"\r"#),
                b => tmp.push(b),
            }
        }
        fmt!(out, "\"", tmp, "\"")
    }
}

impl Format for i32 {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        write!(out, "{}", self)
    }
}

impl Format for f32 {
    fn fmt<W: Write>(&self, out: &mut W) -> io::Result<()> {
        let mut s = format!("{}", self);
        if !s.contains('.') {
            s.push_str(".0");
        }
        fmt!(out, s.as_bytes().as_bstr())
    }
}
