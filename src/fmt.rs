use bstr::{BStr, BString, ByteSlice, ByteVec};
use thiserror::Error;
use std::io::{self, Write};
use crate::ast;
use crate::meta::Meta;
use crate::ident::Ident;

// We can't impl Display because that's UTF-8 based.
/// Trait for displaying Touhou script code.
pub trait Format {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result;
}

//==============================================================================

pub type Result<T = ()> = std::result::Result<T, Error>;

#[derive(Debug, Error)]
#[error(transparent)]
pub struct Error(ErrorKind);

#[derive(Debug, Error)]
enum ErrorKind {
    #[error("{}", .0)]
    Io(io::Error),

    // This variant is used to implement backtracking for things with conditional block formatting.
    // If the user ever sees this error message, it's because the error must have somehow been
    // unwrapped instead of backtracking.
    #[error("Failed to backtrack for conditional block formatting. This is a bug!")]
    LineBreakRequired,
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self { Error(ErrorKind::Io(e)) }
}

//==============================================================================

pub use formatter::{Formatter};
mod formatter {
    use super::*;

    const INDENT: isize = 4;

    /// Type that is primarily responsible for managing indentation and optional block formatting.
    pub struct Formatter<W: io::Write> {
        // This is an Option only so that `into_inner` can remove it.
        writer: Option<W>,
        pending_data: bool,
        // Block- and line- formatting state
        line_buffer: Vec<u8>,
        target_width: usize,
        indent: usize,
        is_label: bool,
        inline_depth: u32,
        /// Contains state that is not directly managed by Formatter itself, but rather
        /// by various [`Format`] impls.
        pub(super) state: State,
    }

    /// If a partially-written line has not yet been committed through a call to
    /// [`Formatter::next_line`], it will be written on drop, and errors will be ignored.
    impl<W: io::Write> Drop for Formatter<W> {
        fn drop(&mut self) {
            let _ = self._flush_incomplete_line();
        }
    }

    impl<W: io::Write> Formatter<W> {
        /// Construct a new [`Formatter`] for writing at an initial indent level of 0.
        pub fn new(writer: W) -> Self {
            Self {
                writer: Some(writer),
                target_width: 99,
                indent: 0,
                is_label: false,
                inline_depth: 0,
                pending_data: false,
                // The initial level here is used when writing a Stmt as toplevel.
                // When parsing items, we mostly use a second level that gets pushed/popped with functions.
                line_buffer: vec![],
                state: State::new(),
            }
        }

        // FIXME: Replace with an `Options` builder-pattern struct so that it
        //        can't be used mid-formatting.
        pub fn with_max_columns(mut self, width: usize) -> Self {
            // FIXME: The -1 is to work around a known bug where, if something is in
            //        block mode and one of its items exactly exactly reaches target_width
            //        in inline mode, then the comma after the item will surpass the width
            //        without triggering backtracking on the item.
            self.target_width = width - 1; self
        }

        /// Recover the wrapped `io::Write` object.
        ///
        /// **Important:** If the last line has not yet been written by calling
        /// [`Formatter::next_line`], it will attempt to write this data now.
        /// This can fail.
        pub fn into_inner(mut self) -> Result<W> {
            self._flush_incomplete_line()?;
            Ok(self.writer.take().unwrap())
        }

        fn _flush_incomplete_line(&mut self) -> Result {
            if self.pending_data {
                self.writer.as_mut().unwrap().write_all(&self.line_buffer)?;
                self.pending_data = false;
            }
            Ok(())
        }
    }

    impl<W: io::Write> Formatter<W> {
        /// Convenience method that calls [`Format::fmt`].
        pub fn fmt<T: Format>(&mut self, x: T) -> Result { x.fmt(self) }

        /// Write a line without any indent, like a label.
        ///
        /// Only works at the beginning of the line (otherwise it just writes normally,
        /// followed by a space).  When it does take effect, a newline is automatically
        /// inserted after writing the argument.
        pub fn fmt_label<T: Format>(&mut self, label: T) -> Result {
            assert!(!self.is_label, "Tried to write nested labels. This is a bug!");
            if self.pending_data {
                // write label inline
                self.fmt((label, " "))?;
            } else {
                // write label flush with margin
                self.is_label = true; // note: flag is cleared by `next_line()`
                self.line_buffer.clear(); // strip indent
                self.fmt(label)?;
                assert!(self.is_label, "Detected line break in label. This is a bug!");
                self.next_line()?;
            }
            Ok(())
        }

        /// Write a comma-separated list.
        ///
        /// Switches to block style (with trailing comma) on long lines.
        pub fn fmt_comma_separated<T: Format>(
            &mut self,
            open: &'static str,
            close: &'static str,
            items: impl IntoIterator<Item=T> + Clone,
        ) -> Result {
            self.try_inline(|me| {
                // Reasons the inline formatting may fail:
                // * A line length check may fail here.
                // * One of the list items may unconditionally produce a newline
                me.fmt(open)?;
                let mut first = true;
                for x in items.clone() {
                    if !first { me.fmt(", ")?; }
                    first = false;
                    me.fmt(x)?;
                    me.backtrack_inline_if_long()?;
                }
                me.fmt(close)?;
                me.backtrack_inline_if_long()
            }, |me| {
                // Block formatting
                me.fmt(open)?;
                me.next_line()?;
                me.indent()?;
                for x in items.clone() {
                    me.fmt((x, ","))?;
                    me.next_line()?;
                }
                me.dedent()?;
                me.fmt(close)
            })
        }

        /// Helper which writes items from an iterator, invoking the separator closure between
        /// each pair of items. (but NOT after the final item)
        pub fn fmt_separated<T: Format, B>(
            &mut self,
            items: impl IntoIterator<Item=T> + Clone,
            mut sep: impl FnMut(&mut Self) -> Result<B>,
        ) -> Result {
            let mut first = true;
            for x in items {
                if !first { sep(self)?; }
                first = false;
                self.fmt(x)?;
            }
            Ok(())
        }

        /// Increases the indent level.
        ///
        /// Panics if not at the beginning of a line.
        pub fn indent(&mut self) -> Result { self._add_indent(INDENT) }

        /// Decreases the indent level.
        ///
        /// Panics if not at the beginning of a line, or if an attempt is made to dedent beyond the
        /// left margin.
        pub fn dedent(&mut self) -> Result { self._add_indent(-INDENT) }

        /// Output a line and start a new one at the same indent level.  Causes backtracking
        /// if currently in inline mode.
        pub fn next_line(&mut self) -> Result {
            self.backtrack_inline()?;
            self.is_label = false;
            self.pending_data = false;
            self.line_buffer.push(b'\n');
            self.writer.as_mut().unwrap().write_all(&self.line_buffer)?;
            self.line_buffer.clear();
            self.line_buffer.resize(self.indent, b' ');
            Ok(())
        }

        // ---------------------

        /// Appends a string to the current (not yet written) line.
        pub(super) fn append_to_line(&mut self, bytes: &[u8]) -> Result {
            // Catch accidental use of "\n" in output strings where next_line() should be used.
            assert!(!bytes.contains(&b'\n'), "Tried to append newline to line. This is a bug!");
            self.pending_data = true;
            self.line_buffer.extend_from_slice(bytes);
            Ok(())
        }

        /// Append to the current (not yet written) line using [`std::fmt::Display`].
        pub(super) fn append_display_to_line(&mut self, x: impl std::fmt::Display) -> Result {
            self.pending_data = true;
            write!(&mut self.line_buffer, "{}", x)?;
            Ok(())
        }

        /// If we're in inline mode, backtrack to the outermost [`Formatter::try_inline`].
        fn backtrack_inline(&mut self) -> Result {
            if self.inline_depth > 0 {
                return Err(Error(ErrorKind::LineBreakRequired));
            }
            Ok(())
        }

        /// If we're in inline mode and the line is too long, backtrack to the
        /// outermost [`Formatter::try_inline`].
        fn backtrack_inline_if_long(&mut self) -> Result {
            if self.inline_depth > 0 && self.line_buffer.len() > self.target_width {
                return Err(Error(ErrorKind::LineBreakRequired));
            }
            Ok(())
        }

        /// Attempt to write something inline, else write block style.
        fn try_inline<B>(
            &mut self,
            mut inline_cb: impl FnMut(&mut Self) -> Result<B>,
            mut block_cb: impl FnMut(&mut Self) -> Result<B>,
        ) -> Result<B> {
            let backtrack_pos = match self.inline_depth {
                0 => Some(self.line_buffer.len()),
                _ => None, // don't backtrack if nested in another inline_cb
            };
            self.inline_depth += 1;
            let result = inline_cb(self);
            self.inline_depth -= 1;
            match (result, backtrack_pos) {
                // If we fail to write inline and this is the outermost `try_inline`,
                // backtrack and try writing not inline.
                (Err(Error(ErrorKind::LineBreakRequired)), Some(backtrack_pos)) => {
                    assert_eq!(self.inline_depth, 0, "Block cb in inline mode. This is a bug!");
                    self.line_buffer.truncate(backtrack_pos);
                    block_cb(self)
                },
                (result, _) => result,
            }
        }

        fn _add_indent(&mut self, delta: isize) -> Result {
            let new_indent = self.indent as isize + delta;
            assert!(!self.pending_data, "Attempted to change indent mid-line. This is a bug!");
            assert!(!self.is_label, "Attempted to change indent in a label. This is a bug!");
            assert!(new_indent >= 0, "Attempted to dedent past 0. This is a bug!");

            self.indent = new_indent as usize;
            self.line_buffer.resize(self.indent, b' ');
            Ok(())
        }
    }
}

//==============================================================================

// Base impls: To write arbitrary text, use a string type.
impl Format for BString {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        out.append_to_line(self.as_ref())
    }
}
impl Format for BStr {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        out.append_to_line(self.as_ref())
    }
}
impl Format for str {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        out.append_to_line(self.as_ref())
    }
}

// Use `format_args!` to delegate to a `std::fmt` trait.
impl Format for std::fmt::Arguments<'_> {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        out.append_display_to_line(self)
    }
}

// Forwarded impls
impl<T: Format + ?Sized> Format for &T {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        Format::fmt(&**self, out)
    }
}
impl<T: Format + ?Sized> Format for Box<T> {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        Format::fmt(&**self, out)
    }
}

//==============================================================================

/// Additional state used during formatting which is not directly related to indentation and
/// block formatting.
#[derive(Debug, Clone)]
struct State {
    /// When we are printing instructions, tracks the last time label so that we can produce a
    /// nice listing with relative labels.
    ///
    /// A stack is used *as if* we supported nested function definitions.  In practice, the level at
    /// index 0 gets used exclusively when writing `Stmt`s, and a level at index 1 gets used when
    /// writing `Item`s.
    time_stack: Vec<i32>,
}

impl State {
    fn new() -> Self { State {
        time_stack: vec![0],
    }}
}

//==============================================================================
// Helpers

// Tuples concatenate their arguments.
//
// The most important use case is to facilitate use of helper functions that take
// `impl IntoIterator<T> where T: Format`.  As a small bonus, it also helps
// reduce verbosity in plain `fmt` calls.
macro_rules! impl_tuple_format {
    ($($a:ident:$A:ident),*) => {
        impl<$($A: Format),*> Format for ( $($A),* ) {
            fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
                let ( $($a),* ) = self;
                $( Format::fmt($a, out)?; )*
                Ok(())
            }
        }
    }
}

impl_tuple_format!(a:A, b:B);
impl_tuple_format!(a:A, b:B, c:C);
impl_tuple_format!(a:A, b:B, c:C, d:D);
impl_tuple_format!(a:A, b:B, c:C, d:D, e:E);
impl_tuple_format!(a:A, b:B, c:C, d:D, e:E, f:F);
impl_tuple_format!(a:A, b:B, c:C, d:D, e:E, f:F, g:G);
impl_tuple_format!(a:A, b:B, c:C, d:D, e:E, f:F, g:G, h:H);

//==============================================================================
// Items

impl Format for ast::Script {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        let ast::Script { items } = self;
        out.fmt_separated(items, |out| {
            out.next_line()?;
            out.next_line()
        })
    }
}

impl Format for Meta {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        match self {
            Meta::Int(x) => out.fmt(x),
            Meta::Float(x) => out.fmt(x),
            Meta::String(x) => out.fmt(ast::LitString { string: x }),
            Meta::Object(map) => out.fmt_comma_separated("{", "}", map.iter().map(|(k, v)| (k, ": ", v))),
            Meta::Array(xs) => out.fmt_comma_separated("[", "]", xs),
        }
    }
}

impl Format for ast::Item {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result<()> {
        match self {
            ast::Item::Func { inline, keyword, name, params, code, } => {
                let inline_keyword = if *inline { "inline " } else { "" };

                out.fmt((inline_keyword, keyword, " ", name))?;
                out.fmt_comma_separated("(", ")", params.iter().map(|(ty, param)| (ty, " ", param)))?;

                out.state.time_stack.push(0);
                match code {
                    None => out.fmt(";")?,
                    Some(code) => out.fmt((" ", code))?,
                }
                out.state.time_stack.pop();
                Ok(())
            },
            ast::Item::AnmScript { number, name, code } => {
                out.state.time_stack.push(0);
                out.fmt( "script ")?;
                if let Some(number) = number {
                    out.fmt((number, " "))?;
                }
                out.fmt((name, " ", code))?;
                out.state.time_stack.pop();
                Ok(())
            },
            ast::Item::Meta { keyword, name, meta } => {
                out.fmt((keyword, " "))?;
                if let Some(name) = name {
                    out.fmt((name, " "))?;
                }
                out.fmt(meta)
            },
            ast::Item::FileList { keyword, files } => {
                out.fmt((keyword, "{ "))?;
                for file in files {
                    out.fmt((file, "; "))?;
                }
                out.fmt(" }")
            },
        }
    }
}

impl Format for ast::FuncKeyword {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        match *self {
            ast::FuncKeyword::Type(ty) => out.fmt( ty),
            ast::FuncKeyword::Sub => out.fmt( "sub"),
            ast::FuncKeyword::Timeline => out.fmt( "timeline"),
        }
    }
}

impl Format for ast::FileListKeyword {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        out.fmt( match self {
            ast::FileListKeyword::Anim => "anim",
            ast::FileListKeyword::Ecli => "ecli",
        })
    }
}

impl Format for ast::MetaKeyword {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        out.fmt( match self {
            ast::MetaKeyword::Entry => "entry",
            ast::MetaKeyword::Meta => "meta",
        })
    }
}

// =============================================================================
// Statements

impl Format for ast::Stmt {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        let ast::Stmt { time, labels, body } = self;

        let top_time = out.state.time_stack.last_mut().expect("empty time stack?! (bug!)");
        let prev_time = *top_time;
        *top_time = *time;

        // Nice time label display
        if *time != prev_time {
            if prev_time < 0 {
                out.fmt_label("0:")?;
                if *time > 0 {
                    out.fmt_label(("+", *time, ": // ", *time))?;
                }
            } else if *time < prev_time {
                out.fmt_label((*time, ":"))?;
            } else if prev_time < *time {
                out.fmt_label(("+", *time - prev_time, ": // ", *time))?;
            }
        };
        for label in labels {
            out.fmt(label)?;
        }
        out.fmt(body)
    }
}

impl Format for ast::StmtLabel {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        match *self {
            ast::StmtLabel::Label(ref ident) => out.fmt_label((ident, ":")),
            ast::StmtLabel::Difficulty { temporary, ref flags } => {
                let colon = if temporary { ":" } else { "" };
                out.fmt_label(("!", flags, colon))
            },
        }
    }
}

impl Format for ast::StmtBody {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        match self {
            ast::StmtBody::Jump(jump) => out.fmt((jump, ";")),
            ast::StmtBody::Return { value } => {
                out.fmt( "return")?;
                if let Some(value) = value {
                    out.fmt((" ", value))?;
                }
                out.fmt(";")
            },
            ast::StmtBody::CondJump { kind, cond, jump } => {
                out.fmt((kind, " (", cond, ") ", jump, ";"))
            },
            ast::StmtBody::CondChain(chain) => out.fmt( chain),
            ast::StmtBody::While { is_do_while: true, cond, block } => {
                out.fmt(("do ", block, " while (", cond, ");"))
            },
            ast::StmtBody::While { is_do_while: false, cond, block } => {
                out.fmt(("while (", cond, ") ", block))
            },
            ast::StmtBody::Times { count, block } => {
                out.fmt(("times(", count, ") ", block))
            },
            ast::StmtBody::Expr(e) => out.fmt((e, ";")),
            ast::StmtBody::Assignment { var, op, value } => {
                out.fmt((var, " ", op, " ", value, ";"))
            },
            ast::StmtBody::Declaration { ty, vars } => {
                out.fmt((ty, " "))?;

                let mut first = true;
                for (ident, expr) in vars {
                    if !first {
                        out.fmt(",")?;
                    }
                    first = false;

                    out.fmt( ident)?;
                    if let Some(expr) = expr {
                        out.fmt((" = ", expr))?;
                    }
                }
                out.fmt(";")
            },
            ast::StmtBody::CallSub { at_symbol, async_, func, args } => {
                out.fmt(if *at_symbol { "@" } else { "" })?;
                out.fmt(func)?;
                out.fmt_comma_separated("(", ")", args)?;
                if let Some(async_) = async_ {
                    out.fmt((" ", async_))?;
                }
                out.fmt(";")
            }
        }
    }
}

impl Format for ast::StmtGoto {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        let ast::StmtGoto { destination, time } = self;
        out.fmt(("goto", destination))?;
        if let Some(time) = time {
            out.fmt(("@", time))?;
        }
        Ok(())
    }
}

impl Format for ast::StmtCondChain {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        let ast::StmtCondChain { cond_blocks, else_block } = self;
        let mut iter = cond_blocks.iter();

        out.fmt(iter.next().expect("no if's in if-chain?!"))?;
        for cond_block in iter {
            out.fmt((" else ", cond_block))?; // else ifs
        }
        if let Some(else_block) = else_block {
            out.fmt((" else ", else_block))?;
        }
        Ok(())
    }
}

impl Format for ast::CondBlock {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        let ast::CondBlock { kind, cond, block } = self;
        out.fmt((kind, " (", cond, ") ", block))
    }
}

impl Format for ast::CallAsyncKind {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        match *self {
            ast::CallAsyncKind::CallAsync => out.fmt("async"),
            ast::CallAsyncKind::CallAsyncId(ref e) => out.fmt(("async ", e)),
        }
    }
}

impl Format for ast::CondKind {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        out.fmt( match self {
            ast::CondKind::If => "if",
            ast::CondKind::Unless => "unless",
        })
    }
}

impl Format for ast::AssignOpKind {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        out.fmt( match self {
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
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        let ast::Block(statements) = self;
        out.fmt("{")?;
        out.next_line()?;
        out.indent()?;
        for stmt in statements {
            out.fmt(stmt)?;
            out.next_line()?;
        }
        out.dedent()?;
        out.fmt("}")
    }
}

// =============================================================================
// Expressions

impl Format for ast::Expr {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        match self {
            ast::Expr::Ternary { cond, left, right } => {
                out.fmt(("(", cond, " ? ", left, " : ", right, ")"))
            },
            ast::Expr::Binop(a, op, b) => out.fmt(("(", a, " ", op, " ", b, ")")),
            ast::Expr::Call { func, args } => {
                out.fmt(func)?;
                out.fmt_comma_separated("(", ")", args)
            },
            ast::Expr::Decrement { var } => out.fmt((var, "--")),
            ast::Expr::Unop(op, x) => out.fmt(("(", op, x, ")")),
            ast::Expr::LitInt{ value, hex: false } => out.fmt(value),
            ast::Expr::LitInt{ value, hex: true } => out.fmt(format_args!("{:#x}", value)),
            ast::Expr::LitFloat { value } => out.fmt(value),
            ast::Expr::LitString(x) => out.fmt(x),
            ast::Expr::Var(x) => out.fmt(x),
        }
    }
}

impl Format for ast::Var {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        match self {
            ast::Var::Named { ty, ident } => match ty {
                None => out.fmt( ident),
                Some(ast::TypeKind::Int) => out.fmt(("$", ident)),
                Some(ast::TypeKind::Float) => out.fmt(("%", ident)),
                Some(ast::TypeKind::Void) => panic!("unexpected void variable"),
            },
            ast::Var::Unnamed { ty, number } => match ty {
                ast::TypeKind::Int => out.fmt(("[", number, "]")),
                ast::TypeKind::Float => out.fmt(("[", *number as f32, "]")),
                ast::TypeKind::Void => panic!("unexpected void variable"),
            },
        }
    }
}

impl Format for ast::VarTypeKeyword {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        out.fmt( match self {
            ast::VarTypeKeyword::Int => "int",
            ast::VarTypeKeyword::Float => "float",
            ast::VarTypeKeyword::Var => "var",
        })
    }
}

impl Format for ast::BinopKind {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        out.fmt( match self {
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
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        out.fmt( match self {
            ast::UnopKind::Not => "!",
            ast::UnopKind::Neg => "-",
        })
    }
}

// =============================================================================
// Basic tokens

impl Format for ast::TypeKind {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        out.fmt( match self {
            ast::TypeKind::Int => "int",
            ast::TypeKind::Float => "float",
            ast::TypeKind::Void => "void",
        })
    }
}

impl Format for Ident {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        let s: &str = self.as_ref();
        out.fmt(s)
    }
}

impl<S: AsRef<[u8]>> Format for ast::LitString<S> {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        let mut tmp = BString::from(Vec::with_capacity(2*self.string.as_ref().len()+1));
        for byte in self.string.as_ref().bytes() {
            match byte {
                b'\0' => tmp.push_str(br#"\0"#),
                b'\"' => tmp.push_str(br#"\""#),
                b'\\' => tmp.push_str(br#"\\"#),
                b'\n' => tmp.push_str(br#"\n"#),
                b'\r' => tmp.push_str(br#"\r"#),
                b => tmp.push(b),
            }
        }
        out.fmt(("\"", tmp, "\""))
    }
}

impl Format for i32 {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        out.append_display_to_line(self)
    }
}

impl Format for f32 {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        let mut s = format!("{}", self);
        if !s.contains('.') {
            s.push_str(".0");
        }
        out.fmt(&s[..])
    }
}

// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // Verify that Shift-JIS text is preserved.
    const QUOTED_SJIS: &[u8] = b"\"\x82\xB1\x82\xF1\x82\xC9\x82\xBF\x82\xCD\""; // "こんにちは"
    const QUOTED_UTF8: &[u8] = "\"こんにちは\"".as_bytes();

    // Parse and dump back out, with some max columns.
    fn reformat<'a, T: crate::parse::Parse<'a> + Format>(ncol: usize, meta_text: &'a [u8]) -> Vec<u8> {
        let mut f = Formatter::new(vec![]).with_max_columns(ncol);
        let value = T::parse(meta_text).unwrap_or_else(|e| panic!("{}", e));
        f.fmt(&value).unwrap();
        f.into_inner().unwrap()
    }

    #[test]
    fn string_lit_utf8() {
        assert_eq!(reformat::<ast::LitString>(100, QUOTED_UTF8), QUOTED_UTF8);
    }

    #[test]
    fn string_lit_shift_jis() {
        assert_eq!(reformat::<ast::LitString>(100, QUOTED_SJIS), QUOTED_SJIS);
    }

    #[test]
    fn fancy_formatting() {
        // inline format
        assert_eq!(
            reformat::<Meta>(100, br#"{  apple:  "delicious" ,numbers  : [1 ,2, 3]}"#).as_bstr(),
            br#"{apple: "delicious", numbers: [1, 2, 3]}"#[..].as_bstr(),
        );

        // block format
        assert_eq!(
            reformat::<Meta>(3, br#"{  apple:  "delicious" ,numbers  : [1 ,2]}"#).trim().as_bstr(),
            br#"{
    apple: "delicious",
    numbers: [
        1,
        2,
    ],
}"#[..].as_bstr(),
        );

        // mixed format
        assert_eq!(
            reformat::<Meta>(30, br#"{a: [10, 23], b: [10000000, 230000000, 4900000]}"#).trim().as_bstr(),
            br#"{
    a: [10, 23],
    b: [
        10000000,
        230000000,
        4900000,
    ],
}"#[..].as_bstr()
        );
    }

    #[test]
    fn fancy_formatting_trigger_point() {
        // The line "    a: [10, 23]," is 16 characters long, so it should switch
        // to block formatting for max_columns <= 15.
        //
        // Verify that it switches at exactly the right point.
        assert_eq!(
            reformat::<Meta>(16, br#"{a: [10, 23], b: 30}"#).trim().as_bstr(),
            br#"{
    a: [10, 23],
    b: 30,
}"#[..].as_bstr(),
        );
        assert_eq!(
            reformat::<Meta>(15, br#"{a: [10, 23], b: 30}"#).trim().as_bstr(),
            br#"{
    a: [
        10,
        23,
    ],
    b: 30,
}"#[..].as_bstr(),
        );
    }

    #[test]
    fn test_time_formatting() {
        // * suppress initial 0 label
        // * prefer relative labels
        assert_eq!(
            reformat::<ast::Item>(9999, br#"void main() { 0: a(); 2: a(); 5: a(); }"#).as_bstr(),
            br#"
void main() {
    a();
+2: // 2
    a();
+3: // 5
    a();
}"#[1..].as_bstr(),
        );

        // * nonzero beginning
        // * absolute labels during decrease
        // * explicit 0 label
        assert_eq!(
            reformat::<ast::Item>(9999, br#"void main() { 5: a(); 3: a(); 0: a(); }"#).as_bstr(),
            br#"
void main() {
+5: // 5
    a();
3:
    a();
0:
    a();
}"#[1..].as_bstr(),
        );

        // negative label followed by zero or positive
        assert_eq!(
            reformat::<ast::Item>(9999, br#"void main() { -1: a(); 0: c(); -1: e(); 6: g(); }"#).as_bstr(),
            br#"
void main() {
-1:
    a();
0:
    c();
-1:
    e();
0:
+6: // 6
    g();
}"#[1..].as_bstr(),
        );

        // compression of identical time labels, regardless of sign
        assert_eq!(
            reformat::<ast::Item>(9999, br#"void main() { a(); b(); 6: c(); d(); -1: e(); f(); }"#).as_bstr(),
            br#"
void main() {
    a();
    b();
+6: // 6
    c();
    d();
-1:
    e();
    f();
}"#[1..].as_bstr(),
        );
    }
}
