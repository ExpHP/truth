use crate::ast;
use crate::pos::{Sp, Span};

/// An abbreviated way to refer to variants of token enums.
///
/// TODO: More docs and examples
#[macro_export]
macro_rules! token {
    (rec_sp!($span:expr => $($tok:tt)+)) => { sp!($span => token!($($tok)+)) };

    ($(binop)? +) => { $crate::ast::BinOpKind::Add };
    (  binop   -) => { $crate::ast::BinOpKind::Sub };
    ($(binop)? *) => { $crate::ast::BinOpKind::Mul };
    ($(binop)? /) => { $crate::ast::BinOpKind::Div };
    (  binop   %) => { $crate::ast::BinOpKind::Rem };
    ($(binop)? |) => { $crate::ast::BinOpKind::BitOr };
    ($(binop)? ^) => { $crate::ast::BinOpKind::BitXor };
    ($(binop)? &) => { $crate::ast::BinOpKind::BitAnd };
    ($(binop)? ||) => { $crate::ast::BinOpKind::LogicOr };
    ($(binop)? &&) => { $crate::ast::BinOpKind::LogicAnd };
    ($(binop)? ==) => { $crate::ast::BinOpKind::Eq };
    ($(binop)? !=) => { $crate::ast::BinOpKind::Ne };
    ($(binop)? <) => { $crate::ast::BinOpKind::Lt };
    ($(binop)? <=) => { $crate::ast::BinOpKind::Le };
    ($(binop)? >) => { $crate::ast::BinOpKind::Gt };
    ($(binop)? >=) => { $crate::ast::BinOpKind::Ge };

    ($(unop)? !) => { $crate::ast::UnOpKind::Not };
    (  unop   -) => { $crate::ast::UnOpKind::Neg };
    ($(unop)? sin) => { $crate::ast::UnOpKind::Sin };
    ($(unop)? cos) => { $crate::ast::UnOpKind::Cos };
    ($(unop)? sqrt) => { $crate::ast::UnOpKind::Sqrt };
    ($(unop)? _S) => { $crate::ast::UnOpKind::CastI };
    ($(unop)? _f) => { $crate::ast::UnOpKind::CastF };

    ($(assignop)? =) => { $crate::ast::AssignOpKind::Assign };
    ($(assignop)? +=) => { $crate::ast::AssignOpKind::Add };
    ($(assignop)? -=) => { $crate::ast::AssignOpKind::Sub };
    ($(assignop)? *=) => { $crate::ast::AssignOpKind::Mul };
    ($(assignop)? /=) => { $crate::ast::AssignOpKind::Div };
    ($(assignop)? %=) => { $crate::ast::AssignOpKind::Rem };
    ($(assignop)? |=) => { $crate::ast::AssignOpKind::BitOr };
    ($(assignop)? ^=) => { $crate::ast::AssignOpKind::BitXor };
    ($(assignop)? &=) => { $crate::ast::AssignOpKind::BitAnd };

    ($(ty)? int) => { $crate::ast::TypeKeyword::Int };
    ($(ty)? float) => { $crate::ast::TypeKeyword::Float };
    ($(ty)? string) => { $crate::ast::TypeKeyword::String };
    ($(ty)? var) => { $crate::ast::TypeKeyword::Var };
    ($(ty)? void) => { $crate::ast::TypeKeyword::Void };

    ($(fnqual)? const) => { $crate::ast::FuncQualifier::Const };
    ($(fnqual)? inline) => { $crate::ast::FuncQualifier::Inline };

    ($(cond)? if) => { $crate::ast::CondKeyword::If };
    ($(cond)? unless) => { $crate::ast::CondKeyword::Unless };

    ($(pseudo)? pop) => { $crate::ast::PseudoArgKind::Pop };
    ($(pseudo)? mask) => { $crate::ast::PseudoArgKind::Mask };
    ($(pseudo)? blob) => { $crate::ast::PseudoArgKind::Blob };
    ($(pseudo)? arg0) => { $crate::ast::PseudoArgKind::ExtraArg };

    ($(meta)? meta) => { $crate::ast::MetaKeyword::Meta };
    ($(meta)? entry) => { $crate::ast::MetaKeyword::Entry };

    ($(labelprop)? offsetof) => { $crate::ast::LabelPropertyKeyword::OffsetOf };
    ($(labelprop)? timeof) => { $crate::ast::LabelPropertyKeyword::TimeOf };

    ($(loopjump)? continue) => { $crate::ast::BreakContinueKeyword::Continue };
    ($(loopjump)? break) => { $crate::ast::BreakContinueKeyword::Break };

    ($(sigil)? $) => { $crate::ast::VarSigil::Int };
    (  sigil   %) => { $crate::ast::VarSigil::Float };

    // ambiguous ones; these will use Into, which may work in exprs, though you're SOL in patterns
    // and will have to provide a disambiguating prefix there.  e.g. `token![unop -]`
    (-) => { ::core::convert::Into::into($crate::quote::MinusSign) };
    (%) => { ::core::convert::Into::into($crate::quote::PercentSign) };
}

// These briefly appear in the expansion of `token!()` for tokens that can be parsed as
// more than one output type.
#[doc(hidden)] pub struct MinusSign;
#[doc(hidden)] pub struct PercentSign;

macro_rules! impl_ambiguous_token_into {
    ($( $UnitTy:ident => ast::$OutTy:ident::$Variant:ident, )*) => {$(
        impl From<$UnitTy> for ast::$OutTy {
            fn from(_: $UnitTy) -> Self { ast::$OutTy::$Variant }
        }
    )*}
}

impl_ambiguous_token_into!{
    MinusSign => ast::BinOpKind::Sub,
    MinusSign => ast::UnOpKind::Neg,
    PercentSign => ast::VarSigil::Float,
    PercentSign => ast::BinOpKind::Rem,
}

// -----------------------------------

/// A recursive form of `sp!()` for recursively applying a span to subterms when using macros to generate AST nodes.
#[macro_export(local_inner_macros)]
macro_rules! rec_sp {
    // favor interior spans of nested sp! calls
    ($span:expr => sp!$args:tt ) => { sp!$args };
    ($span:expr => rec_sp!$args:tt ) => { rec_sp!$args };
    // `rec_sp!()` can be applied to a vec of macro calls
    ($span:expr => vec![$($mac:ident!$args:tt),* $(,)?]) => { match $span { span => _truth__vec![$( rec_sp!(span => $mac!$args) ),*] } };
    // If the macro is wrapped in _ast_sp_transparent!(...), don't apply a span here, but DO recurse
    ($span:expr => _ast_sp_transparent!($mac:ident!( $($arg:tt)+ ))) => { $mac!(rec_sp!( span => $($arg)+ )) };
    ($span:expr => _ast_sp_transparent!($mac:ident![ $($arg:tt)+ ])) => { $mac![rec_sp!( span => $($arg)+ )] };
    ($span:expr => _ast_sp_transparent!($mac:ident!{ $($arg:tt)+ })) => { $mac!{rec_sp!( span => $($arg)+ )} };
    ($span:expr => _ast_sp_transparent!($value:expr)) => { $value };
    // Add a span to the thing, then stick ourselves into the argument to recurse.
    ($span:expr => $mac:ident!( $($arg:tt)+ )) => { match $span { span => $crate::quote::IntoSpanned::into_spanned($mac!(rec_sp!( span => $($arg)+ )), span) }};
    ($span:expr => $mac:ident![ $($arg:tt)+ ]) => { match $span { span => $crate::quote::IntoSpanned::into_spanned($mac![rec_sp!( span => $($arg)+ )], span) }};
    ($span:expr => $mac:ident!{ $($arg:tt)+ }) => { match $span { span => $crate::quote::IntoSpanned::into_spanned($mac!{rec_sp!( span => $($arg)+ )}, span) }};
    ($span:expr => $value:expr) => { $crate::quote::IntoSpanned::into_spanned($value, $span) };
}

/// Allows a span to be added to an AST node if it doesn't already have one.
///
/// This is used in the implementation of the [`rec_sp`] macro to allow spans to be recursively set on spanless
/// subterms, while preserving any spans that already exist.
pub trait IntoSpanned {
    type Value;

    fn into_spanned(self, default_span: Span) -> Sp<Self::Value>;
}

// Implementation for a type that already has a span.
impl<T> IntoSpanned for Sp<T> {
    type Value = T;

    fn into_spanned(self, _: Span) -> Sp<Self::Value> { self }
}

macro_rules! impl_into_spanned_for_ast {
    ($($ty:ty,)+) => {$(
        impl IntoSpanned for $ty {
            type Value = $ty;

            fn into_spanned(self, span: Span) -> Sp<Self::Value> { Sp { span, value: self } }
        }
    )+};
}

// Implementations that apply a span to an item that currently lacks one.
//
// One is provided for every type that we might wrap `Sp<...>` around.
impl_into_spanned_for_ast!{
    ast::Expr, ast::Var, ast::Item, ast::Stmt, ast::StmtKind, ast::Cond,
    ast::UnOpKind, ast::BinOpKind, ast::AssignOpKind,
    ast::CondKeyword, ast::TypeKeyword, ast::MetaKeyword,
    crate::ident::Ident,
    crate::ast::Meta,
    i32, f32,
}

// -----------------------------------

/// An AST macro that applies a function to the output of another AST macro.
///
/// This is used sometimes in the parsing and expansion of AST macros when one of the subterms is an enum.
/// For instance, an 'if' condition might parse to `_ast_map!($crate::ast::Cond::Expr, $($toks)+)`.
///
/// (why not just parse to `$crate::ast::Cond::Expr($($toks)+)`? The answer is because that's not a macro
///  call, so `rec_sp!` would not be able to recurse into it)
#[macro_export]
#[doc(hidden)]
macro_rules! _ast_map {
    (rec_sp!($span:expr => $map_func:expr, $($inner:tt)+)) => {
        $map_func(rec_sp!($span => $($inner)+))
    };
    ($map_func:expr, $($inner:tt)+) => {
        $map_func($($inner)+)
    };
}

/// An AST pseudo-macro that causes [`rec_sp`] to recurse into another macro's body without also applying a span to the
/// final result.
///
/// Basically, the difference is:
///
/// * `rec_sp!(span => mac!(<stuff>))` expands to `sp!(span => mac!(rec_sp!(span => <stuff>)))`. (sort of)
/// * `rec_sp!(span => _ast_sp_transparent!(mac!(<stuff>)))` expands to `mac!(rec_sp!(span => <stuff>))`,
///   i.e. no span is applied to the outermost result.
///
/// Similarly, for non-macro expressions, `rec_sp!(span => <expr>)` expands to `sp!(span => <expr>)`,
/// while `rec_sp!(span => _ast_sp_transparent!(<expr>))` simply expands to `<expr>`.
///
/// In actuality, this macro is never actually called.  [`rec_sp`] will recognize it by name, alter its own behavior,
/// and remove it from the token stream.
#[macro_export]
#[doc(hidden)]
macro_rules! _ast_sp_transparent {
    ($($t:tt)*) => {
        compile_error!(concat!(
            "The macro _ast_sp_transparent!() was invoked. This should never happen!\n",
            "Args: `", stringify!($($t)*), "`",
        ))
    };
}

// -----------------------------------

#[macro_use]
mod ast_macros {
    #[doc(hidden)]
    #[macro_export]
    macro_rules! _truth__compile_error {
        ($($t:tt)*) => { compile_error!{$($t)*} }
    }

    #[doc(hidden)]
    #[macro_export]
    macro_rules! _truth__stringify {
        ($($t:tt)*) => { stringify!{$($t)*} }
    }

    #[doc(hidden)]
    #[macro_export]
    macro_rules! _truth__concat {
        ($($t:tt)*) => { concat!{$($t)*} }
    }

    #[doc(hidden)]
    #[macro_export]
    macro_rules! _truth__vec {
        ($($t:tt)*) => { vec!{$($t)*} }
    }

    // The macros are some nasty incremental tt munchers that are too tedious to write by hand,
    // so we generate them.
    include!(concat!(env!("OUT_DIR"), "/generated_macros.rs"));
}

// -----------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pos::FileId;
    use crate::ident::Ident;

    const FILE_ID: FileId = std::num::NonZeroU32::new(1);

    #[test]
    fn smoke_test() {
        let span_1 = Span::new(FILE_ID, 1, 1);
        let span_2 = Span::new(FILE_ID, 2, 2);
        let a: ast::Expr = 23.into();
        let b: Sp<ast::Expr> = sp!(span_2 => 42.into());
        let c: ast::Expr = 32.into();

        // Subexprs in an AST macro can be:
        //  * opaque, parenthesized expressions
        //  * local variable identifiers
        //  * another macro call, through which rec_sp! will be recursively applied
        let expr = rec_sp!(span_1 => expr_binop!(#(a.clone()) + expr_binop!(#a + expr_binop!(#b - #c))));
        match &expr.value {
            ast::Expr::BinOp(subexpr1, op, subexpr2) => match &subexpr2.value {
                ast::Expr::BinOp(subexpr21, op2, subexpr22) => match &subexpr22.value {
                    ast::Expr::BinOp(subexpr221, op22, subexpr222) => {
                        assert_eq!(expr.span, span_1);
                        assert_eq!(op.span, span_1);
                        assert_eq!(op2.span, span_1);
                        assert_eq!(op22.span, span_1);
                        assert_eq!(subexpr1.span, span_1);
                        assert_eq!(subexpr22.span, span_1);

                        // these are both 'a'
                        assert_eq!(subexpr1, subexpr21);

                        // b should have kept its own span
                        assert_ne!(subexpr222.span, subexpr221.span);
                        assert_eq!(subexpr221.span, span_2);
                    },
                    ex => panic!("{:?}", ex),
                },
                ex => panic!("{:?}", ex),
            },
            ex => panic!("{:?}", ex),
        }
    }

    #[test]
    fn nested_rec_sp() {
        let span_1 = Span::new(FILE_ID, 1, 1);
        let span_2 = Span::new(FILE_ID, 2, 2);

        // Test that the span from an inner rec_sp! takes precedence over the outer one
        let a: ast::Expr = 23.into();
        let b: ast::Expr = 42.into();
        let expr = rec_sp!(span_1 => expr_binop!(
            #a + rec_sp!(span_2 => expr_binop!(#b + #(ast::Expr::from(31))))
        ));
        match &expr.value {
            ast::Expr::BinOp(subexpr1, _, subexpr2) => match &subexpr2.value {
                ast::Expr::BinOp(subexpr21, _, subexpr22) => {
                    assert_eq!(subexpr1.span, span_1);
                    assert_eq!(subexpr2.span, span_2);
                    assert_eq!(subexpr21.span, span_2);
                    assert_eq!(subexpr22.span, span_2);
                },
                ex => panic!("{:?}", ex),
            },
            ex => panic!("{:?}", ex),
        }

        // Test that the span from an inner sp! takes precedence over an outer rec_sp!
        let a: ast::Expr = 23.into();
        let b: ast::Expr = 42.into();
        let expr = rec_sp!(span_1 => expr_binop!(#a + sp!(span_2 => b)));
        match &expr.value {
            ast::Expr::BinOp(subexpr1, _, subexpr2) => {
                assert_eq!(subexpr1.span, span_1);
                assert_eq!(subexpr2.span, span_2);
            },
            ex => panic!("{:?}", ex),
        }
    }

    #[test]
    fn without_rec_sp() {
        let span_1 = Span::new(FILE_ID, 1, 1);

        // Test that the span from an inner rec_sp! takes precedence over the outer one
        let a: ast::Expr = 23.into();
        let b: ast::Expr = 42.into();
        let _ = expr_binop!(sp!(span_1 => a) sp!(span_1 => token![+]) sp!(span_1 => b));

        let a: Sp<ast::Expr> = sp!(span_1 => 23.into());
        let b: Sp<ast::Expr> = sp!(span_1 => 42.into());
        let _ = expr_binop!(#a sp!(span_1 => token![+]) #b);
    }

    #[test]
    fn stmt() {
        let span_1 = Span::new(FILE_ID, 1, 1);

        let label: Ident = "label".parse().unwrap();
        let _ = rec_sp!(span_1 => stmt_label!(#label));
    }
}
