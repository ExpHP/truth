use crate::ast;
use crate::pos::{Sp, Span};

/// An abbreviated way to refer to variants of token enums.
///
/// TODO: More docs and examples
#[macro_export]
macro_rules! token {
    (rec_sp!($span:expr => $($tok:tt)+)) => { sp!($span => token!($($tok)+)) };
    (+) => { $crate::ast::BinopKind::Add };
    (-) => { <_ as ::core::convert::Into<_>>::into($crate::quote::MinusSign) };
    (*) => { $crate::ast::BinopKind::Mul };
    (/) => { $crate::ast::BinopKind::Div };
    (%) => { $crate::ast::BinopKind::Rem };
    (|) => { $crate::ast::BinopKind::BitOr };
    (^) => { $crate::ast::BinopKind::BitXor };
    (&) => { $crate::ast::BinopKind::BitAnd };
    (||) => { $crate::ast::BinopKind::LogicOr };
    (&&) => { $crate::ast::BinopKind::LogicAnd };
    (==) => { $crate::ast::BinopKind::Eq };
    (!=) => { $crate::ast::BinopKind::Ne };
    (<) => { $crate::ast::BinopKind::Lt };
    (<=) => { $crate::ast::BinopKind::Le };
    (>) => { $crate::ast::BinopKind::Gt };
    (>=) => { $crate::ast::BinopKind::Ge };

    (!) => { $crate::ast::UnopKind::Not };

    (=) => { $crate::ast::AssignOpKind::Assign };
    (+=) => { $crate::ast::AssignOpKind::Add };
    (-=) => { $crate::ast::AssignOpKind::Sub };
    (*=) => { $crate::ast::AssignOpKind::Mul };
    (/=) => { $crate::ast::AssignOpKind::Div };
    (%=) => { $crate::ast::AssignOpKind::Rem };
    (|=) => { $crate::ast::AssignOpKind::BitOr };
    (^=) => { $crate::ast::AssignOpKind::BitXor };
    (&=) => { $crate::ast::AssignOpKind::BitAnd };

    (int) => { ::core::convert::Into::into($crate::quote::KeywordInt) };
    (float) => { ::core::convert::Into::into($crate::quote::KeywordFloat) };
    (var) => { $crate::ast::VarDeclKeyword::Var };
    (void) => { $crate::ast::FuncReturnType::Void };
    (if) => { $crate::ast::CondKeyword::If };
    (unless) => { $crate::ast::CondKeyword::Unless };
    (sin) => { $crate::ast::UnopKind::Sin };
    (cos) => { $crate::ast::UnopKind::Cos };
    (sqrt) => { $crate::ast::UnopKind::Sqrt };
    (_S) => { $crate::ast::UnopKind::CastI };
    (_f) => { $crate::ast::UnopKind::CastF };
}

// These briefly appear in the expansion of `token!()` for tokens that can be parsed as
// more than one output type.
#[doc(hidden)] pub struct MinusSign;
#[doc(hidden)] pub struct KeywordInt;
#[doc(hidden)] pub struct KeywordFloat;

macro_rules! impl_ambiguous_token_into {
    ($( $UnitTy:ident => ast::$OutTy:ident::$Variant:ident, )*) => {$(
        impl From<$UnitTy> for ast::$OutTy {
            fn from(_: $UnitTy) -> Self { ast::$OutTy::$Variant }
        }
    )*}
}

impl_ambiguous_token_into!{
    MinusSign => ast::BinopKind::Sub,
    MinusSign => ast::UnopKind::Neg,
    KeywordInt => ast::FuncReturnType::Int,
    KeywordInt => ast::VarDeclKeyword::Int,
    KeywordFloat => ast::FuncReturnType::Float,
    KeywordFloat => ast::VarDeclKeyword::Float,
}

// -----------------------------------

/// A recursive form of `sp!()` for recursively applying a span to subterms when using macros to generate AST nodes.
#[macro_export(local_inner_macros)]
macro_rules! rec_sp {
    // favor interior spans of nested sp! calls
    ($span:expr => sp!$args:tt ) => { sp!$args };
    ($span:expr => rec_sp!$args:tt ) => { rec_sp!$args };
    // Add a span to the thing, then stick ourselves into the argument to recurse.
    ($span:expr => $mac:ident!( $($arg:tt)* )) => { match $span { span => $crate::quote::IntoSpanned::into_spanned($mac!(rec_sp!( span => $($arg)+ )), span) }};
    ($span:expr => $mac:ident![ $($arg:tt)* ]) => { match $span { span => $crate::quote::IntoSpanned::into_spanned($mac![rec_sp!( span => $($arg)+ )], span) }};
    ($span:expr => $mac:ident!{ $($arg:tt)* }) => { match $span { span => $crate::quote::IntoSpanned::into_spanned($mac!{rec_sp!( span => $($arg)+ )}, span) }};
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

impl_into_spanned_for_ast!{
    ast::Expr, ast::Var, ast::Item, ast::Stmt, ast::StmtBody, ast::StmtLabel,
    ast::UnopKind, ast::BinopKind, ast::AssignOpKind,
    ast::CondKeyword, ast::FuncReturnType, ast::VarDeclKeyword, ast::MetaKeyword,
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

    // The macros are some nasty incremental tt munchers that are too tedious to write by hand,
    // so we generate them.
    include!(concat!(env!("OUT_DIR"), "/generated_macros.rs"));
}

// -----------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pos::FileId;

    const FILE_ID: FileId = std::num::NonZeroU32::new(1);

    #[test]
    fn smoke_test() {
        let span_1 = Span::new(FILE_ID, 1, 1);
        let span_2 = Span::new(FILE_ID, 2, 2);
        let a: ast::Expr = 23.into();
        let b: Sp<ast::Expr> = sp!(span_2 => 42.into());
        let c: ast::Expr = 32.into();
        let var: ast::Var = ast::Var::Named { ident: "lol".parse().unwrap(), ty_sigil: None };
        // panic!("{:?}", expr_binop!());

        // Subexprs in an AST macro can be:
        //  * opaque, parenthesized expressions
        //  * local variable identifiers
        //  * another macro call, through which rec_sp! will be recursively applied
        let expr = rec_sp!(span_1 => expr_binop!((a.clone()) + expr_binop!(a + expr_binop!(b - c))));
        match &expr.value {
            ast::Expr::Binop(subexpr1, op, subexpr2) => match &subexpr2.value {
                ast::Expr::Binop(subexpr21, op2, subexpr22) => match &subexpr22.value {
                    ast::Expr::Binop(subexpr221, op22, subexpr222) => {
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
        let expr = rec_sp!(span_1 => expr_binop!(a + rec_sp!(span_2 => expr_binop!(b + (ast::Expr::from(31))))));
        match &expr.value {
            ast::Expr::Binop(subexpr1, _, subexpr2) => match &subexpr2.value {
                ast::Expr::Binop(subexpr21, _, subexpr22) => {
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
        let expr = rec_sp!(span_1 => expr_binop!(a + sp!(span_2 => b)));
        match &expr.value {
            ast::Expr::Binop(subexpr1, op, subexpr2) => {
                assert_eq!(subexpr1.span, span_1);
                assert_eq!(subexpr2.span, span_2);
            },
            ex => panic!("{:?}", ex),
        }
    }
}
