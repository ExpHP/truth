
#[cfg(test)]
#[macro_use]
/// Alternative `insta` macros with the following properties:
///
/// * They use a single snapshot directory outside of the src/ directory.
/// * If you provide a third argument, it is ADDED to the expression rather than replacing it.
///   This way, there is no hidden disadvantage to providing an extra string that describes
///   what the test is specifically looking for.
mod _insta_helpers {
    macro_rules! assert_snapshot { ($($args:tt)+) => { wrap_insta!(assert_snapshot, $($args)+) }; }

    /// Normally when you provide a snapshot name, it removes the current function name from the snapshot.
    /// This is a workaround to add some sort of prefix back in.
    #[cfg(test)]
    macro_rules! prefix_snapshot_names {
        ($prefix:literal, {
            $( $mac:ident!( $name:literal, $($args:tt)+ ); )+
        }) => {{ $( $mac!(concat!($prefix, "__", $name), $($args)+); )+ }};
    }

    #[cfg(test)]
    macro_rules! wrap_insta {
        ($mac:ident, $name:expr, $value:expr) => {
            wrap_insta!{@ $mac, $name, $value}
        };
        ($mac:ident, $name:expr, $value:expr, $debug_expr:expr) => {
            wrap_insta!{@ $mac, $name, $value, concat!(stringify!($value), "\n\n", $debug_expr)}
        };
        ($mac:ident, $value:expr) => {
            wrap_insta!{@ $mac, $value}
        };
        (@ $mac:ident, $($args:tt)+) => {
            insta::with_settings!{{snapshot_path => concat!(env!("CARGO_MANIFEST_DIR"), "/snapshots")}, {
                insta::$mac!{$($args)+}
            }}
        };
    }
}

macro_rules! zip {
    ($a:expr, $b:expr) => { IntoIterator::into_iter($a).zip($b) };
    ($a:expr, $b:expr, $c:expr) => { IntoIterator::into_iter($a).zip($b).zip($c).map(|((a, b), c)| (a, b, c)) };
    ($a:expr, $b:expr, $c:expr, $d:expr) => { IntoIterator::into_iter($a).zip($b).zip($c).zip($d).map(|(((a, b), c), d)| (a, b, c, d)) };
}

// =============================================================================

#[derive(Debug, thiserror::Error)]
#[error("got {:?}, expected one of: {:?}", .got, .expected)]
pub struct ParseStrEnumError {
    pub got: String,
    pub expected: &'static [&'static str],
}

// Quick little util for stringly enums.
macro_rules! string_enum {
    (
        $(#[$($Enum_attr:tt)+])*
        $vis:vis enum $Enum:ident {
            $(
                $(#[$($variant_attr:tt)+])* $Variant:ident,
            )*
        }
    ) => {
        $(#[$($Enum_attr)+])*
        #[derive(strum::Display, strum::EnumString)]
        $vis enum $Enum {
            $( $(#[$($variant_attr)+])* $Variant, )*
        }

        impl crate::fmt::Format for $Enum {
            fn fmt<W: ::std::io::Write>(&self, out: &mut crate::fmt::Formatter<W>) -> crate::fmt::Result {
                out.fmt(format_args!("{}", self))
            }
        }
    }
}

// =============================================================================

#[macro_export]
macro_rules! _diagnostic {
    ( // shorthand for message only
        @ $severity:ident,
        $message_fmt:literal $(, $message_arg:expr)* $(,)?
    ) => { $crate::_diagnostic!{
        @ $severity,
        message($message_fmt $(, $message_arg)*),
    }};

    ( @ $severity:ident, $($rest:tt)+ ) => {{
        let mut d = $crate::diagnostic::Diagnostic::$severity();
        $crate::_diagnostic_muncher!( [&mut d], $($rest)+ );
        d
    }};
}

#[macro_export]
macro_rules! _diagnostic_muncher {
    ( [$d:expr] ) => { $d };
    ( [$d:expr], ) => { $d };
    ( [$d:expr], code=$code:literal $($rest:tt)* ) => { $crate::_diagnostic_muncher!{
        [$d.code($code)] $($rest)*
    }};
    ( [$d:expr], message( $($msg:tt)+ ) $($rest:tt)* ) => { $crate::_diagnostic_muncher!{
        [$d.message(format!($($msg)+))] $($rest)*
    }};
    ( [$d:expr], primary( $span:expr, $($msg:tt)+ ) $($rest:tt)* ) => { $crate::_diagnostic_muncher!{
        [$d.primary(&$span, format!($($msg)+))] $($rest)*
    }};
    ( [$d:expr], secondary( $span:expr, $($msg:tt)+ ) $($rest:tt)* ) => { $crate::_diagnostic_muncher!{
        [$d.secondary(&$span, format!($($msg)+))] $($rest)*
    }};
    ( [$d:expr], note( $($msg:tt)+ ) $($rest:tt)* ) => { $crate::_diagnostic_muncher!{
        [$d.note(format!($($msg)+))] $($rest)*
    }};
}

/// Generates a [`crate::diagnostic::Diagnostic`] of severity `bug`.
#[macro_export]
macro_rules! bug {
    ($($arg:tt)+) => { $crate::_diagnostic!(@bug, $($arg)+) };
}

/// Generates a [`crate::diagnostic::Diagnostic`] of severity `error`.
///
/// See `error_macro_examples` near its definition for an example of usage.
#[macro_export]
macro_rules! error {
    ($($arg:tt)+) => { $crate::_diagnostic!(@error, $($arg)+) };
}

/// Generates a [`crate::diagnostic::Diagnostic`] of severity `warning`.
#[macro_export]
macro_rules! warning {
    ($($arg:tt)+) => { $crate::_diagnostic!(@warning, $($arg)+) };
}

/// Generates a [`crate::diagnostic::Diagnostic`] of severity `info`.
#[macro_export]
macro_rules! info {
    ($($arg:tt)+) => { $crate::_diagnostic!(@info, $($arg)+) };
}

#[test]
fn error_macro_examples() {
    use crate::ast;

    let mut scope = crate::Builder::new().capture_diagnostics(true).build();
    let mut truth = scope.truth();
    let some_ast_node = truth.parse::<ast::Expr>("<input>", "1 + x".as_ref()).unwrap();
    let some_span = some_ast_node.span;

    // Shorthand form: Just the message
    truth.emit(error!("lmao {}", 20 + 3)).ignore();

    // Long form: any parts can be mixed and matched in any order
    truth.emit(error!(
        code="E0201",
        message("lmao {}", 20 + 3),
        // labels.  First arg is a span, rest is format args.
        primary(some_span, "1 is silly"),
        secondary(some_ast_node, "{} is silly", "x"),  // <- they can also take Sp<T>
        primary(some_ast_node, "yeah, you can have multiple, what about it"),
    )).ignore();
}
