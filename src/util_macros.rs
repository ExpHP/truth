
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
