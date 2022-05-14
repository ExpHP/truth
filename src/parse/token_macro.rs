macro_rules! define_token_enum {
    (
        $( #[$($meta:tt)+] )*
        $vis:vis enum $Token:ident<$lt:lifetime> {
            $( #[token($fixed_str:literal)] $fixed_variant:ident, )*

            $(
                #[regex($($regex_tt:tt)+)]
                $regex_variant:ident($regex_ty:ty),
            )*

            #[error]
            $( #[ $($error_meta:tt)+ ] )*
            Error,

            $($other_variants:tt)*
        }
    ) => {
        $( #[$($meta)+] )*
        $vis enum $Token<$lt> {
            $( #[token($fixed_str)] $fixed_variant, )*

            $( #[regex($($regex_tt)+)] $regex_variant($regex_ty), )*

            #[error]
            $( #[ $($error_meta)+ ] )*
            Error,

            $($other_variants)*
        }

        const _: () = {
            use ::core::fmt;

            impl<'input> $Token<'input> {
                pub(super) fn as_str(&self) -> &'input str {
                    match self {
                        $( $Token::$fixed_variant => $fixed_str, )*
                        $( $Token::$regex_variant(str) => str, )*
                        $Token::Error => "<invalid>",

                        // e.g. virtual tokens
                        #[allow(unreachable_patterns)]
                        _ => "<special>",
                    }
                }
            }

            impl fmt::Display for Token<'_> {
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    fmt::Display::fmt(&self.as_str(), f)
                }
            }
        };
    };
}
