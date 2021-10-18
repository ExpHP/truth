//! Pseudo-arguments; special "arguments" that can be used on instructions that
//! directly set parts of the raw format.

use crate::raw;
use crate::ast;
use crate::pos::Sp;
use crate::diagnostic::Diagnostic;

/// A normalized form of the pseudo-args in an instruction call.
pub struct PseudoArgData {
    pub param_mask: Option<Sp<raw::ParamMask>>,
    pub blob: Option<Sp<Vec<u8>>>,
    pub pop: Option<Sp<raw::StackPop>>,
    pub extra_arg: Option<Sp<raw::ExtraArg>>,
}

impl PseudoArgData {
    pub fn from_pseudos(pseudos: &[Sp<ast::PseudoArg>]) -> Result<PseudoArgData, Diagnostic> {
        let mut param_mask = None;
        let mut extra_arg = None;
        let mut blob = None;
        let mut pop = None;

        for pseudo in pseudos {
            macro_rules! set_option {
                ($option:ident, $as_const_method:ident) => {{
                    let value: &Sp<ast::Expr> = &pseudo.value.value;

                    if let Some(prev) = $option.take() {
                        return Err(error!(
                            message("duplicate pseudo-arg"),
                            secondary(prev, "previously supplied here"),
                            primary(value, "duplicate pseudo-arg"),
                        ));
                    }

                    $option = Some({
                        value.$as_const_method()
                            .map(|const_value| sp!(value.span => const_value))
                            .ok_or_else(|| error!(
                                message("non-const pseudo-arg"),
                                primary(value, "non-const pseudo-arg"),
                            ))?
                    });
                }}
            }

            match pseudo.kind.value {
                ast::PseudoArgKind::Blob => set_option!(blob, as_const_str),
                ast::PseudoArgKind::Mask => set_option!(param_mask, as_const_int),
                ast::PseudoArgKind::Pop => set_option!(pop, as_const_int),
                ast::PseudoArgKind::ExtraArg => set_option!(extra_arg, as_const_int),
            }
        }

        Ok(PseudoArgData {
            blob: blob.map(|str| parse_args_blob(str).map(|s| sp!(str.span => s))).transpose()?,
            param_mask: param_mask.map(|x| sp!(x.span => x.value as _)),
            pop: pop.map(|x| sp!(x.span => x.value as _)),
            extra_arg: extra_arg.map(|x| sp!(x.span => x.value as _)),
        })
    }
}

fn parse_args_blob(str: Sp<&str>) -> Result<Vec<u8>, Diagnostic> {
    let mut out = vec![];
    let mut first_char = None;
    for c in str.chars() {
        if c.is_ascii_whitespace() {
            continue;
        }
        let value = match c {
            'a'..='f' => (c as u32 as u8 - b'a' + 10),
            'A'..='F' => (c as u32 as u8 - b'A' + 10),
            '0'..='9' => (c as u32 as u8 - b'0'),
            _ => return Err(error!(
                message("invalid character '{}' in blob literal", c),
                primary(str, "invalid blob literal"),
            )),
        };

        match first_char.take() {
            Some(first_char) => out.push(first_char * 16 + value),
            None => first_char = Some(value),
        }
    }

    if first_char.is_some() {
        return Err(error!(
            message("odd number of hexadecimal digits in blob literal"),
            primary(str, "invalid blob literal"),
        ));
    }

    // XXX EoSD ECL violates this :/
    // if out.len() % 4 != 0 {
    //     return Err(error!(
    //         message("number of bytes in blob not divisible by 4 (remainder: {})", out.len() % 4),
    //         primary(str, "invalid blob literal"),
    //     ))
    // }

    Ok(out)
}

#[test]
fn test_parse_args_blob() {
    assert_eq!(parse_args_blob(sp!("0b0 C0d21")).unwrap(), vec![11, 12, 13, 33]);
    assert!(parse_args_blob(sp!("0b0c0d2")).is_err());  // odd length
    assert!(parse_args_blob(sp!("0b0c==0d21")).is_err());  // bad character
}

pub fn format_blob(blob: &[u8]) -> String {
    use std::fmt::Write;

    let mut out = String::new();
    let mut first_chunk = true;

    for chunk in blob.chunks(4) {
        if !first_chunk {
            out.push_str(" ");
        }
        first_chunk = false;

        for &byte in chunk {
            write!(&mut out, "{:02x}", byte).unwrap();
        }
    }
    out
}
