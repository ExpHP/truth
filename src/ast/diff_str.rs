use std::collections::BTreeMap;

use crate::ast;
use crate::raw;
use crate::diagnostic::Diagnostic;
use crate::bitset::BitSet32;
use crate::pos::Sp;

type FlagIndex = u32;

#[derive(Debug, Clone, Default)]
pub struct DiffFlagNames {
    flag_default_enable: BitSet32,
    by_name: BTreeMap<char, FlagIndex>,
    by_flag: BTreeMap<FlagIndex, char>,
}

const VALID_CHAR_DESCRIPTION: &'static str = "ASCII alphanumeric character";
macro_rules! diff_flag_char_pat {
    () => { '0'..='9' | 'a'..='z' | 'A'..='Z' };
}

impl DiffFlagNames {
    pub fn define_flag_from_mapfile(&mut self, index: Sp<i32>, str: Sp<&str>) -> Result<(), Diagnostic> {
        if !(0 <= index.value && index.value < 8) {
            return Err(error!(
                message("difficulty flag index out of range"),
                primary(index, "must be from 0 to 7 inclusive"),
            ));
        }

        let invalid_definition = || error!(
            message("invalid difficulty flag definition"),
            primary(str, ""),
            note("the definition must consist of a {} and a +/- (+ means enabled by default)", VALID_CHAR_DESCRIPTION),
        );
        if str.len() != 2 || !str.is_char_boundary(1) {
            return Err(invalid_definition());
        }

        let mut chars = str.chars();
        let name = match chars.next().unwrap() {
            c@diff_flag_char_pat!() => c,
            _ => return Err(invalid_definition()),
        };
        let enable = match chars.next().unwrap() {
            '-' => false,
            '+' => true,
            _ => return Err(invalid_definition()),
        };

        self.define_flag(name, index.value as _, enable);
        Ok(())
    }

    pub fn define_flag(&mut self, name: char, index: u32, enable: bool) {
        assert!(index < 8);
        assert!(matches!(name, diff_flag_char_pat!()));

        self.flag_default_enable.set_bit(index as _, enable);
        self.by_name.insert(name, index as _);
        self.by_flag.insert(index as _, name);
    }

    pub fn parse_diff_string(&self, str: Sp<&str>) -> Result<Sp<BitSet32>, Diagnostic> {
        let mut out = BitSet32::new();
        let mut enable = true;
        for char in str.chars() {
            match char {
                '-' => enable = false,
                '+' => enable = true,

                diff_flag_char_pat!() => match self.by_name.get(&char) {
                    Some(&index) => out.set_bit(index as _, enable),
                    None => return Err(error!(
                        message("unknown difficulty flag {:?}", char),
                        primary(str, ""),
                        note("the known flags are: {}", self.currently_known_flags_msg()),
                    )),
                },

                _ => return Err(error!(
                    message("invalid character {:?} in difficulty string", char),
                    primary(str, ""),
                    note("valid characters are '-', '+', or a {}", VALID_CHAR_DESCRIPTION),
                )),
            }
        }
        Ok(sp!(str.span => out))
    }

    pub fn mask_to_diff_label(&self, mask: BitSet32) -> Result<ast::Expr, Diagnostic> {
        let must_enable = mask & self.flag_default_enable.complement(8);
        let must_disable = mask.complement(8) & self.flag_default_enable;

        // they must all have names for us to create a string
        if (must_enable | must_disable).into_iter().any(|bit| !self.by_flag.contains_key(&bit)) {
            return Ok((mask.mask() as raw::LangInt).into());
        }

        let mut out = String::new();
        for bit in must_enable {
            out.push(self.by_flag[&bit]);
        }

        if !must_disable.is_empty() {
            out.push('-');
            for bit in must_disable {
                out.push(self.by_flag[&bit]);
            }
        }
        Ok(out.into())
    }

    fn currently_known_flags_msg(&self) -> String {
        self.by_name.keys().map(ToString::to_string).collect::<Vec<_>>().join(", ")
    }
}
