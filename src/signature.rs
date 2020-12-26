use std::collections::HashMap;
use crate::ident::Ident;
use crate::eclmap::Eclmap;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Functions {
    aliases: HashMap<Ident, Ident>,
    opcode_signatures: HashMap<u32, Signature>,
    pub opcode_names: HashMap<u32, Ident>,
}

impl Functions {
    pub fn new() -> Self { Self::default() }

    /// Get the signature of a function as a single instruction, if known.
    pub fn ins_signature(&self, name: &Ident) -> Option<&Signature> {
        let name = self.resolve_aliases(name);
        match name.as_ins() {
            Some(opcode) => self.opcode_signatures.get(&opcode),
            _ => unimplemented!("function is not an instruction"),
        }
    }

    pub fn resolve_aliases<'a>(&'a self, name: &'a Ident) -> &'a Ident {
        let mut name: &Ident = name;
        loop {
            if let Some(new_name) = self.aliases.get(name) {
                name = new_name;
                continue;
            }
            return name;
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signature {
    /// String representing the signature.
    arg_string: String,
}

impl Signature {
    /// Get an automatic signature for reading an unknown instruction with this many dwords.
    pub fn auto(n: usize) -> Signature {
        Signature { arg_string: String::from_utf8(vec![b'S'; n]).unwrap() }
    }

    pub fn arg_encodings(&self) -> Vec<ArgEncoding> {
        self.arg_string.chars().map(|c| match c {
            'S' => ArgEncoding::Dword,
            'C' => ArgEncoding::Color,
            'f' => ArgEncoding::Float,
            '_' => ArgEncoding::Padding,
            _ => panic!("unknown signature character: {:?}", c)
        }).collect()
    }

    /// Get the minimum number of args allowed in the AST.
    pub fn min_args(&self) -> usize { self.count_args_incl_padding() - self.count_padding() }
    /// Get the maximum number of args allowed in the AST.
    pub fn max_args(&self) -> usize { self.count_args_incl_padding() }

    fn count_args_incl_padding(&self) -> usize {
        self.arg_string.len()
    }

    fn count_padding(&self) -> usize {
        self.arg_string.bytes().rev().position(|c| c != b'_').unwrap_or(self.count_args_incl_padding())
    }

    pub fn split_padding<'a, T>(&self, args: &'a [T]) -> Option<(&'a [T], &'a [T])> {
        let i = self.count_args_incl_padding() - self.count_padding();
        if i <= args.len() {
            Some(args.split_at(i))
        } else { None }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArgEncoding {
    /// Script argument encoded as a 4-byte integer.
    Dword,
    /// Unused 4-byte space after script arguments, optionally displayed as integer in text.
    ///
    /// Only exists in pre-StB STD where instructions have fixed sizes.
    Padding,
    /// Script argument encoded as a 4-byte integer, printed as hex.
    Color,
    /// Script argument encoded as a 4-byte float.
    Float,
}

impl Functions {
    pub fn add_from_eclmap(&mut self, eclmap: &Eclmap) {
        for (&opcode, name) in &eclmap.ins_names {
            self.opcode_names.insert(opcode as u32, name.clone());
            self.aliases.insert(name.clone(), Ident::new_ins(opcode as u32));
        }
        for (&opcode, value) in &eclmap.ins_signatures {
            let arg_string = value.to_string();
            self.opcode_signatures.insert(opcode as u32, Signature { arg_string });
        }
    }
}
