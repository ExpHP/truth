use std::collections::HashMap;
use crate::CompileError;
use crate::ident::Ident;
use crate::eclmap::Eclmap;
use crate::ast;
use crate::pos::{Span, Sp};

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct TypeSystem {
    /// List of all loaded mapfiles
    mapfiles: Vec<std::path::PathBuf>,

    // Functions
    func_aliases: HashMap<Ident, Ident>,

    // Instructions
    opcode_signatures: HashMap<u32, Signature>,
    pub opcode_names: HashMap<u32, Ident>,

    // Variables
    gvar_default_types: HashMap<i32, ScalarType>,
    pub gvar_map: HashMap<Ident, i32>,
    pub gvar_names: HashMap<i32, Ident>,
}

impl TypeSystem {
    pub fn new() -> Self { Self::default() }

    /// Get the signature of a function as a single instruction, if known.
    pub fn ins_signature(&self, name: &Ident) -> Option<&Signature> {
        let name = self.resolve_func_aliases(name);
        match name.as_ins() {
            Some(opcode) => self.opcode_signatures.get(&opcode),
            _ => unimplemented!("function is not an instruction"),
        }
    }

    pub fn resolve_func_aliases<'a>(&'a self, name: &'a Ident) -> &'a Ident {
        let mut name: &Ident = name;
        loop {
            if let Some(new_name) = self.func_aliases.get(name) {
                name = new_name;
                continue;
            }
            return name;
        }
    }

    /// Get the type of a variable (int or float), if known.
    pub fn var_type(&self, var: &ast::Var) -> Option<ScalarType> {
        match *var {
            ast::Var::Named { ty, ref ident } => {
                if let Some(ty) = ty {
                    return Some(ty.into()); // explicit type from user
                }
                self.gvar_default_types.get(self.gvar_map.get(ident)?).copied()
            },
            ast::Var::Unnamed { ty, .. } => Some(ty.into()),
        }
    }

    /// Get the ID number of a variable, if it is a global.
    pub fn gvar_id(&self, var: &ast::Var) -> Option<i32> {
        match *var {
            ast::Var::Named { ref ident, .. } => self.gvar_map.get(ident).copied(),
            ast::Var::Unnamed { number, .. } => Some(number),
        }
    }

    /// Generate an AST node with the ideal appearance for a global variable reference.
    pub fn gvar_to_ast(&self, id: i32, ty: ScalarType) -> ast::Var {
        match self.gvar_names.get(&id) {
            Some(name) => {
                // Suppress the type prefix if it matches the default
                if self.gvar_default_types.get(&id) == Some(&ty) {
                    ast::Var::Named { ident: name.clone(), ty: None }
                } else {
                    ast::Var::Named { ident: name.clone(), ty: Some(ty.into()) }
                }
            },
            None => ast::Var::Unnamed { number: id, ty: ty.into() },
        }
    }

    /// Add info from an eclmap.  Its path is recorded in order to help emit import directives
    /// into the file.
    pub fn extend_from_eclmap(&mut self, path: &std::path::Path, eclmap: &Eclmap) {
        self.mapfiles.push(path.to_owned());

        for (&opcode, name) in &eclmap.ins_names {
            self.opcode_names.insert(opcode as u32, name.clone());
            self.func_aliases.insert(name.clone(), Ident::new_ins(opcode as u32));
        }
        for (&opcode, value) in &eclmap.ins_signatures {
            let arg_string = value.to_string();
            self.opcode_signatures.insert(opcode as u32, Signature { arg_string });
        }
        for (&id, name) in &eclmap.gvar_names {
            self.gvar_names.insert(id, name.clone());
            self.gvar_map.insert(name.clone(), id);
        }
        for (&id, value) in &eclmap.gvar_types {
            let ty = match &value[..] {
                "%" => ScalarType::Float,
                "$" => ScalarType::Int,
                _ => {
                    fast_warning!(
                        "In mapfile: Ignoring invalid variable type '{}' for gvar {}",
                        value, id,
                    );
                    continue;
                },
            };
            self.gvar_default_types.insert(id, ty);
        }
    }

    pub fn mapfiles_to_ast(&self) -> Vec<crate::pos::Sp<ast::LitString>> {
        self.mapfiles.iter().map(|s| {
            let string = s.to_str().expect("unpaired surrogate not supported!").into();
            sp!(ast::LitString { string })
        }).collect()
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
            // o and t get no special encoding because we translate jumps directly into `goto`
            'o' => ArgEncoding::Dword, // offset
            't' => ArgEncoding::Dword, // time
            'f' => ArgEncoding::Float,
            '_' => ArgEncoding::Padding,
            'n' => ArgEncoding::Dword, // FIXME sprite
            'N' => ArgEncoding::Dword, // FIXME script
            _ => panic!("In mapfile: unknown signature character: {:?}", c)
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

/// Type of a value that exists at runtime in the script.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(enum_map::Enum)]
pub enum ScalarType { Int, Float }

/// Type of an argument to an instruction.
///
/// This is a bit more nuanced compared to [`ScalarType`].  Arguments with the same type
/// may have different encodings based on how they are either stored in the file, or on how they
/// may be written in a source file.
///
/// By this notion, [`ArgEncoding`] tends to be more relevant for immediate/literal arguments, while
/// [`ScalarType`] tends to be more relevant for variables.
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

impl ScalarType {
    pub fn default_encoding(self) -> ArgEncoding {
        match self {
            ScalarType::Int => ArgEncoding::Dword,
            ScalarType::Float => ArgEncoding::Float,
        }
    }

    /// Textual description, e.g. `"an integer"`.
    pub fn descr(self) -> &'static str {
        match self {
            ScalarType::Int => "an integer",
            ScalarType::Float => "a float",
        }
    }

    pub fn check_same(self, other: ScalarType, cause: Span, spans: (Span, Span)) -> Result<ScalarType, CompileError> {
        if self == other {
            Ok(self)
        } else {
            Err(error!(
                message("type error"),
                primary(spans.1, "{}", other.descr()),
                secondary(cause, "same types required due to this"),
                secondary(spans.0, "{}", self.descr()),
            ))
        }
    }
}

impl Sp<ast::BinopKind> {
    pub fn result_type(&self, a: ScalarType, b: ScalarType, arg_spans: (Span, Span)) -> Result<ScalarType, CompileError> {
        use ast::BinopKind as B;

        // they ALL require matching types
        let ty = a.check_same(b, self.span, arg_spans)?;
        match self.value {
            B::Add | B::Sub | B::Mul | B::Div | B::Rem | B::LogicOr | B::LogicAnd => Ok(ty),
            B::Eq | B::Ne | B::Lt | B::Le | B::Gt | B::Ge => Ok(ScalarType::Int),
            B::BitXor | B::BitAnd | B::BitOr => {
                if ty == ScalarType::Int {
                    Ok(ScalarType::Int)
                } else {
                    Err(error!(
                        message("type error"),
                        primary(arg_spans.0, "{}", a.descr()),
                        secondary(self, "only defined on integers"),
                    ))
                }
            },
        }
    }
}

impl Sp<ast::UnopKind> {
    pub fn result_type(&self, ty: ScalarType, arg_span: Span) -> Result<ScalarType, CompileError> {
        match self.value {
            ast::UnopKind::Neg => Ok(ty),
            ast::UnopKind::Not => {
                if ty == ScalarType::Int {
                    Ok(ScalarType::Int)
                } else {
                    Err(error!(
                        message("type error"),
                        primary(arg_span, "{}", ty.descr()),
                        secondary(self, "only defined on integers"),
                    ))
                }
            },
        }
    }
}
