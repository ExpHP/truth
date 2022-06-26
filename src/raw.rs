//! Raw integer aliases.
//!
//! Using these everywhere is not obligatory but they can help reduce memorization and
//! they can also explain choices when there are competing reasonable alternatives
//! for an integer size.
//!
//! You are meant to import this as `use crate::raw;` and then use the names qualified,
//! e.g. `raw::LangInt`.  This helps these types stand out as names that stand in for
//! primitive types.

/// An integer in the high-level abstract machine.
///
/// The vast majority of integers in the AST will be of this type, even if they represent
/// something of a lower bit-width in the target binary, as this may help them be replaced
/// with const expressions in the future.
pub type LangInt = i32;

/// A floating point number in the high-level abstract machine.
pub type LangFloat = f32;

/// The preferred type for representing the time field of an instruction.
pub type Time = i32;

/// The preferred type for representing an instruction opcode.
pub type Opcode = u16;

/// The preferred type for representing a register ID.
pub type Register = i32;

/// The preferred type for representing the parameter mask field of an instruction.
pub type ParamMask = u16;

/// The preferred type for representing the extra argument of an ECL timeline instruction.
pub type ExtraArg = i16;

/// The preferred type for representing the difficulty mask field of an ECL instruction.
pub type DifficultyMask = u8;

/// The preferred type for representing the argument count field of an ECL instruction.
pub type ArgCount = u8;

/// An dword-sized integer serving as a bag of 32 bits.  It's possible that these bits actually
/// encode data of a different type. (e.g. a signed integer or a float...)
pub type RawDwordBits = u32;

/// The preferred type for representing the stack pop field of a modern ECL instruction.
pub type StackPop = u8;

/// The preferred type for representing an instruction's unsigned byte position relative to
/// the beginning of a compiled subroutine.
pub type BytePos = u64;
