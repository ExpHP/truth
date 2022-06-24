use crate::raw;
use crate::resolve::RegId;
use serde::ser::{Serialize, Serializer};

pub const VERSION: u32 = 1;

// =================================================================================================

#[derive(serde::Serialize)]
#[derive(Debug, Clone, Default)]
#[serde(rename_all = "kebab-case")]
pub struct DebugInfo {
    /// `debug-info` version.  This is incremented when breaking changes are made.
    pub version: Version,
    pub source_files: Vec<SourceFile>,
    pub exported_scripts: Vec<Script>,
    /// Global `const`s.
    pub consts: Vec<Const>,
}

/// Version field in the debug-info file.  This is always the [latest debug-info version][`VERSION`].
#[derive(Debug, Clone, Default)]
pub struct Version;

impl Serialize for Version {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        VERSION.serialize(serializer)
    }
}

#[derive(serde::Serialize)]
#[derive(Debug, Clone)]
#[serde(rename_all = "kebab-case")]
pub struct SourceFile {
    /// A number identifying this source file inside [`Span`]s.
    ///
    /// The numbers assigned to source files in this array are NOT necessarily sequential
    /// or in increasing order, but they are unique among [`SourceFile`]s in this `debug_info`.
    pub id: i32,
    /// This may be the path of a file, or some other placeholder string indicating what this source
    /// file represents.
    pub name: String,
}

#[derive(serde::Serialize)]
#[derive(Debug, Clone)]
#[serde(rename_all = "kebab-case")]
pub struct BinaryFile {
    /// A number identifying this source file inside [`Span`]s.
    ///
    /// The numbers assigned to source files in this array are NOT necessarily sequential
    /// or in increasing order, but they are unique among [`BinaryFile`]s in this `debug_info`.
    pub id: i32,
    /// This may be the path of a file, or some other placeholder string indicating what this source
    /// file represents.
    pub name: String,
}

#[derive(serde::Serialize)]
#[derive(Debug, Clone)]
#[serde(rename_all = "kebab-case")]
pub struct Script {
    // These smaller structs exist to make it easier to construct, by breaking it up
    // similarly to how the lowering code is organized.  Feel free to ruthlessly reorganize and
    // refactor these structs when changing the lowering code.
    #[serde(flatten)]
    pub export_info: ScriptExportInfo,
    #[serde(flatten)]
    pub lowering_info: ScriptLoweringInfo,
}

#[derive(serde::Serialize)]
#[derive(Debug, Clone)]
#[serde(rename_all = "kebab-case")]
pub struct ScriptLoweringInfo {
    #[serde(flatten)]
    pub register_info: ScriptRegisterInfo,
    #[serde(flatten)]
    pub offset_info: ScriptOffsetInfo,
}

#[derive(serde::Serialize)]
#[derive(Debug, Clone)]
#[serde(rename_all = "kebab-case")]
pub struct ScriptExportInfo {
    pub exported_as: ScriptType,
    pub name: Option<String>,
    pub name_span: Span,
}

#[derive(serde::Serialize)]
#[derive(Debug, Clone)]
#[serde(rename_all = "kebab-case")]
pub struct ScriptRegisterInfo {
    pub locals: Vec<Local>,
}

#[derive(serde::Serialize)]
#[derive(Debug, Clone)]
#[serde(rename_all = "kebab-case")]
pub struct ScriptOffsetInfo {
    pub instrs: Vec<Instr>,
    /// Offset (in bytes) from the first instruction to the position after the last instruction.
    pub end_offset: raw::BytePos,
    pub labels: Vec<Label>,
}

#[derive(serde::Serialize)]
#[derive(Debug, Clone)]
#[serde(rename_all = "kebab-case")]
#[serde(tag = "type")]
pub enum ScriptType {
    SclScript { index: usize },
    AnmScript { index: usize },
    MsgScript { indices: Vec<usize> },
    StdScript,
    EclSub { index: usize },
}

#[derive(serde::Serialize)]
#[derive(Debug, Clone)]
#[serde(rename_all = "kebab-case")]
pub struct Const {
    pub name: String,
    pub name_span: Option<Span>,
    pub value: Value,
}

#[derive(serde::Serialize)]
#[derive(Debug, Clone)]
#[serde(rename_all = "kebab-case")]
pub struct Local {
    pub name: String,
    pub name_span: Span,
    pub r#type: LocalType,
    pub bound_to: LocalBinding,
}

#[derive(serde::Serialize)]
#[derive(Debug, Clone)]
#[serde(rename_all = "kebab-case")]
pub enum LocalType {
    Int,
    Float,
}

impl From<crate::value::ReadType> for LocalType {
    fn from(ty: crate::value::ReadType) -> Self {
        match ty {
            crate::value::ReadType::Int => Self::Int,
            crate::value::ReadType::Float => Self::Float,
        }
    }
}

#[derive(serde::Serialize)]
#[derive(Debug, Clone)]
#[serde(rename_all = "kebab-case")]
pub enum LocalBinding {
    Reg(raw::Register),
}

impl From<RegId> for LocalBinding {
    fn from(reg: RegId) -> Self {
        LocalBinding::Reg(reg.0)
    }
}

#[derive(serde::Serialize)]
#[derive(Debug, Clone)]
#[serde(rename_all = "kebab-case")]
pub enum Value {
    Int(raw::LangInt),
    Float(raw::LangFloat),
    String(String),
}

impl From<crate::value::ScalarValue> for Value {
    fn from(value: crate::value::ScalarValue) -> Value {
        match value {
            crate::value::ScalarValue::Int(x) => Value::Int(x),
            crate::value::ScalarValue::Float(x) => Value::Float(x),
            crate::value::ScalarValue::String(x) => Value::String(x),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Span {
    span: crate::pos::Span,
}

impl From<crate::pos::Span> for Span {
    fn from(span: crate::pos::Span) -> Self {
        Span { span }
    }
}

impl Serialize for Span {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self.span.file_id {
            None => serializer.serialize_none(),  // null
            Some(file_id) => {
                let tuple = (file_id.get(), self.span.start.0, self.span.end.0);
                tuple.serialize(serializer)
            },
        }
    }
}

#[derive(serde::Serialize)]
#[derive(Debug, Clone)]
#[serde(rename_all = "kebab-case")]
pub struct Label {
    /// Offset of this label.  This will always be equal to one of the offsets of one of the [`Instr`]s,
    /// or to [`Script::end_offset`].
    pub offset: raw::BytePos,
    pub time: raw::Time,
    pub name: String,
    pub span: Span,
}

#[derive(serde::Serialize)]
#[derive(Debug, Clone)]
#[serde(rename_all = "kebab-case")]
pub struct Instr {
    /// Byte offset into script for this instruction.
    pub offset: raw::BytePos,
    /// Span that might be suitable for a source-level debugger to point at for this instruction.
    pub span: Span,
}

// =================================================================================================
