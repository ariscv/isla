#[cfg(feature = "tracetool")]
pub mod itrace;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ItraceTerminalMetadata {
    pub scope: String,
    pub case_id: u64,
    pub status: String,
    pub phase: String,
    pub path_signature: u64,
}
