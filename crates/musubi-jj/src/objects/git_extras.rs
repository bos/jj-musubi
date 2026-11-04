//! jj's Git extras encoding, independent of its private generated protobuf module.
//!
//! Field numbers and types match jj's `git_store.proto`. Keep obsolete fields so that
//! prost rejects malformed encodings of them just as jj's decoder does.

/// Metadata that older Git commits cannot always carry in their headers.
#[derive(Clone, PartialEq, prost::Message)]
pub struct CommitExtras {
    /// Alternating positive and negative tree terms, set only for conflicts.
    #[prost(bytes = "vec", repeated, tag = "1")]
    pub root_tree: Vec<Vec<u8>>,
    /// Earlier versions of this commit.
    #[prost(bytes = "vec", repeated, tag = "2")]
    pub predecessors: Vec<Vec<u8>>,
    /// The commit's change identity, if it differs from the one Git implies.
    #[prost(bytes = "vec", tag = "4")]
    pub change_id: Vec<u8>,
    /// Obsolete field retained for decoding existing metadata.
    #[prost(bool, tag = "8")]
    pub is_open: bool,
    /// Obsolete field retained for decoding existing metadata.
    #[prost(bool, tag = "9")]
    pub is_pruned: bool,
    /// Whether trees use the conflict representation.
    #[prost(bool, tag = "10")]
    pub uses_tree_conflict_format: bool,
}
