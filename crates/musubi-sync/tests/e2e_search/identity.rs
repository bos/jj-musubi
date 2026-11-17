//! Operation identities used by the search. None of these metadata keys replaces a native
//! operation id or an immutable canonical original: each records a different equivalence
//! relation, and the source collectors keep their existing ambiguity checks.
//!
//! The encoded keys retain their original lexical ordering and diagnostic spelling. Only
//! these constructors interpret metadata or jj template output; callers compare typed keys.

use std::fmt;

use jj_lib::op_store::Operation;

/// History-key projection, retaining the exact diagnostic encoding emitted by jj.
pub const OP_KEY_TEMPLATE: &str = r#"time.start().format("%Y-%m-%dT%H:%M:%S%.f") ++ " " ++ time.end().format("%Y-%m-%dT%H:%M:%S%.f") ++ " " ++ user ++ " " ++ description.first_line() ++ "\n""#;

/// Source-key projection, matching `SourceKey::of` byte for byte.
pub const MERGE_KEY_TEMPLATE: &str = r#"time.start().format("%s%3f") ++ " " ++ time.end().format("%s%3f") ++ " " ++ description.first_line()"#;

/// Start/end milliseconds and the first description line, excluding parents, view and user.
/// Reparenting and canonicalization preserve this key. Seeded command times distinguish
/// commands, but simultaneous node merges can collide: source collectors must reject an
/// ambiguous body and survivor lookup must require one native id on each side of a rewrite.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceKey(String);

impl SourceKey {
    /// The same encoding as `MERGE_KEY_TEMPLATE`.
    pub fn of(op: &Operation) -> Self {
        let metadata = &op.metadata;
        Self(format!(
            "{} {} {}",
            metadata.time.start.timestamp.0,
            metadata.time.end.timestamp.0,
            metadata.description.lines().next().unwrap_or_default()
        ))
    }

    pub fn from_template(encoded: &str) -> Self {
        Self(encoded.to_owned())
    }
}

impl fmt::Display for SourceKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl fmt::Debug for SourceKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

/// ISO start/end times, user and first description line, as `OP_KEY_TEMPLATE` emits them.
/// Embedded operation ids in restore/revert descriptions are normalized because each copy
/// names the same operation differently. Equality compares those exact normalized bytes;
/// this key compares replicated histories, without proving an exact native parent version.
/// The seeded command chronology distinguishes independent commands. Equal encodings remain
/// set-equivalent as before; exact identity and collision qualification use native ids.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HistoryKey(String);

impl HistoryKey {
    pub fn from_template(encoded: &str) -> Self {
        Self(without_op_ids(encoded))
    }

    pub fn is_join(&self) -> bool {
        self.0.ends_with(" joins") && self.0.contains(" musubi: ")
    }
}

impl fmt::Display for HistoryKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl fmt::Debug for HistoryKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

/// A normalized source key, hostname and username, in that order. Parent ids mentioned by
/// restore/revert descriptions are ignored here too. Equal headers are candidate witnesses:
/// different native parent versions and originals can have the same header, so history
/// checks still require exact native/original evidence and retain unknown-header cases.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceHeader {
    key: String,
    hostname: String,
    username: String,
}

impl SourceHeader {
    pub fn of(op: &Operation) -> Self {
        Self {
            key: without_op_ids(&SourceKey::of(op).0),
            hostname: op.metadata.hostname.clone(),
            username: op.metadata.username.clone(),
        }
    }
}

impl fmt::Debug for SourceHeader {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&(&self.key, &self.hostname, &self.username), f)
    }
}

/// Full native import metadata: start/end milliseconds, hostname, username and the entire
/// description. Seeded command times distinguish imports; ref and HEAD imports of one
/// command have distinct descriptions. Parents and views may both change in a later
/// representation, which must not cause that same import to be judged again.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ImportIdentity(String);

impl ImportIdentity {
    pub fn of(op: &Operation) -> Self {
        let metadata = &op.metadata;
        Self(format!(
            "{} {} {} {} {}",
            metadata.time.start.timestamp.0,
            metadata.time.end.timestamp.0,
            metadata.hostname,
            metadata.username,
            metadata.description,
        ))
    }
}

/// Native jj operations whose semantics the harness distinguishes. Prefixes are exactly
/// the ones used by the existing checks; reconciliation is an exact description match.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NativeOperation {
    Undo,
    Redo,
    Restore,
    Revert,
    Fetch,
    ImportRefs,
    ImportHead,
    Reconciliation,
    Other,
}

impl NativeOperation {
    pub fn of(op: &Operation) -> Self {
        Self::from_description(&op.metadata.description)
    }

    pub fn from_description(description: &str) -> Self {
        if description == "reconcile divergent operations" {
            return Self::Reconciliation;
        }
        for (prefix, kind) in [
            ("undo", Self::Undo),
            ("redo", Self::Redo),
            ("restore to operation", Self::Restore),
            ("revert operation", Self::Revert),
            ("fetch from git remote", Self::Fetch),
            ("import git refs", Self::ImportRefs),
            ("import git head", Self::ImportHead),
        ] {
            if description.starts_with(prefix) {
                return kind;
            }
        }
        Self::Other
    }

    pub fn restores_view(self) -> bool {
        matches!(self, Self::Undo | Self::Redo | Self::Restore | Self::Revert)
    }

    pub fn explains_reintroduced_work(self) -> bool {
        self.restores_view() || matches!(self, Self::Fetch | Self::ImportRefs | Self::ImportHead)
    }
}

/// Copy-local ids in a restore/revert's description do not distinguish its representations.
/// Preserve the first matching marker and its original maximal hexadecimal run exactly.
fn without_op_ids(key: &str) -> String {
    for marker in ["restore to operation ", "revert operation "] {
        if let Some(at) = key.find(marker) {
            let start = at + marker.len();
            let end = key[start..]
                .find(|c: char| !c.is_ascii_hexdigit())
                .map_or(key.len(), |len| start + len);
            return format!("{}<op>{}", &key[..start], &key[end..]);
        }
    }
    key.to_owned()
}
