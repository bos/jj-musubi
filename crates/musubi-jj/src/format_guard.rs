//! Rejects operation and view files containing fields this jj-lib does not define.
//!
//! jj-lib decodes op store files with prost, which silently drops unknown fields. A file
//! written by a newer `jj` could therefore lose data when musubi canonicalizes it. Walking
//! the protobuf encoding against the schema of `simple_op_store.proto` (jj-lib 0.46) turns
//! that into an error instead.

use std::fmt::Write as _;

use thiserror::Error;

#[derive(Debug, Error, PartialEq, Eq)]
pub enum FormatError {
    #[error("unknown field {field} in {path} (written by a newer jj?)")]
    UnknownField { path: String, field: u32 },
    #[error("field {field} in {path} has wire type {wire_type}, expected {expected}")]
    WireType {
        path: String,
        field: u32,
        wire_type: u8,
        expected: u8,
    },
    #[error("malformed protobuf in {path}")]
    Malformed { path: String },
}

#[derive(Clone, Copy)]
enum Kind {
    Varint,
    /// Strings, bytes, and packed repeated scalars.
    Bytes,
    Message(Msg),
}

impl Kind {
    fn wire_type(self) -> u8 {
        match self {
            Self::Varint => 0,
            Self::Bytes | Self::Message(_) => 2,
        }
    }
}

/// Message types of `simple_op_store.proto`, plus the synthetic map-entry messages.
#[derive(Clone, Copy, Debug)]
enum Msg {
    Operation,
    OperationMetadata,
    Timestamp,
    AttributesEntry,
    CommitPredecessors,
    View,
    WcCommitIdsEntry,
    GitRef,
    Bookmark,
    RemoteBookmark,
    Tag,
    GitHead,
    RemoteView,
    RemoteRef,
    RefTargetTerm,
    RefTarget,
    RefConflictLegacy,
    RefConflict,
    RefConflictTerm,
}

impl Msg {
    /// The kind of each field this message defines. Reserved fields count as known: they
    /// appear only in files from older versions, which jj-lib 0.46 reads by ignoring them.
    fn field(self, number: u32) -> Option<Kind> {
        use Kind::*;
        let kind = match (self, number) {
            (Self::Operation, 1 | 2) => Bytes,
            (Self::Operation, 3) => Message(Self::OperationMetadata),
            (Self::Operation, 4) => Message(Self::CommitPredecessors),
            (Self::Operation, 5) => Varint,

            (Self::OperationMetadata, 1 | 2) => Message(Self::Timestamp),
            (Self::OperationMetadata, 3 | 4 | 5 | 8) => Bytes,
            (Self::OperationMetadata, 6) => Message(Self::AttributesEntry),
            (Self::OperationMetadata, 7) => Varint,

            (Self::Timestamp, 1 | 2) => Varint,
            (Self::AttributesEntry, 1 | 2) => Bytes,
            (Self::CommitPredecessors, 1 | 2) => Bytes,

            (Self::View, 1 | 2 | 7) => Bytes,
            (Self::View, 3) => Message(Self::GitRef),
            (Self::View, 4) => Bytes,
            (Self::View, 5) => Message(Self::Bookmark),
            (Self::View, 6) => Message(Self::Tag),
            (Self::View, 8) => Message(Self::WcCommitIdsEntry),
            (Self::View, 9) => Message(Self::RefTarget),
            (Self::View, 10 | 12) => Varint,
            (Self::View, 11) => Message(Self::RemoteView),
            (Self::View, 13) => Message(Self::GitHead),

            (Self::WcCommitIdsEntry, 1 | 2) => Bytes,
            (Self::GitRef, 1 | 2) => Bytes,
            (Self::GitRef, 3) => Message(Self::RefTarget),
            (Self::Bookmark, 1) => Bytes,
            (Self::Bookmark, 2) => Message(Self::RefTarget),
            (Self::Bookmark, 3) => Message(Self::RemoteBookmark),
            (Self::RemoteBookmark, 1) => Bytes,
            (Self::RemoteBookmark, 2) => Message(Self::RefTarget),
            (Self::RemoteBookmark, 3) => Varint,
            (Self::Tag | Self::GitHead, 1) => Bytes,
            (Self::Tag | Self::GitHead, 2) => Message(Self::RefTarget),
            (Self::RemoteView, 1) => Bytes,
            (Self::RemoteView, 2 | 3) => Message(Self::RemoteRef),
            (Self::RemoteRef, 1) => Bytes,
            (Self::RemoteRef, 2) => Message(Self::RefTargetTerm),
            (Self::RemoteRef, 3) => Varint,
            (Self::RefTargetTerm | Self::RefConflictTerm, 1) => Bytes,
            (Self::RefTarget, 1) => Bytes,
            (Self::RefTarget, 2) => Message(Self::RefConflictLegacy),
            (Self::RefTarget, 3) => Message(Self::RefConflict),
            (Self::RefConflictLegacy, 1 | 2) => Bytes,
            (Self::RefConflict, 1 | 2) => Message(Self::RefConflictTerm),
            _ => return None,
        };
        Some(kind)
    }
}

/// Checks an encoded `simple_op_store.Operation`.
pub fn check_operation(bytes: &[u8]) -> Result<(), FormatError> {
    walk(bytes, Msg::Operation, &mut String::from("Operation"))
}

/// Checks an encoded `simple_op_store.View`.
pub fn check_view(bytes: &[u8]) -> Result<(), FormatError> {
    walk(bytes, Msg::View, &mut String::from("View"))
}

fn walk(mut bytes: &[u8], msg: Msg, path: &mut String) -> Result<(), FormatError> {
    let malformed = |path: &str| FormatError::Malformed {
        path: path.to_owned(),
    };
    while !bytes.is_empty() {
        let tag = read_varint(&mut bytes).ok_or_else(|| malformed(path))?;
        let field = u32::try_from(tag >> 3).map_err(|_| malformed(path))?;
        let wire_type = (tag & 7) as u8;
        let kind = msg.field(field).ok_or_else(|| FormatError::UnknownField {
            path: path.clone(),
            field,
        })?;
        // The schema has no fixed-width or packed repeated scalar fields, so every known
        // field has exactly one valid wire type.
        if wire_type != kind.wire_type() {
            return Err(FormatError::WireType {
                path: path.clone(),
                field,
                wire_type,
                expected: kind.wire_type(),
            });
        }
        match kind {
            Kind::Varint => {
                read_varint(&mut bytes).ok_or_else(|| malformed(path))?;
            }
            Kind::Bytes | Kind::Message(_) => {
                let len = read_varint(&mut bytes).ok_or_else(|| malformed(path))?;
                let len = usize::try_from(len).map_err(|_| malformed(path))?;
                if len > bytes.len() {
                    return Err(malformed(path));
                }
                let (body, rest) = bytes.split_at(len);
                bytes = rest;
                if let Kind::Message(inner) = kind {
                    let saved = path.len();
                    write!(path, ".{field}:{inner:?}").expect("writing to a String");
                    walk(body, inner, path)?;
                    path.truncate(saved);
                }
            }
        }
    }
    Ok(())
}

fn read_varint(bytes: &mut &[u8]) -> Option<u64> {
    let mut value = 0u64;
    for shift in (0..64).step_by(7) {
        let (&byte, rest) = bytes.split_first()?;
        *bytes = rest;
        value |= u64::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return Some(value);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn varint(mut v: u64, out: &mut Vec<u8>) {
        loop {
            let byte = (v & 0x7f) as u8;
            v >>= 7;
            if v == 0 {
                out.push(byte);
                return;
            }
            out.push(byte | 0x80);
        }
    }

    fn field_bytes(field: u32, body: &[u8], out: &mut Vec<u8>) {
        varint(u64::from(field) << 3 | 2, out);
        varint(body.len() as u64, out);
        out.extend_from_slice(body);
    }

    #[test]
    fn accepts_known_nested_fields() {
        let mut term = Vec::new();
        field_bytes(1, b"commit", &mut term);
        let mut remote_ref = Vec::new();
        field_bytes(1, b"main", &mut remote_ref);
        field_bytes(2, &term, &mut remote_ref);
        let mut remote_view = Vec::new();
        field_bytes(1, b"origin", &mut remote_view);
        field_bytes(2, &remote_ref, &mut remote_view);
        let mut view = Vec::new();
        field_bytes(1, b"head", &mut view);
        field_bytes(11, &remote_view, &mut view);
        assert_eq!(check_view(&view), Ok(()));
    }

    #[test]
    fn rejects_unknown_nested_field() {
        let mut remote_ref = Vec::new();
        field_bytes(9, b"future", &mut remote_ref);
        let mut remote_view = Vec::new();
        field_bytes(2, &remote_ref, &mut remote_view);
        let mut view = Vec::new();
        field_bytes(11, &remote_view, &mut view);
        assert_eq!(
            check_view(&view),
            Err(FormatError::UnknownField {
                path: "View.11:RemoteView.2:RemoteRef".into(),
                field: 9
            })
        );
    }

    #[test]
    fn rejects_truncated_input() {
        let mut view = Vec::new();
        field_bytes(1, b"head", &mut view);
        view.pop();
        assert!(matches!(
            check_view(&view),
            Err(FormatError::Malformed { .. })
        ));
    }
}
