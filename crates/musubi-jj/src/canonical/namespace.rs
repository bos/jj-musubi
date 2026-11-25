//! `musubi.workspace-context`: names of workspaces as one machine gave them, by the
//! machine-qualified keys they stand for. An earlier release recorded it on canonical
//! operations where `jj op abandon` had trimmed their history away. Nothing writes or reads it
//! now, but it is part of the operations that carry it, and of their ids, for as long as their
//! hives last, so imports still accept it, checking only that it is well formed, as they did.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use jj_lib::op_store::OperationMetadata;
use serde::Deserialize;

use super::CanonicalError;
use crate::workspaces;

const ATTRIBUTE: &str = "musubi.workspace-context";

/// Literal names apply only on `source`. Canonical views, rather than these names, carry
/// the resulting bindings to other machines.
#[derive(Deserialize)]
pub(crate) struct Namespace {
    source: String,
    names: BTreeMap<String, String>,
    known: BTreeSet<String>,
}

impl Namespace {
    /// Refuses an operation whose `musubi.workspace-context` isn't one an earlier release
    /// could have written.
    pub fn check(metadata: &OperationMetadata) -> Result<(), CanonicalError> {
        let Some(text) = metadata.attributes.get(ATTRIBUTE) else {
            return Ok(());
        };
        let malformed = || CanonicalError::MalformedOperation("workspace context".to_owned());
        let namespace: Self = serde_json::from_str(text).map_err(|_| malformed())?;
        let key = |s: &str| !s.is_empty() && !s.contains(char::is_whitespace) && !s.contains('/');
        let distinct: BTreeSet<_> = namespace.names.values().collect();
        if !key(&namespace.source)
            || !namespace.known.contains(&namespace.source)
            || distinct.len() != namespace.names.len()
            || namespace.known.iter().any(|s| !key(s))
            || namespace.names.iter().any(|(name, qualified)| {
                !workspaces::split_key(qualified).is_some_and(|(machine, workspace)| {
                    key(machine)
                        && namespace.known.contains(machine)
                        && (machine != namespace.source || workspace == name)
                })
            })
        {
            return Err(malformed());
        }
        Ok(())
    }
}
