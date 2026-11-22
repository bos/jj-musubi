//! Names of workspaces as one machine gave them, by the machine-qualified keys they stand for:
//! the form of `musubi.local-workspaces`, which a realization records of this machine's own
//! (`node::view::record_private_workspaces`), and of `musubi.workspace-context`. An earlier
//! release recorded the latter on canonical operations where `jj op abandon` had trimmed their
//! history away. Nothing writes or reads it now, but it is part of the operations that carry
//! it, and of their ids, for as long as their hives last, so imports still accept it, checking
//! only that it is well formed, as they did.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use jj_lib::op_store::OperationMetadata;
use serde::Deserialize;
use serde::Serialize;

use super::CanonicalError;
use crate::workspaces;

const ATTRIBUTE: &str = "musubi.workspace-context";

/// Literal names apply only on `source`. Canonical views, rather than these names, carry
/// the resulting bindings to other machines.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct Namespace {
    pub source: String,
    pub names: BTreeMap<String, String>,
    pub known: BTreeSet<String>,
}

impl Namespace {
    /// Refuses an operation whose `musubi.workspace-context` isn't one an earlier release
    /// could have written.
    pub fn check(metadata: &OperationMetadata) -> Result<(), CanonicalError> {
        Self::read_attribute(metadata, ATTRIBUTE).map(|_| ())
    }

    pub fn read_attribute(
        metadata: &OperationMetadata,
        attribute: &str,
    ) -> Result<Option<Self>, CanonicalError> {
        let Some(text) = metadata.attributes.get(attribute) else {
            return Ok(None);
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
        Ok(Some(namespace))
    }

    pub fn encode(&self) -> String {
        // Every field has a string representation in JSON.
        serde_json::to_string(self).expect("workspace context contains strings only")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The serialized text is part of the identities of operations that carry it.
    #[test]
    fn workspace_context_encoding_is_pinned() {
        let namespace = Namespace {
            source: "alpha#aaaa".to_owned(),
            names: BTreeMap::from([
                ("default".to_owned(), "alpha#aaaa/default".to_owned()),
                ("beta/default".to_owned(), "beta#bbbb/default".to_owned()),
            ]),
            known: BTreeSet::from(["alpha#aaaa".to_owned(), "beta#bbbb".to_owned()]),
        };
        assert_eq!(
            namespace.encode(),
            concat!(
                r#"{"source":"alpha#aaaa","names":{"beta/default":"beta#bbbb/default","#,
                r#""default":"alpha#aaaa/default"},"known":["alpha#aaaa","beta#bbbb"]}"#,
            )
        );
    }
}
