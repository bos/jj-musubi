//! Settings the whole hive shares that jj keeps outside its operations: git remote
//! definitions (docs/design.md, "Hive settings").
//!
//! Remote bookmarks replicate with the view, but which remotes exist, and where they point,
//! is in each machine's git config. So musubi records the hive's settings in an attribute
//! of an operation it makes whenever they change, and replicates them like any operation:
//! ordered by the hub, and merged three-way, entry by entry, where operations ran
//! concurrently.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use serde::Deserialize;
use serde::Serialize;

use crate::merge::merge_entry;

/// The operation attribute that records the hive's settings.
pub const ATTRIBUTE: &str = "musubi.settings";

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct HiveSettings {
    /// Git remotes, by name.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub remotes: BTreeMap<String, Remote>,
}

/// A git remote's URLs.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Remote {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub url: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub push_url: Option<String>,
}

impl HiveSettings {
    pub fn parse(text: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(text)
    }

    /// The attribute's value: deterministic, since maps serialize in key order.
    pub fn to_attribute(&self) -> String {
        serde_json::to_string(self).expect("settings serialize")
    }

    /// Merges three-way, remote by remote, as jj merges workspaces.
    pub fn merge(ours: &Self, base: &Self, theirs: &Self) -> Self {
        let names: BTreeSet<&String> = ours
            .remotes
            .keys()
            .chain(base.remotes.keys())
            .chain(theirs.remotes.keys())
            .collect();
        let remotes = names
            .into_iter()
            .filter_map(|name| {
                let remote = merge_entry(
                    ours.remotes.get(name),
                    base.remotes.get(name),
                    theirs.remotes.get(name),
                )?;
                Some((name.clone(), remote.clone()))
            })
            .collect();
        Self { remotes }
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use super::*;

    fn with(remotes: &[(&str, &str)]) -> HiveSettings {
        HiveSettings {
            remotes: remotes
                .iter()
                .map(|(name, url)| {
                    (
                        (*name).to_owned(),
                        Remote {
                            url: Some((*url).to_owned()),
                            push_url: None,
                        },
                    )
                })
                .collect(),
        }
    }

    #[test]
    fn merges_remote_by_remote() {
        let base = with(&[("origin", "a"), ("old", "x")]);
        let ours = with(&[("origin", "b"), ("old", "x"), ("mine", "m")]);
        let theirs = with(&[("origin", "a"), ("theirs", "t")]);
        let merged = HiveSettings::merge(&ours, &base, &theirs);
        assert_eq!(
            merged,
            with(&[("origin", "b"), ("mine", "m"), ("theirs", "t")])
        );
    }

    #[test]
    fn round_trips_through_the_attribute() {
        let settings = with(&[("origin", "git@example.com:repo.git")]);
        assert_eq!(
            HiveSettings::parse(&settings.to_attribute()).unwrap(),
            settings
        );
    }
}
