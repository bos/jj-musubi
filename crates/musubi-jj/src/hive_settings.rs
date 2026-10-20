//! Settings the whole hive shares that jj keeps outside its operations: git remote
//! definitions, and chosen keys of jj's repo config (docs/design.md, "Hive settings").
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

/// The repo config key that names more keys for the hive to share.
pub const SHARED_CONFIG_KEY: &str = "musubi.shared-config";

/// The repo config keys the hive shares whatever `musubi.shared-config` says: those that
/// decide what is safe to rewrite or push, which machines must agree on.
pub const SHARED_CONFIG: [&str; 4] = [
    r#"revset-aliases."immutable_heads()""#,
    r#"revset-aliases."trunk()""#,
    "git.private-commits",
    SHARED_CONFIG_KEY,
];

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct HiveSettings {
    /// Git remotes, by name.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub remotes: BTreeMap<String, Remote>,
    /// Shared repo config keys that are set, with their values as TOML (see
    /// [`normalize_value`]).
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub config: BTreeMap<String, String>,
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

    /// Merges three-way, remote by remote and key by key, as jj merges workspaces.
    pub fn merge(ours: &Self, base: &Self, theirs: &Self) -> Self {
        Self {
            remotes: merge_maps(&ours.remotes, &base.remotes, &theirs.remotes),
            config: merge_maps(&ours.config, &base.config, &theirs.config),
        }
    }

    /// The extra repo config keys these settings' `musubi.shared-config` names.
    pub fn extra_config_keys(&self) -> Vec<String> {
        self.config
            .get(SHARED_CONFIG_KEY)
            .map(|value| config_keys(value))
            .unwrap_or_default()
    }
}

fn merge_maps<T: Clone + Eq + std::hash::Hash>(
    ours: &BTreeMap<String, T>,
    base: &BTreeMap<String, T>,
    theirs: &BTreeMap<String, T>,
) -> BTreeMap<String, T> {
    let names: BTreeSet<&String> = ours
        .keys()
        .chain(base.keys())
        .chain(theirs.keys())
        .collect();
    names
        .into_iter()
        .filter_map(|name| {
            let value = merge_entry(ours.get(name), base.get(name), theirs.get(name))?;
            Some((name.clone(), value.clone()))
        })
        .collect()
}

/// A TOML value in canonical form, so that machines that write the same value differently
/// (with other quotes, say) agree on it. `None` if `text` isn't a TOML value.
pub fn normalize_value(text: &str) -> Option<String> {
    let table: toml::Table = toml::from_str(&format!("v = {text}")).ok()?;
    Some(table.get("v")?.to_string())
}

/// The keys a `musubi.shared-config` value, an array of strings, names.
pub fn config_keys(value: &str) -> Vec<String> {
    let Ok(table) = toml::from_str::<toml::Table>(&format!("v = {value}")) else {
        return vec![];
    };
    table
        .get("v")
        .and_then(toml::Value::as_array)
        .map(|keys| {
            keys.iter()
                .filter_map(toml::Value::as_str)
                .map(str::to_owned)
                .collect()
        })
        .unwrap_or_default()
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use super::*;

    fn with(remotes: &[(&str, &str)]) -> HiveSettings {
        HiveSettings {
            config: BTreeMap::new(),
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
    fn normalizes_values() {
        assert_eq!(normalize_value("'main'"), normalize_value(r#""main""#));
        assert_eq!(
            normalize_value("[ 'a', \"b\" ]"),
            normalize_value(r#"["a", "b"]"#)
        );
        assert_eq!(normalize_value("not toml"), None);
        assert_eq!(
            config_keys(r#"["aliases.x", 'ui.y']"#),
            ["aliases.x", "ui.y"]
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
