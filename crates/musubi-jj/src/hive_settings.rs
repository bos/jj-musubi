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
use crate::remote_url::RemoteUrl;

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

    /// These settings with each URL that names the repository `hive`'s URL for the same
    /// remote names spelled as `hive` spells it. A machine's own spelling of a shared remote,
    /// over another transport, say, is its own business, not a change for the hive.
    pub fn in_terms_of(&self, hive: &Self) -> Self {
        let mut ours = self.clone();
        for (name, remote) in &mut ours.remotes {
            if let Some(theirs) = hive.remotes.get(name) {
                if same_url(remote.url.as_deref(), theirs.url.as_deref()) {
                    remote.url.clone_from(&theirs.url);
                }
                // A push URL naming the repository the URL names is only spelling too.
                if same_url(remote.push_target(), theirs.push_target()) {
                    remote.push_url.clone_from(&theirs.push_url);
                }
            }
        }
        ours
    }

    /// The extra repo config keys these settings' `musubi.shared-config` names.
    pub fn extra_config_keys(&self) -> Vec<String> {
        self.config
            .get(SHARED_CONFIG_KEY)
            .map(|value| config_keys(value))
            .unwrap_or_default()
    }
}

impl Remote {
    /// Where pushes go: the push URL, or else the URL.
    fn push_target(&self) -> Option<&str> {
        self.push_url.as_deref().or(self.url.as_deref())
    }
}

fn same_url(a: Option<&str>, b: Option<&str>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(a), Some(b)) => {
            a == b
                || matches!(
                    (RemoteUrl::parse(a), RemoteUrl::parse(b)),
                    (Some(a), Some(b)) if a.key() == b.key()
                )
        }
        _ => false,
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
    fn a_remote_spelled_otherwise_is_no_change() {
        let hive = with(&[
            ("origin", "https://example.com/team/project.git"),
            ("x", "a"),
        ]);
        let ours = with(&[("origin", "git@example.com:team/project"), ("x", "b")]);
        assert_eq!(
            ours.in_terms_of(&hive),
            with(&[
                ("origin", "https://example.com/team/project.git"),
                ("x", "b")
            ])
        );
        // A remote the hive doesn't have is left alone.
        let only_ours = with(&[("mine", "git@example.com:team/mine")]);
        assert_eq!(only_ours.in_terms_of(&hive), only_ours);
        // Push URLs too, each URL on its own: one naming the repository the URL names is
        // spelling, and one naming another isn't.
        let remote = |url: &str, push_url: Option<&str>| HiveSettings {
            config: BTreeMap::new(),
            remotes: BTreeMap::from([(
                "origin".to_owned(),
                Remote {
                    url: Some(url.to_owned()),
                    push_url: push_url.map(str::to_owned),
                },
            )]),
        };
        let https = "https://example.com/p";
        let ssh = "git@example.com:p";
        let hive = remote(https, None);
        assert_eq!(remote(https, Some(ssh)).in_terms_of(&hive), hive);
        assert_eq!(remote(ssh, Some(ssh)).in_terms_of(&hive), hive);
        let elsewhere = "git@example.com:q";
        assert_eq!(
            remote(ssh, Some(elsewhere)).in_terms_of(&hive),
            remote(https, Some(elsewhere))
        );
        assert_eq!(
            remote(ssh, None).in_terms_of(&remote(https, Some(elsewhere))),
            remote(https, None)
        );
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
