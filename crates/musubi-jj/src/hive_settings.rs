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
///
/// Two remotes are equal when they name the same repositories, however their URLs are
/// spelled: the URL's [`RemoteUrl::key`], and the push target's (the push URL, or else the
/// URL). So settings merge, and changes are noticed, by where remotes point, and a machine's
/// own spelling of a shared remote, over https on one machine and ssh on another, say, is
/// never a change. The strings are kept as they were written, for machines that need them.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
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

impl Remote {
    /// The repository the URL names.
    pub fn url_repository(&self) -> Option<String> {
        self.url.as_deref().map(repository)
    }

    /// The repository pushes go to: the push URL's, or else the URL's.
    pub fn push_repository(&self) -> Option<String> {
        self.push_url
            .as_deref()
            .or(self.url.as_deref())
            .map(repository)
    }
}

impl PartialEq for Remote {
    fn eq(&self, other: &Self) -> bool {
        self.url_repository() == other.url_repository()
            && self.push_repository() == other.push_repository()
    }
}

impl Eq for Remote {}

impl std::hash::Hash for Remote {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.url_repository().hash(state);
        self.push_repository().hash(state);
    }
}

/// What identifies the repository `url` names: its [`RemoteUrl::key`], or the URL itself if
/// it doesn't parse.
pub fn repository(url: &str) -> String {
    RemoteUrl::parse(url).map_or_else(|| url.to_owned(), |url| url.key())
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
    fn remotes_are_equal_when_they_name_the_same_repositories() {
        let remote = |url: Option<&str>, push_url: Option<&str>| Remote {
            url: url.map(str::to_owned),
            push_url: push_url.map(str::to_owned),
        };
        let https = Some("https://example.com/team/p.git");
        let ssh = Some("git@example.com:team/p");
        let other = Some("git@example.com:team/q");
        assert_eq!(remote(https, None), remote(ssh, None));
        // A push URL to where the URL points is only spelling.
        assert_eq!(remote(https, ssh), remote(ssh, None));
        assert_eq!(remote(https, None), remote(https, https));
        assert_ne!(remote(https, other), remote(https, None));
        assert_ne!(remote(https, None), remote(other, None));
        // Pushing to the repository the URL names, but with no URL, isn't fetching from it.
        assert_ne!(remote(None, https), remote(https, None));
        assert_eq!(remote(None, None), Remote::default());
        // Unparsed URLs compare as written.
        assert_eq!(remote(Some(" "), None), remote(Some(" "), None));
        let hash = |remote: &Remote| {
            use std::hash::Hash as _;
            use std::hash::Hasher as _;
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            remote.hash(&mut hasher);
            hasher.finish()
        };
        assert_eq!(hash(&remote(https, ssh)), hash(&remote(ssh, None)));
        // So merging three-way, a machine's own spelling is no change of its own.
        let hive = with(&[("origin", "https://example.com/team/p.git")]);
        let ours = with(&[("origin", "git@example.com:team/p")]);
        let theirs = with(&[("origin", "https://example.com/team/moved.git")]);
        let merged = HiveSettings::merge(&ours, &hive, &theirs);
        assert_eq!(merged.remotes["origin"].url, theirs.remotes["origin"].url);
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
