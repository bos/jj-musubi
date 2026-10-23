//! Settings the whole hive shares that jj keeps outside its operations: git remote
//! definitions, and chosen keys of jj's repo config (docs/design.md, "Hive settings").
//!
//! Remote bookmarks replicate with the view, but which remotes exist, and where they point,
//! is in each machine's git config. So musubi records the hive's settings in an attribute
//! of an operation it makes whenever they change, and replicates them like any operation.
//! Each setting carries the time it was written, by the writing machine's clock, and where
//! machines disagree, the later write wins (docs/design.md, "Recording and merging"). Clock
//! skew can make the wrong one win; that is accepted, for a rule anyone can predict.

use std::collections::BTreeMap;

use serde::Deserialize;
use serde::Serialize;

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

/// The hive's settings: each remote and shared config key, with when it was last written.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(from = "Wire", into = "Wire")]
pub struct HiveSettings {
    /// Git remotes, by name.
    pub remotes: BTreeMap<String, Entry<Remote>>,
    /// Shared repo config keys, with their values as TOML (see [`normalize_value`]).
    pub config: BTreeMap<String, Entry<String>>,
}

/// One setting: its value, or that it was removed, and when it was written.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry<T> {
    pub value: Option<T>,
    pub stamp: Stamp,
}

/// When a setting was written, and by which machine.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Stamp {
    /// Milliseconds since the epoch, by the writer's clock. Zero in settings recorded
    /// before writes were timed, until [`HiveSettings::date_untimed`] dates them.
    pub time: i64,
    /// The writer's machine key, which breaks ties.
    pub machine: String,
}

/// Settings as one machine has them: the remotes and shared config keys that are set.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SettingValues {
    pub remotes: BTreeMap<String, Remote>,
    pub config: BTreeMap<String, String>,
}

/// A git remote's URLs: as written, and as the writing machine's git expands them through
/// its `url.<base>.insteadOf` rules, where that differs, since another machine needn't have
/// the same rules.
///
/// Two remotes are equal when they share a repository, however their URLs are spelled: by
/// [`RemoteUrl::key`], as written or as expanded, of the URL, and of the push target (the
/// push URL, or else the URL). So settings merge, and changes are noticed, by
/// where remotes point, and a machine's own spelling of a shared remote, over https on one
/// machine and ssh on another, say, or through an alias, is never a change.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Remote {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub url: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub push_url: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expanded_url: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expanded_push_url: Option<String>,
}

impl HiveSettings {
    pub fn parse(text: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(text)
    }

    /// The attribute's value: deterministic, since maps serialize in key order.
    pub fn to_attribute(&self) -> String {
        serde_json::to_string(self).expect("settings serialize")
    }

    /// Dates the settings that were recorded without a time with `time`: the time of the
    /// operation that recorded them.
    pub fn date_untimed(&mut self, time: i64) {
        let stamps = self
            .remotes
            .values_mut()
            .map(|entry| &mut entry.stamp)
            .chain(self.config.values_mut().map(|entry| &mut entry.stamp));
        for stamp in stamps {
            if stamp.time == 0 {
                stamp.time = time;
            }
        }
    }

    /// Whether every setting has a time: none was recorded before writes were timed.
    pub fn is_timed(&self) -> bool {
        self.remotes
            .values()
            .map(|entry| &entry.stamp)
            .chain(self.config.values().map(|entry| &entry.stamp))
            .all(|stamp| stamp.time != 0)
    }

    /// Combines two sets of settings, setting by setting: the later write wins.
    pub fn merge(a: &Self, b: &Self) -> Self {
        Self {
            remotes: merge_maps(&a.remotes, &b.remotes),
            config: merge_maps(&a.config, &b.config),
        }
    }

    /// These settings without the removed ones.
    pub fn without_removed(&self) -> Self {
        fn present<T: Clone>(entries: &BTreeMap<String, Entry<T>>) -> BTreeMap<String, Entry<T>> {
            entries
                .iter()
                .filter(|(_, entry)| entry.value.is_some())
                .map(|(name, entry)| (name.clone(), entry.clone()))
                .collect()
        }
        Self {
            remotes: present(&self.remotes),
            config: present(&self.config),
        }
    }

    /// The settings' values, without the removed ones.
    pub fn values(&self) -> SettingValues {
        fn present<T: Clone>(entries: &BTreeMap<String, Entry<T>>) -> BTreeMap<String, T> {
            entries
                .iter()
                .filter_map(|(name, entry)| Some((name.clone(), entry.value.clone()?)))
                .collect()
        }
        SettingValues {
            remotes: present(&self.remotes),
            config: present(&self.config),
        }
    }
}

impl SettingValues {
    /// The extra repo config keys these settings' `musubi.shared-config` names.
    pub fn extra_config_keys(&self) -> Vec<String> {
        self.config
            .get(SHARED_CONFIG_KEY)
            .map(|value| config_keys(value))
            .unwrap_or_default()
    }
}

impl Remote {
    /// The URL, as expanded, and so naming a real host, and as written.
    pub fn urls(&self) -> impl Iterator<Item = &str> {
        self.expanded_url
            .iter()
            .chain(&self.url)
            .map(String::as_str)
    }

    /// The repositories the URL names, as written and as expanded.
    pub fn url_repositories(&self) -> Vec<String> {
        self.urls().map(repository).collect()
    }

    /// The repositories pushes go to: the push URL's, or else the URL's.
    pub fn push_repositories(&self) -> Vec<String> {
        let push: Vec<String> = self
            .push_url
            .iter()
            .chain(&self.expanded_push_url)
            .map(|url| repository(url))
            .collect();
        if push.is_empty() {
            self.url_repositories()
        } else {
            push
        }
    }
}

/// Whether two remotes' URLs name the same repository, as written or as expanded; no URL is
/// the same only as no URL.
pub fn same_repository(a: &[String], b: &[String]) -> bool {
    if a.is_empty() || b.is_empty() {
        a.is_empty() && b.is_empty()
    } else {
        a.iter().any(|repository| b.contains(repository))
    }
}

impl PartialEq for Remote {
    fn eq(&self, other: &Self) -> bool {
        same_repository(&self.url_repositories(), &other.url_repositories())
            && same_repository(&self.push_repositories(), &other.push_repositories())
    }
}

/// Not transitive: `a` and `c` can each share a repository with `b`, as written and as
/// expanded, but not with each other. Only pairs are ever compared.
impl Eq for Remote {}

/// What identifies the repository `url` names: its [`RemoteUrl::key`], or the URL itself if
/// it doesn't parse.
pub fn repository(url: &str) -> String {
    RemoteUrl::parse(url).map_or_else(|| url.to_owned(), |url| url.key())
}

fn merge_maps<T: Clone>(
    a: &BTreeMap<String, Entry<T>>,
    b: &BTreeMap<String, Entry<T>>,
) -> BTreeMap<String, Entry<T>> {
    let mut merged = a.clone();
    for (name, theirs) in b {
        match merged.get(name) {
            Some(ours) if ours.stamp >= theirs.stamp => {}
            _ => {
                merged.insert(name.clone(), theirs.clone());
            }
        }
    }
    merged
}

/// The attribute as written: each remote's URLs, or `removed`, and each config key's value,
/// with when and by whom it was written. Settings recorded before writes were timed have no
/// time, and config values that are bare strings.
#[derive(Default, Serialize, Deserialize)]
struct Wire {
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    remotes: BTreeMap<String, WireRemote>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    config: BTreeMap<String, WireConfig>,
}

#[derive(Serialize, Deserialize)]
struct WireRemote {
    /// First, so that its fields come first, as they always have: a canonical operation's
    /// id is a hash of the attribute this is in.
    #[serde(flatten)]
    remote: Remote,
    #[serde(default, skip_serializing_if = "is_false")]
    removed: bool,
    #[serde(default, skip_serializing_if = "is_zero")]
    time: i64,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    machine: String,
}

#[derive(Serialize, Deserialize)]
#[serde(untagged)]
enum WireConfig {
    Untimed(String),
    Timed {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        value: Option<String>,
        time: i64,
        machine: String,
    },
}

fn is_false(value: &bool) -> bool {
    !value
}

fn is_zero(value: &i64) -> bool {
    *value == 0
}

impl From<Wire> for HiveSettings {
    fn from(wire: Wire) -> Self {
        let remotes = wire
            .remotes
            .into_iter()
            .map(|(name, remote)| {
                let value = (!remote.removed).then_some(remote.remote);
                let stamp = Stamp {
                    time: remote.time,
                    machine: remote.machine,
                };
                (name, Entry { value, stamp })
            })
            .collect();
        let config = wire
            .config
            .into_iter()
            .map(|(key, config)| {
                let entry = match config {
                    WireConfig::Untimed(value) => Entry {
                        value: Some(value),
                        stamp: Stamp::default(),
                    },
                    WireConfig::Timed {
                        value,
                        time,
                        machine,
                    } => Entry {
                        value,
                        stamp: Stamp { time, machine },
                    },
                };
                (key, entry)
            })
            .collect();
        Self { remotes, config }
    }
}

impl From<HiveSettings> for Wire {
    fn from(settings: HiveSettings) -> Self {
        let remotes = settings
            .remotes
            .into_iter()
            .map(|(name, entry)| {
                let removed = entry.value.is_none();
                let wire = WireRemote {
                    remote: entry.value.unwrap_or_default(),
                    removed,
                    time: entry.stamp.time,
                    machine: entry.stamp.machine,
                };
                (name, wire)
            })
            .collect();
        let config = settings
            .config
            .into_iter()
            .map(|(key, entry)| {
                let wire = WireConfig::Timed {
                    value: entry.value,
                    time: entry.stamp.time,
                    machine: entry.stamp.machine,
                };
                (key, wire)
            })
            .collect();
        Self { remotes, config }
    }
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

    /// Remotes, each at a URL or removed, all written at `time` by `machine`.
    fn with(time: i64, machine: &str, remotes: &[(&str, Option<&str>)]) -> HiveSettings {
        HiveSettings {
            config: BTreeMap::new(),
            remotes: remotes
                .iter()
                .map(|(name, url)| {
                    let entry = Entry {
                        value: url.map(|url| Remote {
                            url: Some(url.to_owned()),
                            ..Remote::default()
                        }),
                        stamp: Stamp {
                            time,
                            machine: machine.to_owned(),
                        },
                    };
                    ((*name).to_owned(), entry)
                })
                .collect(),
        }
    }

    #[test]
    fn remotes_are_equal_when_they_name_the_same_repositories() {
        let remote = |url: Option<&str>, push_url: Option<&str>| Remote {
            url: url.map(str::to_owned),
            push_url: push_url.map(str::to_owned),
            ..Remote::default()
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
        // An alias, as written or as expanded, names the repository its expansion does.
        let alias = Remote {
            url: Some("gh:team/p".to_owned()),
            expanded_url: ssh.map(str::to_owned),
            ..Remote::default()
        };
        assert_eq!(alias, remote(https, None));
        assert_eq!(alias, remote(Some("gh:team/p"), None));
        assert_ne!(alias, remote(other, None));
    }

    #[test]
    fn the_later_write_wins() {
        let alpha = with(
            1,
            "alpha",
            &[
                ("origin", Some("a")),
                ("old", Some("x")),
                ("mine", Some("m")),
            ],
        );
        let beta = with(2, "beta", &[("origin", Some("b")), ("old", None)]);
        let merged = with(2, "beta", &[("origin", Some("b")), ("old", None)]);
        let mut expected = merged.clone();
        expected
            .remotes
            .insert("mine".to_owned(), alpha.remotes["mine"].clone());
        assert_eq!(HiveSettings::merge(&alpha, &beta), expected);
        assert_eq!(HiveSettings::merge(&beta, &alpha), expected);
        assert_eq!(
            expected.values().remotes.keys().collect::<Vec<_>>(),
            ["mine", "origin"]
        );
        // Equal times go to the machine whose key sorts last.
        let gamma = with(2, "gamma", &[("origin", Some("c"))]);
        for merged in [
            HiveSettings::merge(&beta, &gamma),
            HiveSettings::merge(&gamma, &beta),
        ] {
            assert_eq!(merged.remotes["origin"], gamma.remotes["origin"]);
        }
    }

    #[test]
    fn untimed_settings_take_their_operations_time() {
        let mut settings = HiveSettings::parse(
            r#"{"remotes":{"origin":{"url":"https://example.com/r.git"}},"config":{"k":"1"}}"#,
        )
        .unwrap();
        settings.date_untimed(42);
        assert_eq!(settings.remotes["origin"].stamp.time, 42);
        assert_eq!(settings.config["k"].stamp.time, 42);
        assert_eq!(settings.config["k"].value.as_deref(), Some("1"));
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
        // Compared as written: remotes' equality ignores spelling, the attribute doesn't.
        let mut settings = with(
            7,
            "alpha",
            &[("origin", Some("git@example.com:repo.git")), ("gone", None)],
        );
        settings.config.insert(
            "k".to_owned(),
            Entry {
                value: Some("1".to_owned()),
                stamp: Stamp {
                    time: 8,
                    machine: "beta".to_owned(),
                },
            },
        );
        let attribute = settings.to_attribute();
        let parsed = HiveSettings::parse(&attribute).unwrap();
        assert_eq!(parsed, settings);
        assert_eq!(parsed.to_attribute(), attribute);
    }

    /// The attribute is written exactly as it always has been: canonical operation ids are
    /// hashes of it.
    #[test]
    fn the_attribute_is_as_it_was() {
        let stamp = Stamp {
            time: 7,
            machine: "alpha#0".to_owned(),
        };
        let remote = |url: &str| Remote {
            url: Some(url.to_owned()),
            ..Remote::default()
        };
        let full = Remote {
            push_url: Some("p".to_owned()),
            expanded_url: Some("eu".to_owned()),
            expanded_push_url: Some("ep".to_owned()),
            ..remote("u")
        };
        let mut settings = HiveSettings::default();
        for (name, value, stamp) in [
            ("bare", Some(remote("u")), Stamp::default()),
            ("full", Some(full), stamp.clone()),
            ("gone", None, stamp),
        ] {
            settings
                .remotes
                .insert(name.to_owned(), Entry { value, stamp });
        }
        assert_eq!(
            settings.to_attribute(),
            r#"{"remotes":{"bare":{"url":"u"},"full":{"url":"u","push_url":"p","expanded_url":"eu","expanded_push_url":"ep","time":7,"machine":"alpha#0"},"gone":{"removed":true,"time":7,"machine":"alpha#0"}}}"#
        );
    }
}
