//! The hive's settings: this machine's git remotes and shared repo config, reconciled with
//! the hive's (see docs/settings-merge.md).

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;
use std::io;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;

use jj_lib::config::ConfigFile;
use jj_lib::config::ConfigNamePathBuf;
use jj_lib::config::ConfigSource;
use jj_lib::config::ConfigValue;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use pollster::FutureExt as _;
use serde::Deserialize;
use serde::Serialize;

use super::NodeError;
use super::NodeRepo;
use crate::hive_settings;
use crate::hive_settings::Entry;
use crate::hive_settings::HiveSettings;
use crate::hive_settings::SettingValues;
use crate::hive_settings::Stamp;

/// The settings this machine and the hive agreed on when they were last reconciled.
#[derive(Serialize, Deserialize)]
struct SettingsState {
    /// A canonical operation at which the hive's settings were `hive`: the one this was last
    /// written at.
    op: String,
    /// The hive's settings there, if any machine had recorded some.
    hive: Option<HiveSettings>,
    /// The settings both had afterwards.
    settings: HiveSettings,
}

impl NodeRepo {
    /// The hive's settings as of a canonical operation: what its nearest recording
    /// ancestor recorded, combined where concurrent operations met, the later write to each
    /// setting winning, or `None` if no ancestor recorded any.
    fn settings_at(&mut self, op: &OperationId) -> Result<Option<HiveSettings>, NodeError> {
        let root = self.canonical.root_operation_id().clone();
        let mut stack = vec![op.clone()];
        while let Some(id) = stack.last().cloned() {
            if self.settings.contains_key(&id) {
                stack.pop();
                continue;
            }
            if id == root {
                self.settings.insert(id, None);
                stack.pop();
                continue;
            }
            let operation = self.canonical.read_operation(&id)?;
            if let Some(text) = operation.metadata.attributes.get(hive_settings::ATTRIBUTE) {
                let mut settings =
                    HiveSettings::parse(text).map_err(|err| NodeError::Settings {
                        op: id.hex(),
                        message: err.to_string(),
                    })?;
                settings.date_untimed(operation.metadata.time.end.timestamp.0);
                self.settings.insert(id, Some(settings));
                stack.pop();
                continue;
            }
            let missing: Vec<OperationId> = operation
                .parents
                .iter()
                .filter(|parent| !self.settings.contains_key(*parent))
                .cloned()
                .collect();
            if !missing.is_empty() {
                stack.extend(missing);
                continue;
            }
            let merged = operation
                .parents
                .iter()
                .filter_map(|parent| self.settings[parent].clone())
                .reduce(|a, b| HiveSettings::merge(&a, &b));
            self.settings.insert(id, merged);
            stack.pop();
        }
        Ok(self.settings[op].clone())
    }

    /// Brings this machine's settings and the hive's together: records this machine's
    /// changes for the hive, in an operation of its own, and applies the hive's here,
    /// setting by setting, the later write winning (docs/settings-merge.md). A setting
    /// that differs from what this machine last applied is a change, written when the file
    /// holding it was last modified. A machine reconciling for the first time takes the
    /// hive's value of every setting the hive has, and adds its own others. Remotes compare
    /// by the repositories they name ([`hive_settings::Remote`]), so a machine's own
    /// spelling of one is never a change. Returns whether it recorded a change, which then
    /// needs uploading.
    pub fn reconcile_settings(&mut self) -> Result<bool, NodeError> {
        let head = self.merge_heads()?;
        let canonical = self.canonicalize(&head)?;
        let state = self.read_settings_state()?;
        // A state from before writes were timed has no times to offer the cache.
        if let Some((op, hive, _)) = &state
            && hive.as_ref().is_none_or(HiveSettings::is_timed)
        {
            self.settings
                .entry(op.clone())
                .or_insert_with(|| hive.clone());
        }
        let hive = self.settings_at(&canonical)?;
        let current = hive.clone().unwrap_or_default();
        let mut extra = current.values().extra_config_keys();
        if let Some((_, _, applied)) = &state {
            extra.extend(applied.values().extra_config_keys());
        }
        let local = self.local_settings(&extra)?;
        let applied = state
            .as_ref()
            .map(|(_, _, applied)| applied.clone())
            .unwrap_or_default();
        let machine = self.machine.key().to_owned();
        let remotes_time = self.git.as_ref().map(|git| modified(&git.config_path()));
        let config_time = self.repo_config.as_deref().map(modified);
        let mut ours = HiveSettings {
            remotes: stamp_changes(&local.remotes, &applied.remotes, || Stamp {
                time: remotes_time.unwrap_or_else(now),
                machine: machine.clone(),
            }),
            config: stamp_changes(&local.config, &applied.config, || Stamp {
                time: config_time.unwrap_or_else(now),
                machine: machine.clone(),
            }),
        };
        // What this machine last applied before writes were timed has no time, so it loses
        // to the hive's value, and where the hive has none, the hive removed it.
        ours.remotes
            .retain(|name, entry| entry.stamp.time != 0 || current.remotes.contains_key(name));
        ours.config
            .retain(|key, entry| entry.stamp.time != 0 || current.config.contains_key(key));
        if state.is_none() {
            // Joining: the hive's values stand, whatever this machine has, but its own
            // others join them, however recently the hive removed one by that name.
            outlive_removals(&mut ours.remotes, &current.remotes);
            outlive_removals(&mut ours.config, &current.config);
            let present = current.without_removed();
            ours.remotes.extend(present.remotes);
            ours.config.extend(present.config);
        }
        let merged = HiveSettings::merge(&ours, &current);
        let (mut at, mut hive_now, mut recorded) = (canonical, hive, false);
        if merged != current {
            let op = self.record_settings(&head, &merged)?;
            at = self.canonicalize(&op)?;
            self.settings.insert(at.clone(), Some(merged.clone()));
            hive_now = Some(merged.clone());
            recorded = true;
        }
        let values = merged.values();
        if values != local {
            log_replaced(&local, &merged);
            self.apply_settings(&local, &values)?;
        }
        // The state names an operation only so that a restart's `settings_at` can stop
        // there, and any at which the hive had these settings will do, as it always will: so
        // it is written only when the settings change. Rewriting it for each new operation
        // would replace it at almost every sync, and ext4 writes out at once a file that
        // replaces another.
        let unchanged = state
            .as_ref()
            .is_some_and(|(_, hive, settings)| *hive == hive_now && *settings == merged);
        if !unchanged {
            self.write_settings_state(&SettingsState {
                op: at.hex(),
                hive: hive_now,
                settings: merged,
            })?;
        }
        Ok(recorded)
    }

    /// Whether this machine shares the credentials an http(s) remote URL may carry, as
    /// `musubi.share-credentials` in jj's config says; by default it doesn't.
    pub(super) fn share_credentials(&self) -> bool {
        self.loader
            .settings()
            .get_bool("musubi.share-credentials")
            .unwrap_or(false)
    }

    /// This machine's git remotes, if its backend is git.
    pub(super) fn remotes(&self) -> Result<BTreeMap<String, hive_settings::Remote>, NodeError> {
        Ok(match &self.git {
            Some(git) => git.remotes(self.share_credentials())?,
            None => BTreeMap::new(),
        })
    }

    /// The settings this machine has now: its git remotes, and the shared keys of its repo
    /// config, including `extra` keys.
    fn local_settings(&self, extra: &[String]) -> Result<SettingValues, NodeError> {
        Ok(SettingValues {
            remotes: self.remotes()?,
            config: self.read_shared_config(extra)?,
        })
    }

    fn apply_settings(&self, from: &SettingValues, to: &SettingValues) -> Result<(), NodeError> {
        if let Some(git) = &self.git {
            git.change_remotes(&from.remotes, &to.remotes)?;
        }
        self.write_shared_config(&from.config, &to.config)
    }

    fn repo_config_file(&self) -> Result<Option<ConfigFile>, NodeError> {
        let Some(path) = &self.repo_config else {
            return Ok(None);
        };
        ConfigFile::load_or_empty(ConfigSource::Repo, path)
            .map(Some)
            .map_err(|err| config_err(path, err))
    }

    /// The shared keys this machine's repo config sets: the default ones, those its own
    /// `musubi.shared-config` names, and `extra`.
    fn read_shared_config(&self, extra: &[String]) -> Result<BTreeMap<String, String>, NodeError> {
        let Some(file) = self.repo_config_file()? else {
            return Ok(BTreeMap::new());
        };
        let value_of = |key: &str| -> Option<String> {
            let name: ConfigNamePathBuf = key.parse().ok()?;
            let item = file.layer().look_up_item(&name).ok()??;
            hive_settings::normalize_value(&item.as_value()?.to_string())
        };
        let mut keys: BTreeSet<String> = hive_settings::SHARED_CONFIG
            .iter()
            .map(|key| (*key).to_owned())
            .chain(extra.iter().cloned())
            .collect();
        if let Some(value) = value_of(hive_settings::SHARED_CONFIG_KEY) {
            keys.extend(hive_settings::config_keys(&value));
        }
        Ok(keys
            .into_iter()
            .filter_map(|key| {
                let value = value_of(&key)?;
                Some((key, value))
            })
            .collect())
    }

    fn write_shared_config(
        &self,
        from: &BTreeMap<String, String>,
        to: &BTreeMap<String, String>,
    ) -> Result<(), NodeError> {
        if from == to {
            return Ok(());
        }
        let Some(mut file) = self.repo_config_file()? else {
            return Ok(());
        };
        let path = file.path().to_owned();
        let keys: BTreeSet<&String> = from.keys().chain(to.keys()).collect();
        for key in keys {
            if from.get(key) == to.get(key) {
                continue;
            }
            let name: ConfigNamePathBuf = key.parse().map_err(|err| config_err(&path, err))?;
            match to.get(key) {
                Some(text) => {
                    let value: ConfigValue = text.parse().map_err(|err| config_err(&path, err))?;
                    file.set_value(&name, value)
                        .map_err(|err| config_err(&path, err))?;
                }
                None => {
                    file.delete_value(&name)
                        .map_err(|err| config_err(&path, err))?;
                }
            }
        }
        file.save().map_err(|err| config_err(&path, err))
    }

    /// Writes an operation on top of `head` that changes nothing but records `settings`.
    fn record_settings(
        &self,
        head: &OperationId,
        settings: &HiveSettings,
    ) -> Result<OperationId, NodeError> {
        let repo = self.repo_at(head)?;
        let mut tx = repo.start_transaction();
        tx.set_attribute(hive_settings::ATTRIBUTE.to_owned(), settings.to_attribute());
        let repo = tx.commit("musubi: hive settings changed").block_on()?;
        Ok(repo.op_id().clone())
    }

    fn settings_state_path(&self) -> PathBuf {
        self.repo_path.join("musubi/settings.json")
    }

    /// Whether this machine has reconciled its settings with the hive's before.
    pub fn has_reconciled_settings(&self) -> bool {
        self.settings_state_path().exists()
    }

    fn read_settings_state(
        &self,
    ) -> Result<Option<(OperationId, Option<HiveSettings>, HiveSettings)>, NodeError> {
        let path = self.settings_state_path();
        let text = match fs::read_to_string(&path) {
            Ok(text) => text,
            Err(err) if err.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(source) => return Err(NodeError::Io { path, source }),
        };
        let state: SettingsState =
            serde_json::from_str(&text).map_err(|err| NodeError::Settings {
                op: path.display().to_string(),
                message: err.to_string(),
            })?;
        let op = OperationId::try_from_hex(&state.op).ok_or_else(|| NodeError::Settings {
            op: state.op.clone(),
            message: "not an operation id".to_owned(),
        })?;
        Ok(Some((op, state.hive, state.settings)))
    }

    fn write_settings_state(&self, state: &SettingsState) -> Result<(), NodeError> {
        let path = self.settings_state_path();
        let json = serde_json::to_vec_pretty(state).expect("settings serialize");
        let dir = path.parent().expect("path has a parent");
        let io_err = |source| NodeError::Io {
            path: path.clone(),
            source,
        };
        let mut tmp = tempfile::NamedTempFile::new_in(dir).map_err(io_err)?;
        tmp.write_all(&json).map_err(io_err)?;
        tmp.persist(&path).map_err(|err| io_err(err.error))?;
        Ok(())
    }
}

fn config_err(path: &Path, err: impl std::fmt::Display) -> NodeError {
    NodeError::Config {
        path: path.to_owned(),
        message: err.to_string(),
    }
}

/// This machine's settings as entries: as last applied where unchanged, and otherwise
/// written now, as `stamp` says, including removals.
fn stamp_changes<T: Clone + PartialEq>(
    local: &BTreeMap<String, T>,
    applied: &BTreeMap<String, Entry<T>>,
    stamp: impl Fn() -> Stamp,
) -> BTreeMap<String, Entry<T>> {
    let names: BTreeSet<&String> = local.keys().chain(applied.keys()).collect();
    names
        .into_iter()
        .filter_map(|name| {
            let value = local.get(name);
            match applied.get(name) {
                Some(entry) if entry.value.as_ref() == value => Some(entry.clone()),
                None if value.is_none() => None,
                _ => Some(Entry {
                    value: value.cloned(),
                    stamp: stamp(),
                }),
            }
            .map(|entry| (name.clone(), entry))
        })
        .collect()
}

/// Dates each of `ours` that `hive` removed later just after the removal, so that it stands.
fn outlive_removals<T>(ours: &mut BTreeMap<String, Entry<T>>, hive: &BTreeMap<String, Entry<T>>) {
    for (name, entry) in ours {
        if let Some(removal) = hive.get(name).filter(|theirs| theirs.value.is_none())
            && removal.stamp >= entry.stamp
        {
            entry.stamp.time = removal.stamp.time + 1;
        }
    }
}

/// When `path` was last modified, in milliseconds since the epoch, if it can tell.
fn modified(path: &Path) -> i64 {
    fs::metadata(path)
        .and_then(|metadata| metadata.modified())
        .map_or_else(|_| now(), millis)
}

fn now() -> i64 {
    millis(std::time::SystemTime::now())
}

fn millis(time: std::time::SystemTime) -> i64 {
    time.duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |since| {
            i64::try_from(since.as_millis()).unwrap_or(i64::MAX)
        })
}

/// Logs each setting whose value here the hive's replaces, and whose write replaced it.
fn log_replaced(local: &SettingValues, merged: &HiveSettings) {
    fn each<T: PartialEq + std::fmt::Debug>(
        kind: &str,
        local: &BTreeMap<String, T>,
        merged: &BTreeMap<String, Entry<T>>,
    ) {
        for (name, entry) in merged {
            let old = local.get(name);
            if old != entry.value.as_ref() {
                tracing::info!(
                    "{kind} {name}: {old:?} replaced by {:?}, written by {} at {}",
                    entry.value,
                    entry.stamp.machine,
                    entry.stamp.time
                );
            }
        }
    }
    each("remote", &local.remotes, &merged.remotes);
    each("config", &local.config, &merged.config);
}
