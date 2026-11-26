//! A copy's name in the hive (docs/internals/design.md, "Machine names"): the name its
//! workspaces are shown under. Its key embeds the name it joined under; from then on, its
//! daemon records the name `musubi.machine-name` sets, whenever that differs from the copy's
//! name in the hive, as an operation that is the copy's work (`crate::presence::NAME_ATTRIBUTE`).

use jj_lib::config::ConfigNamePathBuf;
use jj_lib::config::ConfigSource;
use pollster::FutureExt as _;

use super::NodeError;
use super::NodeRepo;
use crate::op_id::LocalOp;
use crate::presence::NAME_ATTRIBUTE;
use crate::presence::WORK_ATTRIBUTE;
use crate::workspaces;

/// The jj config key for the name this machine's copies have in their hives. Read only from
/// a machine's config, not a repository's or a workspace's: one setting names every copy on
/// the machine.
pub const MACHINE_NAME_KEY: &str = "musubi.machine-name";

/// `musubi.machine-name` as `config` sets it outside any repository, as `workspaces::sanitize`
/// makes it: none if no layer but a repository's or a workspace's sets it. A value that isn't
/// a string is taken for unset, with a warning.
pub fn configured_machine_name(config: &jj_lib::config::StackedConfig) -> Option<String> {
    let name: ConfigNamePathBuf = MACHINE_NAME_KEY.parse().expect("a valid config name");
    for layer in config.layers().iter().rev() {
        if matches!(layer.source, ConfigSource::Repo | ConfigSource::Workspace) {
            continue;
        }
        match layer.look_up_item(&name) {
            Ok(Some(item)) => {
                if let Some(text) = item.as_str() {
                    return Some(workspaces::sanitize(text));
                }
                tracing::warn!("{MACHINE_NAME_KEY} isn't a string; leaving the name as it is");
                return None;
            }
            _ => continue,
        }
    }
    None
}

impl NodeRepo {
    /// This copy's name in the hive as of its (merged) op head: the one it last recorded,
    /// else the one its key embeds.
    pub fn name_in_history(&mut self) -> Result<String, NodeError> {
        let (_, presence) = self.present_copies()?;
        Ok(presence.name(self.machine.key()).to_owned())
    }

    /// Records this copy's name in the hive as `musubi.machine-name` sets it, if that isn't
    /// its name there now: an operation that is this copy's work, and changes nothing else.
    /// Writes nothing where the setting is unset, so a copy keeps the name it has, nor while
    /// the hive has forgotten the copy: the record, being work, would bring it back, as a
    /// setting changed for the machine's other repos shouldn't. The copy records it once its
    /// own work brings it back. Returns whether it wrote one.
    pub fn record_name(&mut self) -> Result<bool, NodeError> {
        let Some(configured) = configured_machine_name(self.loader.settings().config()) else {
            return Ok(false);
        };
        let repo = self.merged_repo()?;
        let canonical = self.canonicalize(&LocalOp(repo.op_id().clone()))?;
        let presence = self.presence(&canonical)?;
        let key = self.machine.key().to_owned();
        if !presence.is_present(&key) || presence.name(&key) == configured {
            return Ok(false);
        }
        let mut tx = repo.start_transaction();
        tx.set_attribute(WORK_ATTRIBUTE.to_owned(), key);
        tx.set_attribute(NAME_ATTRIBUTE.to_owned(), configured.clone());
        tx.commit(format!("musubi: name this machine {configured}"))
            .block_on()?;
        Ok(true)
    }
}
