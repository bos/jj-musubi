//! Forgetting copies that go unused (docs/internals/design.md, "Copies that go unused"): each
//! copy records its `musubi.forget-after` in the history, and a daemon forgets a copy whose
//! latest work is older than that.

use std::collections::BTreeMap;
use std::time::Duration;
use std::time::SystemTime;

use jj_lib::config::ConfigNamePathBuf;
use jj_lib::config::ConfigSource;
use jj_lib::op_store::OperationId;
use pollster::FutureExt as _;

use super::NodeError;
use super::NodeRepo;
use crate::presence::FORGET_AFTER_ATTRIBUTE;
use crate::presence::Presence;
use crate::presence::WORK_ATTRIBUTE;
use crate::presence::format_forget_after;
use crate::presence::parse_forget_after;
use crate::workspaces;

/// The jj config key for how long a copy may go unused before a daemon forgets it.
pub const FORGET_AFTER_KEY: &str = "musubi.forget-after";

/// A copy present in the hive, as `musubi list` shows it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Activity {
    /// The copy's machine key.
    pub key: String,
    /// The machine's name as its workspaces are shown here.
    pub name: String,
    /// When it last worked, by the clock of the machine that did.
    pub last_work: SystemTime,
    /// How long it may go unused before a daemon forgets it, as it last recorded; `None`
    /// for never.
    pub forget_after: Option<Duration>,
}

impl NodeRepo {
    /// This copy's `musubi.forget-after` as jj's config sets it now, reading its repo config
    /// afresh: `None` for never, as when nothing sets it. A value that isn't one is taken
    /// for never, with a warning.
    pub fn configured_forget_after(&self) -> Result<Option<Duration>, NodeError> {
        let name: ConfigNamePathBuf = FORGET_AFTER_KEY.parse().expect("a valid config name");
        let look_up = |layer: &jj_lib::config::ConfigLayer| match layer.look_up_item(&name) {
            Ok(Some(item)) => Some(item.as_str().map(str::to_owned)),
            _ => None,
        };
        // jj's config as it was when the repository was opened, highest precedence first,
        // but for its repo config, which may have changed since, or been made, as by
        // `musubi join`: that is read afresh, where it ranks.
        let fresh_repo = || -> Result<Option<Option<String>>, NodeError> {
            Ok(self
                .repo_config_file()?
                .and_then(|file| look_up(file.layer())))
        };
        let mut text = None;
        let mut repo_read = false;
        for layer in self.loader.settings().config().layers().iter().rev() {
            if !repo_read && layer.source <= ConfigSource::Repo {
                repo_read = true;
                text = fresh_repo()?;
                if text.is_some() {
                    break;
                }
            }
            if matches!(layer.source, ConfigSource::Repo | ConfigSource::Default) {
                continue;
            }
            text = look_up(layer);
            if text.is_some() {
                break;
            }
        }
        if !repo_read {
            text = fresh_repo()?;
        }
        let Some(text) = text else {
            return Ok(None);
        };
        match text.as_deref().and_then(parse_forget_after) {
            Some(after) => Ok(after),
            None => {
                tracing::warn!(
                    "{FORGET_AFTER_KEY} is neither `never` nor a duration such as `6h`; taking \
                     it for never"
                );
                Ok(None)
            }
        }
    }

    /// Records this copy's `musubi.forget-after` in the hive, if it isn't what the copy last
    /// recorded, or, where it has recorded nothing, never: an operation that is this copy's
    /// work, and changes nothing else. Returns whether it wrote one.
    pub fn record_forget_after(&mut self) -> Result<bool, NodeError> {
        let configured = self.configured_forget_after()?;
        let repo = self.merged_repo()?;
        let canonical = self.canonicalize(repo.op_id())?;
        let presence = self.presence(&canonical)?;
        let key = self.machine.key().to_owned();
        if presence.forget_after(&key) == configured
            && (presence.has_forget_after(&key) || configured.is_none())
        {
            return Ok(false);
        }
        let mut tx = repo.start_transaction();
        tx.set_attribute(WORK_ATTRIBUTE.to_owned(), key);
        tx.set_attribute(
            FORGET_AFTER_ATTRIBUTE.to_owned(),
            format_forget_after(configured),
        );
        let description = match configured {
            Some(after) => format!(
                "musubi: forget this copy once unused for {}",
                format_forget_after(Some(after))
            ),
            None => "musubi: never forget this copy".to_owned(),
        };
        tx.commit(description).block_on()?;
        Ok(true)
    }

    /// Forgets each copy present in the hive, other than this one, that has gone unused for
    /// longer than its `musubi.forget-after` as of `now`, as `musubi forget` would, and
    /// returns their names. A copy's own `stagger`, up to that long, is added to the time, a
    /// different one on each machine, so that the machines seldom forget the same copy at
    /// once.
    pub fn expire_idle(
        &mut self,
        now: SystemTime,
        stagger: Duration,
    ) -> Result<Vec<String>, NodeError> {
        let mut due = vec![];
        for activity in self.activity()? {
            let Some(after) = activity.forget_after else {
                continue;
            };
            if activity.key == self.machine.key() {
                continue;
            }
            let offset = staggered(self.machine.key(), &activity.key, stagger);
            // A duration too long to add to a time is as good as never.
            let at = activity
                .last_work
                .checked_add(after)
                .and_then(|time| time.checked_add(offset));
            if at.is_some_and(|at| at <= now) {
                due.push(activity);
            }
        }
        let mut forgotten = vec![];
        for activity in due {
            if self.forget_copy(&activity.key, &activity.name)? {
                tracing::info!(
                    "forgot {}, unused since {:?}",
                    activity.name,
                    activity.last_work
                );
                forgotten.push(activity.name);
            }
        }
        Ok(forgotten)
    }

    /// Each copy present in the hive as of this machine's (merged) op head, this one
    /// included if it is: when it last worked, and how long it may go unused.
    pub fn activity(&mut self) -> Result<Vec<Activity>, NodeError> {
        let (canonical, presence) = self.present_copies()?;
        let names = self.shown_names(&canonical)?;
        let mut copies = vec![];
        for key in presence.copies() {
            let name = if key == self.machine.key() {
                self.machine.name().to_owned()
            } else {
                names
                    .get(key)
                    .cloned()
                    .unwrap_or_else(|| workspaces::machine_name(key).to_owned())
            };
            copies.push(Activity {
                key: key.to_owned(),
                name,
                last_work: self.last_work(&presence, key)?,
                forget_after: presence.forget_after(key),
            });
        }
        Ok(copies)
    }

    /// When a present copy last worked: the latest end of its latest work's operations.
    fn last_work(
        &self,
        presence: &Presence<OperationId>,
        copy: &str,
    ) -> Result<SystemTime, NodeError> {
        let mut last = SystemTime::UNIX_EPOCH;
        for op in presence.latest(copy).into_iter().flatten() {
            let millis = self
                .canonical
                .read_operation(op)?
                .metadata
                .time
                .end
                .timestamp
                .0;
            let time = SystemTime::UNIX_EPOCH + Duration::from_millis(millis.max(0).unsigned_abs());
            last = last.max(time);
        }
        Ok(last)
    }

    /// The name each other machine's workspaces are shown under here, by machine key.
    pub(super) fn shown_names(
        &self,
        canonical: &OperationId,
    ) -> Result<BTreeMap<String, String>, NodeError> {
        Ok(self
            .other_names(canonical)?
            .into_iter()
            .filter_map(|(local, key)| {
                let (machine, _) = workspaces::split_key(key.as_str())?;
                let (prefix, _) = local.as_str().split_once('/')?;
                Some((machine.to_owned(), prefix.to_owned()))
            })
            .collect())
    }
}

/// How much later than its `musubi.forget-after` the machine `own` forgets `copy`: up to
/// `stagger`, and the same each time, from a hash of the two.
fn staggered(own: &str, copy: &str, stagger: Duration) -> Duration {
    let secs = stagger.as_secs();
    if secs == 0 {
        return Duration::ZERO;
    }
    // FNV-1a, which needn't be the same on every machine, only on this one each time.
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in own.bytes().chain([0]).chain(copy.bytes()) {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0100_0000_01b3);
    }
    Duration::from_secs(hash % secs)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn staggering_stays_within_its_bound() {
        let bound = Duration::from_secs(300);
        let a = staggered("alpha#1", "beta#2", bound);
        assert!(a < bound);
        assert_eq!(a, staggered("alpha#1", "beta#2", bound));
        assert_eq!(
            staggered("alpha#1", "beta#2", Duration::ZERO),
            Duration::ZERO
        );
    }
}
