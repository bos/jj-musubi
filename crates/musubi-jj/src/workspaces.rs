//! Machine identity, and how each machine's workspaces appear to the others.
//!
//! Workspaces are per-machine (docs/design.md, "Per-machine state in a replicated view"), but
//! where each machine's working copies are is worth seeing. The canonical view records every
//! machine's workspaces under machine-qualified keys, `<machine>/<workspace>`. Each machine
//! shows the others' as workspaces of its own view, named after the machine, so `jj log`
//! shows beta's working copy as `beta/default@`. They are never git refs, so nothing git
//! does can touch them. jj moves them as it moves any workspace when it rewrites or abandons
//! their commits, and canonicalization takes those moves, but no other change a machine
//! makes to another machine's workspaces: adding, forgetting or renaming them stays local,
//! and the next realization shows them again.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;
use std::io;
use std::io::Write as _;
use std::path::Path;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::ref_name::WorkspaceNameBuf;
use jj_lib::settings::JJRng;

/// This machine's identity in the hive: a readable name plus a random suffix, `name#1a2b3c4d`,
/// so that two machines with the same hostname are never confused. Stored on first use,
/// because canonical operations embed it and must not change when recomputed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Machine {
    key: String,
}

impl Machine {
    /// The suffix comes from `rng`, jj's, which `debug.randomness-seed` makes repeatable, as
    /// it does jj's change ids: so a test that names two machines alike names them the same
    /// way every time it runs.
    pub fn load_or_create(path: &Path, default_name: &str, rng: &JJRng) -> io::Result<Self> {
        match fs::read_to_string(path) {
            Ok(key) if !key.trim().is_empty() => {
                return Ok(Self {
                    key: key.trim().to_owned(),
                });
            }
            Ok(_) => {}
            Err(err) if err.kind() == io::ErrorKind::NotFound => {}
            Err(err) => return Err(err),
        }
        let suffix = rng.new_change_id(4).hex();
        let key = format!("{}#{suffix}", sanitize(default_name));
        if let Some(dir) = path.parent() {
            fs::create_dir_all(dir)?;
        }
        let mut tmp = tempfile::NamedTempFile::new_in(path.parent().unwrap_or(Path::new(".")))?;
        tmp.write_all(key.as_bytes())?;
        tmp.persist(path).map_err(|err| err.error)?;
        Ok(Self { key })
    }

    pub fn key(&self) -> &str {
        &self.key
    }

    pub fn name(&self) -> &str {
        machine_name(&self.key)
    }
}

/// A name usable as a jj remote name and a git ref component.
pub fn sanitize(name: &str) -> String {
    let cleaned: String = name
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '-' || c == '_' {
                c
            } else {
                '-'
            }
        })
        .collect();
    let cleaned = cleaned.trim_matches('-').to_lowercase();
    if cleaned.is_empty() {
        "machine".to_owned()
    } else {
        cleaned
    }
}

/// The readable part of a machine key: `beta` of `beta#1a2b3c4d`.
pub fn machine_name(key: &str) -> &str {
    key.split_once('#').map_or(key, |(name, _)| name)
}

fn short_id(key: &str) -> &str {
    key.split_once('#')
        .map_or("", |(_, id)| &id[..id.len().min(4)])
}

/// The canonical key of `workspace` on `machine`.
pub fn workspace_key(machine: &str, workspace: &str) -> WorkspaceNameBuf {
    WorkspaceNameBuf::from(format!("{machine}/{workspace}"))
}

/// Splits a canonical workspace key into machine key and workspace name.
pub fn split_key(key: &str) -> Option<(&str, &str)> {
    key.split_once('/')
}

/// The names under which machines' workspaces are shown, as `<name>/<workspace>`: the
/// machine's name, or `name-1a2b` when two machines share a name or `taken` says the name
/// is in use.
pub fn display_names(
    machines: &BTreeSet<String>,
    taken: impl Fn(&str) -> bool,
) -> BTreeMap<String, String> {
    let mut by_name: BTreeMap<&str, usize> = BTreeMap::new();
    for machine in machines {
        *by_name.entry(machine_name(machine)).or_default() += 1;
    }
    machines
        .iter()
        .map(|machine| {
            let name = machine_name(machine);
            let display = if by_name[name] > 1 || taken(name) {
                format!("{name}-{}", short_id(machine))
            } else {
                name.to_owned()
            };
            (machine.clone(), display)
        })
        .collect()
}

/// Merges one workspace's working-copy commit three-way, as jj does.
pub fn merge_working_copy<'a>(
    ours: Option<&'a CommitId>,
    base: Option<&'a CommitId>,
    theirs: Option<&'a CommitId>,
) -> Option<&'a CommitId> {
    crate::merge::merge_entry(ours, base, theirs)
}

/// Moves working-copy commits along the rewrites an operation records: a commit rewritten
/// into several (divergent or split) is followed to the first of them.
pub fn follow_rewrites<K>(
    workspaces: &mut BTreeMap<K, CommitId>,
    predecessors: Option<&BTreeMap<CommitId, Vec<CommitId>>>,
) {
    let Some(predecessors) = predecessors else {
        return;
    };
    let mut successors: BTreeMap<&CommitId, &CommitId> = BTreeMap::new();
    for (new, olds) in predecessors {
        for old in olds {
            successors.entry(old).or_insert(new);
        }
    }
    for wc in workspaces.values_mut() {
        // Rewrites within one operation form chains; follow them to the end.
        let mut seen = BTreeSet::new();
        while let Some(&next) = successors.get(&*wc) {
            if !seen.insert(next.clone()) {
                break;
            }
            *wc = next.clone();
        }
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use std::sync::Arc;

    use jj_lib::config::ConfigLayer;
    use jj_lib::config::ConfigSource;
    use jj_lib::config::StackedConfig;
    use jj_lib::settings::UserSettings;

    use super::*;

    #[test]
    fn names_are_qualified_only_when_ambiguous() {
        let machines: BTreeSet<String> = [
            "beta#11112222",
            "mac#aaaa0000",
            "mac#bbbb0000",
            "git#cccc0000",
            "origin#dddd0000",
        ]
        .map(str::to_owned)
        .into();
        let names = display_names(&machines, |name| name == "origin");
        assert_eq!(names["beta#11112222"], "beta");
        assert_eq!(names["mac#aaaa0000"], "mac-aaaa");
        assert_eq!(names["mac#bbbb0000"], "mac-bbbb");
        assert_eq!(names["git#cccc0000"], "git");
        assert_eq!(names["origin#dddd0000"], "origin-dddd");
    }

    /// jj's RNG, as `debug.randomness-seed = seed` makes it.
    fn rng(seed: u64) -> Arc<JJRng> {
        let mut config = StackedConfig::with_defaults();
        let text = format!("debug.randomness-seed = {seed}");
        config.add_layer(ConfigLayer::parse(ConfigSource::User, &text).unwrap());
        UserSettings::from_config_and_home_dir(config, None)
            .unwrap()
            .get_rng()
    }

    #[test]
    fn identity_is_kept() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("machine");
        let first = Machine::load_or_create(&path, "Bryan's MacBook Pro", &rng(1)).unwrap();
        assert!(
            first.key().starts_with("bryan-s-macbook-pro#"),
            "{}",
            first.key()
        );
        let again = Machine::load_or_create(&path, "something else", &rng(2)).unwrap();
        assert_eq!(first, again);
    }

    /// The e2e search replays a case with machines named alike only if their suffixes come
    /// out the same again.
    #[test]
    fn a_seed_repeats_the_suffix() {
        let dir = tempfile::tempdir().unwrap();
        let key = |file: &str, seed| {
            let path = dir.path().join(file);
            Machine::load_or_create(&path, "mac", &rng(seed))
                .unwrap()
                .key
        };
        assert_eq!(key("a", 1), key("b", 1));
        assert_ne!(key("c", 1), key("d", 2));
    }
}
