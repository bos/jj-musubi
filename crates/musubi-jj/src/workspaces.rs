//! Machine identity, and how each machine's workspaces appear to the others.
//!
//! Workspaces are per-machine (docs/design.md, "Per-machine state in a replicated view"), but
//! where each machine's working copies are is worth seeing. The canonical view records every
//! machine's workspaces under machine-qualified keys, `<machine>/<workspace>`. Each machine
//! writes only its own entries; every machine carries the others' along through rewrites.
//! A machine shows the other machines' workspaces as remote bookmarks of a pseudo-remote
//! named after the machine, so `jj log` labels beta's working copy `default@beta`. They are
//! tracked, since jj treats untracked remote bookmarks as immutable heads by default; with
//! no local bookmark of the same name, `jj bookmark list` shows them as deleted local
//! bookmarks. jj never creates or abandons commits for remote bookmarks, and moves them only
//! on fetch or import, which never involve these, so the labels are inert. The next
//! realization regenerates them and canonicalization strips them, so nothing done to them
//! locally reaches other machines.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;
use std::io;
use std::io::Write as _;
use std::path::Path;

use jj_lib::backend::CommitId;
use jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
use jj_lib::ref_name::WorkspaceNameBuf;

/// This machine's identity in the hive: a readable name plus a random suffix, `name#1a2b3c4d`,
/// so that two machines with the same hostname are never confused. Stored durably on first
/// use, because canonical operations embed it and must not change when recomputed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Machine {
    key: String,
}

impl Machine {
    pub fn load_or_create(path: &Path, default_name: &str) -> io::Result<Self> {
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
        let suffix: u32 = rand_suffix();
        let key = format!("{}#{suffix:08x}", sanitize(default_name));
        if let Some(dir) = path.parent() {
            fs::create_dir_all(dir)?;
        }
        let mut tmp = tempfile::NamedTempFile::new_in(path.parent().unwrap_or(Path::new(".")))?;
        tmp.write_all(key.as_bytes())?;
        tmp.as_file().sync_all()?;
        tmp.persist(path).map_err(|err| err.error)?;
        Ok(Self { key })
    }

    pub fn key(&self) -> &str {
        &self.key
    }

    pub fn name(&self) -> &str {
        name_of(&self.key)
    }
}

fn rand_suffix() -> u32 {
    // Uniqueness, not secrecy: the clock and the process id are plenty.
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.subsec_nanos());
    nanos ^ std::process::id().rotate_left(16)
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

fn name_of(key: &str) -> &str {
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

/// The remote names under which machines' workspaces are shown: the machine's name, or
/// `name-1a2b` when two machines share a name or the name is taken (by the `git`
/// pseudo-remote, or a real remote).
pub fn remote_names(
    machines: &BTreeSet<String>,
    taken: impl Fn(&str) -> bool,
) -> BTreeMap<String, String> {
    let mut by_name: BTreeMap<&str, usize> = BTreeMap::new();
    for machine in machines {
        *by_name.entry(name_of(machine)).or_default() += 1;
    }
    machines
        .iter()
        .map(|machine| {
            let name = name_of(machine);
            let remote = if by_name[name] > 1
                || taken(name)
                || name == REMOTE_NAME_FOR_LOCAL_GIT_REPO.as_str()
            {
                format!("{name}-{}", short_id(machine))
            } else {
                name.to_owned()
            };
            (machine.clone(), remote)
        })
        .collect()
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
        let names = remote_names(&machines, |name| name == "origin");
        assert_eq!(names["beta#11112222"], "beta");
        assert_eq!(names["mac#aaaa0000"], "mac-aaaa");
        assert_eq!(names["mac#bbbb0000"], "mac-bbbb");
        assert_eq!(names["git#cccc0000"], "git-cccc");
        assert_eq!(names["origin#dddd0000"], "origin-dddd");
    }

    #[test]
    fn identity_is_durable() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("machine");
        let first = Machine::load_or_create(&path, "Bryan's MacBook Pro").unwrap();
        assert!(
            first.key().starts_with("bryan-s-macbook-pro#"),
            "{}",
            first.key()
        );
        let again = Machine::load_or_create(&path, "something else").unwrap();
        assert_eq!(first, again);
    }
}
