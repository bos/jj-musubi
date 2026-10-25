//! Which repository is the copy of a key on this machine, and which is a duplicate made of its
//! files (docs/internals/copies.md).
//!
//! A repository's record names its hive and the jj config-id it had when it joined, and the
//! daemon's entry for its key names the same config-id. jj gives a duplicate made on this
//! machine a config-id of its own the first time it opens it while the original still exists,
//! as it decides whether a repository moved or was copied (`handle_metadata_path` in jj-lib's
//! `secure_config`); a duplicate made elsewhere has no entry here. So the copy of a key is the
//! repository whose config-id is its record's and its entry's.
//!
//! [`standing`] and [`check`] decide from what is on disk alone, and are what the Lean model
//! (`formal/Musubi/Copies.lean`) checks.

use std::fs;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use anyhow::Context as _;

use crate::config::Entry;
use crate::config::HiveConfig;
use crate::config::Membership;
use crate::repo::Located;

/// What a repository holds of its identity, read from its files: nothing is created, so a
/// repository can be looked at without changing it, however it came to be where it is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Found {
    pub record: Option<HiveConfig>,
    /// Its machine key, from `musubi/machine`.
    pub key: Option<String>,
    /// Its jj config-id, from `config-id`.
    pub config_id: Option<String>,
}

impl Found {
    /// Reads the repository whose `.jj/repo` directory is `repo_path`. Its config-id is as
    /// the file has it: jj, which gives a duplicate a new one, hasn't looked at it.
    pub fn read(repo_path: &Path) -> anyhow::Result<Self> {
        Ok(Self {
            record: HiveConfig::load(repo_path)?,
            key: read_trimmed(&repo_path.join("musubi/machine"))?,
            config_id: read_trimmed(&repo_path.join("config-id"))?,
        })
    }

    /// Reads the repository at `located` as jj sees it: jj looks at its config-id first, and
    /// gives it a new one if it is a duplicate made on this machine.
    pub fn resolve(located: &Located) -> anyhow::Result<Self> {
        crate::settings::load(&located.workspace_root, &located.repo_path)?;
        Self::read(&located.repo_path)
    }
}

fn read_trimmed(path: &Path) -> anyhow::Result<Option<String>> {
    match fs::read_to_string(path) {
        Ok(text) if !text.trim().is_empty() => Ok(Some(text.trim().to_owned())),
        Ok(_) => Ok(None),
        Err(err) if err.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(err) => Err(err).with_context(|| format!("reading {path:?}")),
    }
}

/// What a repository is to musubi on this machine.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Standing {
    /// Part of no hive: it has no record, or it left.
    Outside,
    /// Its hive was removed from the hub.
    Removed,
    /// The copy of its key: musubi syncs it.
    Copy,
    /// Its record says it joined, but its key or config-id is missing.
    Broken,
    /// Made from a copy's files: jj gave it a config-id of its own, or this machine's entry
    /// for its key is another repository's.
    Duplicate,
    /// Its record says it joined, but this machine serves no copy of its key: a duplicate made
    /// elsewhere, or the copy, carried here (restored onto a new machine, say).
    Unknown,
}

/// What `found` is, given this machine's entry for its key, if it has one.
pub fn standing(found: &Found, entry: Option<&Entry>) -> Standing {
    let Some(record) = &found.record else {
        return Standing::Outside;
    };
    // A duplicate of a copy that left, which joining would join under the copy's key.
    let elsewhere = found
        .config_id
        .as_ref()
        .is_some_and(|config_id| *config_id != record.config_id);
    match record.state {
        Membership::Left | Membership::Removed if elsewhere => return Standing::Duplicate,
        Membership::Left => return Standing::Outside,
        Membership::Removed => return Standing::Removed,
        Membership::Joined => {}
    }
    let (Some(key), Some(config_id)) = (&found.key, &found.config_id) else {
        return Standing::Broken;
    };
    if *config_id != record.config_id {
        return Standing::Duplicate;
    }
    match entry {
        None => Standing::Unknown,
        Some(entry)
            if entry.key == *key
                && entry.hive == record.hive
                && entry.config_id == record.config_id =>
        {
            Standing::Copy
        }
        Some(_) => Standing::Duplicate,
    }
}

/// What a repository whose [`standing`] is `standing` is, given whether its entry's path holds
/// the copy the entry names (`elsewhere_holds`) in another directory than this repository's
/// (`same_directory` false). jj takes a duplicate for the moved repository when the path jj
/// last saw the copy at is empty, though the copy is at its entry's path, as after it was
/// moved away, jj ran in it, and it was moved back: then the copy at the entry's path is the
/// copy, and this is a duplicate.
pub fn refine(standing: Standing, elsewhere_holds: bool, same_directory: bool) -> Standing {
    match standing {
        Standing::Copy if elsewhere_holds && !same_directory => Standing::Duplicate,
        standing => standing,
    }
}

/// [`standing`], [`refine`]d against what is at the entry's path, for the repository at
/// `located`.
pub fn standing_of(located: &Located, found: &Found, entry: Option<&Entry>) -> Standing {
    let standing = standing(found, entry);
    let Some(entry) = entry.filter(|_| standing == Standing::Copy) else {
        return standing;
    };
    let elsewhere = Located::find(&entry.path).ok();
    let holds = elsewhere.is_some() && holds(entry, &entry.path);
    let same = elsewhere.is_some_and(|other| same_directory(&other.repo_path, &located.repo_path));
    refine(standing, holds, same)
}

/// Whether `a` and `b` are one directory, however reached: by the same path, a second
/// workspace's pointer to it, or a bind mount.
#[cfg(unix)]
pub fn same_directory(a: &Path, b: &Path) -> bool {
    use std::os::unix::fs::MetadataExt as _;
    match (fs::metadata(a), fs::metadata(b)) {
        (Ok(a), Ok(b)) => a.dev() == b.dev() && a.ino() == b.ino(),
        _ => false,
    }
}

#[cfg(not(unix))]
pub fn same_directory(a: &Path, b: &Path) -> bool {
    a.canonicalize()
        .ok()
        .is_some_and(|a| b.canonicalize().ok() == Some(a))
}

/// Whether `found` is the copy `entry` names, as the daemon checks before each sync: if not,
/// why, and it syncs nothing.
pub fn check(entry: &Entry, found: &Found) -> Result<(), String> {
    let Some(record) = &found.record else {
        return Err("it is not part of a hive".to_owned());
    };
    if record.hive != entry.hive {
        return Err(format!("it is part of hive {} now", record.display_name()));
    }
    if !record.joined() {
        return Err("it is no longer part of the hive".to_owned());
    }
    match &found.key {
        None => return Err("it has no machine key".to_owned()),
        Some(key) if *key != entry.key => return Err("its machine key has changed".to_owned()),
        Some(_) => {}
    }
    if found.config_id.as_deref() != Some(&entry.config_id) || record.config_id != entry.config_id {
        return Err("it is another repository".to_owned());
    }
    Ok(())
}

/// Whether the repository at `path` is the copy `entry` names.
pub fn holds(entry: &Entry, path: &Path) -> bool {
    Located::find(path)
        .and_then(|located| Found::read(&located.repo_path))
        .is_ok_and(|found| check(entry, &found).is_ok())
}

/// Where jj last saw `entry`'s repository, if that is now the copy `entry` names and not
/// where the entry says: after the copy was moved and jj has run in it since, which records
/// its new path.
pub fn moved_to(entry: &Entry) -> Option<PathBuf> {
    let repo = crate::settings::path_of_config_id(&entry.config_id)?;
    // Its `.jj/repo`: the main workspace is two levels up.
    let workspace = repo.parent()?.parent()?.to_owned();
    (workspace != entry.path && holds(entry, &workspace)).then_some(workspace)
}

/// Where the copy `entry` names is: at its path, or where jj last saw it.
pub fn whereabouts(entry: &Entry) -> Option<PathBuf> {
    if holds(entry, &entry.path) {
        return Some(entry.path.clone());
    }
    moved_to(entry)
}

/// Why a repository whose standing is `standing` isn't the copy of its key, given this
/// machine's entry for its key, and what to do about it.
#[derive(Clone, Debug)]
pub struct NotTheCopy {
    pub why: String,
    pub what_to_do: Option<String>,
}

impl std::fmt::Display for NotTheCopy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.what_to_do {
            Some(advice) => write!(f, "{}; {advice}", self.why),
            None => write!(f, "{}", self.why),
        }
    }
}

/// See [`NotTheCopy`].
pub fn not_the_copy(
    standing: Standing,
    record: Option<&HiveConfig>,
    entry: Option<&Entry>,
) -> NotTheCopy {
    let name = record.map_or_else(|| "its hive".to_owned(), HiveConfig::display_name);
    let (why, what_to_do) = match standing {
        Standing::Outside => ("this repository is not part of a hive".to_owned(), None),
        Standing::Removed => (
            format!("this repository's hive, {name}, was removed from its hub"),
            Some(
                "`musubi join --hive <name>` joins another, and `musubi create` starts a new one"
                    .to_owned(),
            ),
        ),
        Standing::Broken => (
            format!(
                "this repository's record says it is part of hive {name}, but its machine key \
                 or jj config id is missing"
            ),
            Some("`musubi clone` makes a new copy".to_owned()),
        ),
        Standing::Copy => (format!("this repository is part of hive {name}"), None),
        Standing::Duplicate | Standing::Unknown => match entry.and_then(whereabouts) {
            Some(path) => (
                format!(
                    "this repository was made from the files of a copy in hive {name}, which is \
                     at {}, so musubi doesn't sync it",
                    path.display()
                ),
                Some("`musubi clone` makes another copy".to_owned()),
            ),
            None => (
                format!(
                    "this repository was made from the files of a copy in hive {name}, so \
                     musubi doesn't sync it"
                ),
                Some(
                    "`musubi clone` makes another copy. If it is the copy, moved or restored \
                     here, and the one it came from is gone, `musubi join --original` syncs it \
                     as the copy"
                        .to_owned(),
                ),
            ),
        },
    };
    NotTheCopy { why, what_to_do }
}

/// Fails unless the user running musubi owns the repository: a command run as another, as
/// with `sudo`, would leave files the owner can't read, and a daemon of root's would sync it.
#[cfg(unix)]
pub fn check_owner(repo_path: &Path) -> anyhow::Result<()> {
    use std::os::unix::fs::MetadataExt as _;
    let owner = fs::metadata(repo_path)
        .with_context(|| format!("reading {repo_path:?}"))?
        .uid();
    let me = crate::socket::uid()?;
    anyhow::ensure!(
        owner == me,
        "this repository belongs to another user (uid {owner}), not this one (uid {me}); run \
         musubi as its owner"
    );
    Ok(())
}

#[cfg(not(unix))]
pub fn check_owner(_repo_path: &Path) -> anyhow::Result<()> {
    Ok(())
}

#[cfg(test)]
mod tests {
    use uuid::Uuid;

    use super::*;

    const HIVE: Uuid = Uuid::from_u128(1);

    fn record(state: Membership, config_id: &str) -> HiveConfig {
        HiveConfig {
            hive: HIVE,
            name: Some("app".to_owned()),
            hub: "hub".to_owned(),
            node: "laptop".to_owned(),
            config_id: config_id.to_owned(),
            state,
        }
    }

    fn found(record: Option<HiveConfig>, config_id: &str) -> Found {
        Found {
            record,
            key: Some("laptop#1".to_owned()),
            config_id: Some(config_id.to_owned()),
        }
    }

    fn entry(config_id: &str) -> Entry {
        Entry {
            key: "laptop#1".to_owned(),
            hive: HIVE,
            config_id: config_id.to_owned(),
            path: PathBuf::from("/src/app"),
        }
    }

    #[test]
    fn the_copy_is_the_repository_whose_config_id_matches_its_record_and_entry() {
        let joined = || Some(record(Membership::Joined, "a"));
        assert_eq!(
            standing(&found(joined(), "a"), Some(&entry("a"))),
            Standing::Copy
        );
        // jj gave a duplicate made here a config-id of its own.
        assert_eq!(
            standing(&found(joined(), "b"), Some(&entry("a"))),
            Standing::Duplicate
        );
        // Adopted elsewhere, by `musubi join --original`.
        let adopted = Some(record(Membership::Joined, "b"));
        assert_eq!(
            standing(&found(adopted, "b"), Some(&entry("a"))),
            Standing::Duplicate
        );
        // Made on, or carried from, another machine.
        assert_eq!(standing(&found(joined(), "a"), None), Standing::Unknown);
        assert_eq!(standing(&found(None, "a"), None), Standing::Outside);
        let left = || Some(record(Membership::Left, "a"));
        assert_eq!(standing(&found(left(), "a"), None), Standing::Outside);
        assert_eq!(standing(&found(left(), "b"), None), Standing::Duplicate);
        let removed = || Some(record(Membership::Removed, "a"));
        assert_eq!(standing(&found(removed(), "a"), None), Standing::Removed);
        assert_eq!(standing(&found(removed(), "b"), None), Standing::Duplicate);
        let mut keyless = found(joined(), "a");
        keyless.key = None;
        assert_eq!(standing(&keyless, Some(&entry("a"))), Standing::Broken);
    }

    /// A repository jj takes for the copy, moved, is a duplicate while the copy is at its
    /// entry's path in another directory; the same directory reached another way, as from a
    /// second workspace, is the copy.
    #[test]
    fn the_copy_at_the_entry_path_wins() {
        assert_eq!(refine(Standing::Copy, true, false), Standing::Duplicate);
        assert_eq!(refine(Standing::Copy, true, true), Standing::Copy);
        assert_eq!(refine(Standing::Copy, false, false), Standing::Copy);
        assert_eq!(refine(Standing::Unknown, true, false), Standing::Unknown);
    }

    #[test]
    fn the_daemon_syncs_only_the_copy_its_entry_names() {
        let joined = || Some(record(Membership::Joined, "a"));
        assert_eq!(check(&entry("a"), &found(joined(), "a")), Ok(()));
        assert!(check(&entry("a"), &found(joined(), "b")).is_err());
        assert!(check(&entry("a"), &found(None, "a")).is_err());
        let left = Some(record(Membership::Left, "a"));
        assert!(check(&entry("a"), &found(left, "a")).is_err());
        let mut other = record(Membership::Joined, "a");
        other.hive = Uuid::from_u128(2);
        assert!(check(&entry("a"), &found(Some(other), "a")).is_err());
        let mut rekeyed = found(joined(), "a");
        rekeyed.key = Some("laptop#2".to_owned());
        assert!(check(&entry("a"), &rekeyed).is_err());
    }
}

#[cfg(test)]
mod conformance;
