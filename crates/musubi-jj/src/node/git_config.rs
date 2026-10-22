//! A node's git config, read with the git binary and reused until a file it came from
//! changes. A daemon syncs often, and each sync wants the repository's remotes and whether
//! it is a partial clone, but its config seldom changes, and starting git takes long enough
//! on Windows to matter.

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;

use crate::git_command::GitError;
use crate::git_command::GitRepo;

/// The last [`ConfigRead`] of a repository.
#[derive(Default)]
pub(super) struct ConfigCache(Mutex<Option<Arc<ConfigRead>>>);

/// What git's config said, as `git config --list` and `git remote -v` print it, and the
/// files that said it.
pub(super) struct ConfigRead {
    /// Every config entry, in the order git reads them.
    entries: Vec<ConfigEntry>,
    /// `git remote -v`.
    pub remotes: String,
    /// The files the read depends on, with their contents from before it, or `None` where
    /// a file was missing or, unless `whole`, unread. They are small, and compared whole, a
    /// change in the same tick of a file system's clock as the read included.
    files: BTreeMap<PathBuf, Option<Vec<u8>>>,
    /// Whether every file the read depends on was read before it. A read that finds others
    /// is never reused: one of them may have changed meanwhile, even been deleted.
    whole: bool,
}

pub(super) struct ConfigEntry {
    /// `local`, `global`, and so on: where git found the entry, or the file including it.
    scope: String,
    /// The file git read it from, if a file.
    file: Option<PathBuf>,
    pub key: String,
    /// `None` for a key without `=`, which is a true boolean.
    pub value: Option<String>,
}

impl ConfigCache {
    /// `repo`'s config, read again only where a file it came from, or one git would read
    /// it from, has changed since the last read. That includes the files an include names
    /// that don't exist yet, and, where an `onbranch:` include depends on it, HEAD. A system
    /// config file created since isn't noticed until another changes.
    pub fn read(&self, repo: &GitRepo) -> Result<Arc<ConfigRead>, GitError> {
        let mut last = self.0.lock().unwrap_or_else(PoisonError::into_inner);
        if let Some(read) = &*last
            && read.whole
            && read
                .files
                .iter()
                .all(|(path, then)| fs::read(path).ok() == *then)
        {
            return Ok(read.clone());
        }
        // Read before git reads them, so that a change meanwhile shows next time.
        let mut files: BTreeMap<PathBuf, Option<Vec<u8>>> = config_files(repo)
            .into_iter()
            .chain(last.iter().flat_map(|read| read.files.keys().cloned()))
            .map(|path| {
                let contents = fs::read(&path).ok();
                (path, contents)
            })
            .collect();
        let output = repo.run(
            &["config", "--list", "--show-scope", "--show-origin", "-z"],
            None,
        )?;
        let remotes = String::from_utf8_lossy(&repo.run(&["remote", "-v"], None)?).into_owned();
        let entries = parse_config_list(repo.git_dir(), &output);
        // Files the read found besides those, which the next read reads first: included
        // ones, and missing ones an include names. HEAD only where an `onbranch:` include
        // needs it, since jj moves a colocated repository's on most commands.
        let mut whole = true;
        for file in entries.iter().flat_map(|entry| {
            let onbranch = entry.key.starts_with("includeif.onbranch:");
            [
                entry.file.clone(),
                entry.included(),
                onbranch.then(|| repo.git_dir().join("HEAD")),
            ]
            .into_iter()
            .flatten()
        }) {
            files.entry(file).or_insert_with(|| {
                whole = false;
                None
            });
        }
        let read = Arc::new(ConfigRead {
            entries,
            remotes,
            files,
            whole,
        });
        *last = Some(read.clone());
        Ok(read)
    }
}

impl ConfigRead {
    /// The entries from the repository's own config, and the files it includes.
    pub fn local(&self) -> impl Iterator<Item = &ConfigEntry> {
        self.entries.iter().filter(|entry| entry.scope == "local")
    }

    /// The entries from the repository's own config file alone, which `git remote` and
    /// `git config --local` can change: not those of a file it includes. git lists a
    /// file's entries in order, an include's own among them before what it includes, so
    /// the first local entry comes from the file itself, named as git names it.
    pub fn own(&self) -> impl Iterator<Item = &ConfigEntry> {
        let own = self.local().next().and_then(|entry| entry.file.clone());
        self.local()
            .filter(move |entry| own.is_some() && entry.file == own)
    }
}

impl ConfigEntry {
    /// The file an `include.path` or `includeIf.<condition>.path` entry names, whether or
    /// not it exists or its condition holds.
    fn included(&self) -> Option<PathBuf> {
        let section = self.key.strip_suffix(".path")?;
        if section != "include" && !section.starts_with("includeif.") {
            return None;
        }
        let path = self.value.as_deref()?;
        match path.strip_prefix("~/") {
            Some(rest) => Some(home()?.join(rest)),
            None => Some(self.file.as_deref()?.parent()?.join(path)),
        }
    }
}

fn home() -> Option<PathBuf> {
    env::var_os("HOME")
        .filter(|home| !home.is_empty())
        .map(PathBuf::from)
        .or_else(env::home_dir)
}

/// The config files git reads whether or not they exist: the repository's own, and the
/// global ones, whose creation a read must notice. git names the others it reads.
fn config_files(repo: &GitRepo) -> Vec<PathBuf> {
    let mut files = vec![
        repo.git_dir().join("config"),
        repo.git_dir().join("config.worktree"),
    ];
    if let Some(global) = env::var_os("GIT_CONFIG_GLOBAL") {
        files.push(global.into());
    } else if let Some(home) = home() {
        files.push(home.join(".gitconfig"));
        let xdg = env::var_os("XDG_CONFIG_HOME")
            .filter(|dir| !dir.is_empty())
            .map_or_else(|| home.join(".config"), PathBuf::from);
        files.push(xdg.join("git").join("config"));
    }
    files
}

/// Parses `git config --list --show-scope --show-origin -z`, whose entries are a scope, an
/// origin, then the key, each ending in NUL, with the key followed by a newline and its
/// value if it has one. A file origin's relative path is relative to `dir`, where git ran.
fn parse_config_list(dir: &Path, output: &[u8]) -> Vec<ConfigEntry> {
    let output = String::from_utf8_lossy(output);
    let mut fields = output.split('\0');
    let mut entries = vec![];
    while let (Some(scope), Some(origin), Some(item)) =
        (fields.next(), fields.next(), fields.next())
    {
        let (key, value) = match item.split_once('\n') {
            Some((key, value)) => (key, Some(value.to_owned())),
            None => (item, None),
        };
        entries.push(ConfigEntry {
            scope: scope.to_owned(),
            file: origin.strip_prefix("file:").map(|path| dir.join(path)),
            key: key.to_owned(),
            value,
        });
    }
    entries
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::git_command::git;

    #[test]
    fn config_is_read_again_only_once_a_file_changes() {
        let dir = tempfile::tempdir().unwrap();
        let git_dir = dir.path().join(".git");
        let run = |args: &[&str]| {
            let output = git(Path::new("git"))
                .current_dir(dir.path())
                .args(args)
                .output()
                .unwrap();
            assert!(output.status.success(), "git {args:?}: {output:?}");
        };
        let remote =
            |name: &str| format!("[remote \"{name}\"]\n\turl = https://example.com/{name}\n");
        run(&["init", "--quiet"]);
        run(&["config", "include.path", "included"]);
        run(&["config", "--add", "include.path", "missing"]);
        run(&["config", "includeIf.onbranch:other.path", "on-other"]);
        fs::write(git_dir.join("included"), remote("a")).unwrap();
        fs::write(git_dir.join("on-other"), remote("b")).unwrap();
        let repo = GitRepo::new(Path::new("git"), &git_dir);
        let cache = ConfigCache::default();
        let remotes = |entries: &mut dyn Iterator<Item = &ConfigEntry>| -> Vec<String> {
            let mut names: Vec<String> = entries
                .filter_map(|entry| entry.key.strip_suffix(".url"))
                .filter_map(|key| key.strip_prefix("remote."))
                .map(str::to_owned)
                .collect();
            names.sort();
            names
        };
        let names = || remotes(&mut cache.read(&repo).unwrap().local());
        // A file a read finds is read before the next is reused, even where it has gone
        // meanwhile.
        {
            let dir = tempfile::tempdir().unwrap();
            let git_dir = dir.path().join(".git");
            let output = git(Path::new("git"))
                .args(["init", "--quiet"])
                .arg(dir.path())
                .output()
                .unwrap();
            assert!(output.status.success(), "{output:?}");
            let repo = GitRepo::new(Path::new("git"), &git_dir);
            let cache = ConfigCache::default();
            // Every file git reads already, the system's too.
            cache.read(&repo).unwrap();
            cache.read(&repo).unwrap();
            let config = git_dir.join("config");
            let text = fs::read_to_string(&config).unwrap();
            fs::write(&config, format!("{text}[include]\n\tpath = included\n")).unwrap();
            fs::write(git_dir.join("included"), remote("a")).unwrap();
            assert_eq!(remotes(&mut cache.read(&repo).unwrap().local()), ["a"]);
            fs::remove_file(git_dir.join("included")).unwrap();
            assert!(remotes(&mut cache.read(&repo).unwrap().local()).is_empty());
        }
        let reused = || {
            // The first read after a change may find files it hadn't read, which the next
            // reads.
            cache.read(&repo).unwrap();
            let read = cache.read(&repo).unwrap();
            Arc::ptr_eq(&read, &cache.read(&repo).unwrap())
        };
        assert_eq!(names(), ["a"]);
        assert!(reused(), "an unchanged config is read again");

        // An included file changes, to one of the same size, as fast as git can read it.
        fs::write(git_dir.join("included"), remote("c")).unwrap();
        assert_eq!(names(), ["c"]);
        assert!(reused());

        // A missing included file appears.
        fs::write(git_dir.join("missing"), remote("d")).unwrap();
        assert_eq!(names(), ["c", "d"]);

        // HEAD moves to the branch an `onbranch:` include names.
        run(&["symbolic-ref", "HEAD", "refs/heads/other"]);
        assert_eq!(names(), ["b", "c", "d"]);

        // The repository's own config changes.
        run(&["remote", "add", "e", "https://example.com/e"]);
        assert_eq!(names(), ["b", "c", "d", "e"]);
        assert!(reused());
        // Of which `git remote` can change only its own.
        assert_eq!(remotes(&mut cache.read(&repo).unwrap().own()), ["e"]);
    }
}
