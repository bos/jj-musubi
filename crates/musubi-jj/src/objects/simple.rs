//! The simple backend's objects: content-addressed store files, moved one by one.
//!
//! jj's simple backend exists mainly for jj's own tests, so this favors simplicity over
//! transfer size: a bundle carries every tree and file of each new commit, and receivers
//! skip the ones they already have.

use std::collections::BTreeSet;
use std::collections::HashSet;
use std::fs;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::protos::simple_store;
use prost::Message as _;

use super::ObjectError;
use super::ObjectStore;
use super::bundle;
use super::bundle::BundleWriter;
use super::bundle::ObjectKind;
use super::bundle::Record;

/// A simple-backend store directory (`.jj/repo/store` on a node).
pub struct SimpleStore {
    dir: PathBuf,
}

impl SimpleStore {
    pub fn new(dir: &Path) -> Self {
        Self {
            dir: dir.to_owned(),
        }
    }

    /// Creates the store directories, for a hub.
    pub fn init(dir: &Path) -> Result<Self, ObjectError> {
        for kind in [
            ObjectKind::Commit,
            ObjectKind::Tree,
            ObjectKind::File,
            ObjectKind::Symlink,
        ] {
            fs::create_dir_all(dir.join(kind.dir()))?;
        }
        Ok(Self::new(dir))
    }

    fn path(&self, kind: ObjectKind, id: &[u8]) -> PathBuf {
        self.dir
            .join(kind.dir())
            .join(jj_lib::hex_util::encode_hex(id))
    }

    fn read(&self, kind: ObjectKind, id: &[u8]) -> Result<Option<Vec<u8>>, ObjectError> {
        match fs::read(self.path(kind, id)) {
            Ok(bytes) => Ok(Some(bytes)),
            Err(err) if err.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(err) => Err(err.into()),
        }
    }

    /// Walks every object reachable from `wants`, stopping at `haves` and at the root
    /// commit, calling `visit` with each object's kind, id, and contents. Returns the
    /// objects that could not be found.
    fn walk(
        &self,
        wants: &[CommitId],
        haves: &[CommitId],
        mut visit: impl FnMut(ObjectKind, &[u8], &[u8]) -> Result<(), ObjectError>,
    ) -> Result<Vec<String>, ObjectError> {
        let haves: HashSet<&[u8]> = haves.iter().map(|id| id.as_bytes()).collect();
        let mut missing = vec![];
        let mut seen: BTreeSet<(ObjectKind, Vec<u8>)> = BTreeSet::new();
        let mut stack: Vec<(ObjectKind, Vec<u8>)> = wants
            .iter()
            .map(|id| (ObjectKind::Commit, id.to_bytes()))
            .collect();
        while let Some((kind, id)) = stack.pop() {
            let is_root = kind == ObjectKind::Commit && id.iter().all(|&b| b == 0);
            if is_root || haves.contains(id.as_slice()) || !seen.insert((kind, id.clone())) {
                continue;
            }
            let Some(contents) = self.read(kind, &id)? else {
                missing.push(format!(
                    "{} {}",
                    kind.dir(),
                    jj_lib::hex_util::encode_hex(&id)
                ));
                continue;
            };
            let malformed = || ObjectError::MalformedObject {
                kind: kind.dir(),
                id: jj_lib::hex_util::encode_hex(&id),
            };
            match kind {
                ObjectKind::Commit => {
                    let commit =
                        simple_store::Commit::decode(&*contents).map_err(|_| malformed())?;
                    stack.extend(commit.parents.into_iter().map(|p| (ObjectKind::Commit, p)));
                    stack.extend(commit.root_tree.into_iter().map(|t| (ObjectKind::Tree, t)));
                }
                ObjectKind::Tree => {
                    let tree = simple_store::Tree::decode(&*contents).map_err(|_| malformed())?;
                    for entry in tree.entries {
                        use simple_store::tree_value::Value;
                        match entry.value.and_then(|value| value.value) {
                            Some(Value::File(file)) => stack.push((ObjectKind::File, file.id)),
                            Some(Value::SymlinkId(id)) => stack.push((ObjectKind::Symlink, id)),
                            Some(Value::TreeId(id)) => stack.push((ObjectKind::Tree, id)),
                            None => return Err(malformed()),
                        }
                    }
                }
                ObjectKind::File | ObjectKind::Symlink => {}
            }
            visit(kind, &id, &contents)?;
        }
        Ok(missing)
    }
}

impl ObjectStore for SimpleStore {
    fn missing(&self, commits: &[CommitId]) -> Result<Vec<CommitId>, ObjectError> {
        Ok(commits
            .iter()
            .filter(|id| {
                !id.as_bytes().iter().all(|&b| b == 0)
                    && !self.path(ObjectKind::Commit, id.as_bytes()).exists()
            })
            .cloned()
            .collect())
    }

    fn export(
        &self,
        wants: &[CommitId],
        haves: &[CommitId],
        out: &Path,
    ) -> Result<(), ObjectError> {
        let mut writer = BundleWriter::create(out)?;
        let missing = self.walk(wants, haves, |kind, id, contents| {
            writer.object(kind, id, contents)
        })?;
        if !missing.is_empty() {
            return Err(ObjectError::NotConnected(missing.join(", ")));
        }
        writer.finish()
    }

    fn import(
        &self,
        bundle_path: &Path,
        wants: &[CommitId],
        haves: &[CommitId],
    ) -> Result<(), ObjectError> {
        bundle::read(bundle_path, |record| {
            let Record::Object { kind, id, contents } = record else {
                return Err(ObjectError::MalformedBundle(
                    "unexpected record in a simple-backend object bundle".to_owned(),
                ));
            };
            let path = self.path(kind, &id);
            if !path.exists() {
                let tmp = tempfile::NamedTempFile::new_in(self.dir.join(kind.dir()))?;
                fs::write(tmp.path(), &contents)?;
                tmp.persist(&path).map_err(|err| err.error)?;
            }
            Ok(())
        })?;
        self.check_connected(wants, haves)
    }

    fn check_connected(&self, wants: &[CommitId], haves: &[CommitId]) -> Result<(), ObjectError> {
        let missing = self.walk(wants, haves, |_, _, _| Ok(()))?;
        if missing.is_empty() {
            Ok(())
        } else {
            Err(ObjectError::NotConnected(missing.join(", ")))
        }
    }
}
