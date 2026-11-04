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

use jj_lib::backend::Backend as _;
use jj_lib::backend::CommitId;
use jj_lib::backend::TreeId;
use jj_lib::content_hash::ContentHash;
use jj_lib::content_hash::DigestUpdate;
use jj_lib::content_hash::blake2b_hash;
use jj_lib::object_id::ObjectId as _;
use jj_lib::protos::simple_store;
use jj_lib::repo_path::RepoPath;
use jj_lib::repo_path::RepoPathComponentBuf;
use jj_lib::simple_backend::SimpleBackend;
use pollster::FutureExt as _;
use prost::Message as _;

use super::ObjectError;
use super::ObjectStore;
use super::bundle;
use super::bundle::BundleWriter;
use super::bundle::ObjectKind;
use super::bundle::Record;
use crate::files;

/// The length of every id in jj's simple backend, which is a BLAKE2b-512 hash.
const ID_LENGTH: usize = 64;

/// The length of a change id in jj's simple backend.
const CHANGE_ID_LENGTH: usize = 16;

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

    /// Whether the store has the object `id` of `kind`. An id of another length, as a peer can
    /// send, names none, and its path could name a directory.
    fn has(&self, kind: ObjectKind, id: &[u8]) -> bool {
        id.len() == ID_LENGTH && self.path(kind, id).exists()
    }

    fn read(&self, kind: ObjectKind, id: &[u8]) -> Result<Option<Vec<u8>>, ObjectError> {
        if id.len() != ID_LENGTH {
            return Ok(None);
        }
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
            let root = kind == ObjectKind::Commit && is_root(&id);
            if root || haves.contains(id.as_slice()) || !seen.insert((kind, id.clone())) {
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

/// Whether `id` is the root commit's, which no store holds.
fn is_root(id: &[u8]) -> bool {
    id.len() == ID_LENGTH && id.iter().all(|&b| b == 0)
}

/// A store of its own, for jj to read objects from before they are stored, gone when dropped,
/// and outside the store, so that a crash leaves nothing in it.
fn scratch_store() -> Result<tempfile::TempDir, ObjectError> {
    let scratch = tempfile::tempdir()?;
    for kind in [ObjectKind::Commit, ObjectKind::Tree] {
        fs::create_dir(scratch.path().join(kind.dir()))?;
    }
    Ok(scratch)
}

/// Writes `contents` to `scratch` as the object `id` of `kind`, for jj to read, returning where.
fn staged(
    scratch: &Path,
    kind: ObjectKind,
    id: &[u8],
    contents: &[u8],
) -> Result<PathBuf, ObjectError> {
    let path = scratch
        .join(kind.dir())
        .join(jj_lib::hex_util::encode_hex(id));
    fs::write(&path, contents)?;
    Ok(path)
}

/// Bytes hashed as they are, as jj's simple backend hashes a file's or a symlink's.
struct Raw<'a>(&'a [u8]);

impl ContentHash for Raw<'_> {
    fn hash(&self, state: &mut impl DigestUpdate) {
        state.update(self.0);
    }
}

/// Fails unless jj's simple backend can read `contents` as the object `id` of `kind` without
/// panicking, and finds what hashes to `id`, as it names everything it writes. A peer's
/// object stored under another id would stand for that object wherever a commit names it,
/// and would never be replaced, since what is stored isn't received again. Commits and trees
/// are read by jj from `scratch`, a store of their own, so that nothing unchecked is stored;
/// each goes from it once read.
fn check(scratch: &Path, kind: ObjectKind, id: &[u8], contents: &[u8]) -> Result<(), ObjectError> {
    let malformed = || ObjectError::MalformedObject {
        kind: kind.dir(),
        id: jj_lib::hex_util::encode_hex(id),
    };
    let ids = |ids: &[Vec<u8>]| ids.iter().all(|id| id.len() == ID_LENGTH);
    // A merge of terms, as the root tree and the conflict labels are, has an odd number.
    let merge = |terms: usize| terms % 2 == 1;
    if id.len() != ID_LENGTH {
        return Err(malformed());
    }
    let hash = match kind {
        ObjectKind::File | ObjectKind::Symlink => blake2b_hash(&Raw(contents)).to_vec(),
        ObjectKind::Commit => {
            let commit = simple_store::Commit::decode(contents).map_err(|_| malformed())?;
            // jj makes a merged tree of the terms and the labels, which must agree on their
            // number, and writes no commit without a parent but the root.
            let labels = commit.conflict_labels.len();
            let well_formed = commit.change_id.len() == CHANGE_ID_LENGTH
                && !commit.parents.is_empty()
                && merge(commit.root_tree.len())
                && (labels == 0 || labels == commit.root_tree.len())
                && ids(&commit.parents)
                && ids(&commit.predecessors)
                && ids(&commit.root_tree);
            if !well_formed {
                return Err(malformed());
            }
            let path = staged(scratch, kind, id, contents)?;
            let read = SimpleBackend::load(scratch)
                .read_commit(&CommitId::from_bytes(id))
                .block_on();
            fs::remove_file(path)?;
            blake2b_hash(&read.map_err(|_| malformed())?).to_vec()
        }
        ObjectKind::Tree => {
            let tree = simple_store::Tree::decode(contents).map_err(|_| malformed())?;
            let mut names = tree.entries.iter().map(|entry| &entry.name);
            let sorted = names.clone().zip(names.clone().skip(1)).all(|(a, b)| a < b);
            let well_formed = sorted
                && names.all(|name| RepoPathComponentBuf::new(name.clone()).is_ok())
                && tree.entries.iter().all(|entry| {
                    use simple_store::tree_value::Value;
                    match entry.value.as_ref().and_then(|value| value.value.as_ref()) {
                        Some(Value::File(file)) => file.id.len() == ID_LENGTH,
                        Some(Value::SymlinkId(id) | Value::TreeId(id)) => id.len() == ID_LENGTH,
                        None => false,
                    }
                });
            if !well_formed {
                return Err(malformed());
            }
            let path = staged(scratch, kind, id, contents)?;
            let read = SimpleBackend::load(scratch)
                .read_tree(RepoPath::root(), &TreeId::from_bytes(id))
                .block_on();
            fs::remove_file(path)?;
            blake2b_hash(&read.map_err(|_| malformed())?).to_vec()
        }
    };
    if hash == id { Ok(()) } else { Err(malformed()) }
}

impl ObjectStore for SimpleStore {
    fn missing(&self, commits: &[CommitId]) -> Result<Vec<CommitId>, ObjectError> {
        Ok(commits
            .iter()
            .filter(|id| !is_root(id.as_bytes()) && !self.has(ObjectKind::Commit, id.as_bytes()))
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
        let mut scratch = None;
        bundle::read(bundle_path, |record| {
            let Record::Object { kind, id, contents } = record else {
                return Err(ObjectError::MalformedBundle(
                    "unexpected record in a simple-backend object bundle".to_owned(),
                ));
            };
            if !self.has(kind, &id) {
                let scratch = match &mut scratch {
                    Some(scratch) => scratch,
                    None => scratch.insert(scratch_store()?),
                };
                check(scratch.path(), kind, &id, &contents)?;
                files::replace(&self.path(kind, &id), &contents)?;
            }
            Ok(())
        })?;
        self.check_connected(wants, haves)
    }

    fn roots(&self, wants: &[CommitId], haves: &[CommitId]) -> Result<Vec<CommitId>, ObjectError> {
        let mut seen: HashSet<Vec<u8>> = haves.iter().map(|id| id.to_bytes()).collect();
        let mut stack: Vec<Vec<u8>> = wants.iter().map(|id| id.to_bytes()).collect();
        let mut roots = vec![];
        while let Some(id) = stack.pop() {
            if is_root(&id) || !seen.insert(id.clone()) {
                continue;
            }
            let Some(contents) = self.read(ObjectKind::Commit, &id)? else {
                continue;
            };
            let commit = simple_store::Commit::decode(&*contents).map_err(|_| {
                ObjectError::MalformedObject {
                    kind: ObjectKind::Commit.dir(),
                    id: jj_lib::hex_util::encode_hex(&id),
                }
            })?;
            if commit.parents.iter().all(|parent| is_root(parent)) {
                roots.push(CommitId::new(id));
            } else {
                stack.extend(commit.parents);
            }
        }
        Ok(roots)
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

#[cfg(test)]
mod tests {
    use jj_lib::backend::ChangeId;
    use jj_lib::backend::SigningFn;
    use jj_lib::merge::Merge;
    use jj_lib::simple_backend::commit_to_proto;

    use super::*;

    /// A bundle of `objects`, in `dir`.
    fn bundle(dir: &Path, name: &str, objects: &[(ObjectKind, &[u8], &[u8])]) -> PathBuf {
        let path = dir.join(name);
        let mut writer = BundleWriter::create(&path).unwrap();
        for (kind, id, contents) in objects {
            writer.object(*kind, id, contents).unwrap();
        }
        writer.finish().unwrap();
        path
    }

    /// Hive matching needs every first commit, once each, including separate histories
    /// joined by a merge. An incremental index must stop at commits it already indexed,
    /// and never mistake jj's synthetic root for a stored first commit.
    #[test]
    fn roots_find_each_history_and_stop_at_known_commits() {
        let dir = musubi_testutil::tempdir();
        let backend = SimpleBackend::init(dir.path());
        let root = backend
            .read_commit(backend.root_commit_id())
            .block_on()
            .unwrap();
        let write = |parents, description: &str| {
            backend
                .write_commit(
                    jj_lib::backend::Commit {
                        parents,
                        change_id: ChangeId::new(vec![7; CHANGE_ID_LENGTH]),
                        description: description.to_owned(),
                        ..root.clone()
                    },
                    None,
                )
                .block_on()
                .unwrap()
                .0
        };
        let a = write(vec![backend.root_commit_id().clone()], "first history");
        let b = write(vec![backend.root_commit_id().clone()], "second history");
        let merge = write(vec![a.clone(), b.clone()], "merge histories");
        let tip = write(vec![merge], "tip");
        let store = SimpleStore::new(dir.path());
        let sorted = |mut ids: Vec<CommitId>| {
            ids.sort();
            ids
        };
        let wants = [tip, a.clone(), backend.root_commit_id().clone()];
        assert_eq!(
            sorted(store.roots(&wants, &[]).unwrap()),
            sorted(vec![a.clone(), b.clone()])
        );
        assert_eq!(
            store
                .roots(&wants, std::slice::from_ref(&a))
                .unwrap()
                .as_slice(),
            std::slice::from_ref(&b)
        );
        assert!(store.roots(&wants, &[a, b]).unwrap().is_empty());
    }

    /// Objects a buggy or hostile peer can send are refused before they are stored: under an
    /// id of another length, or one their contents don't hash to, which would stand for the
    /// real object for good; or that jj would panic on as it reads or indexes them, though
    /// they hash to their id. Commits jj writes, and their trees, are taken: signed, and with a
    /// conflict and its labels, among them.
    #[test]
    fn objects_are_checked_as_jj_reads_them() {
        let dir = musubi_testutil::tempdir();
        fs::create_dir(dir.path().join("node")).unwrap();
        let node = SimpleBackend::init(&dir.path().join("node"));
        assert_eq!(node.commit_id_length(), ID_LENGTH);
        assert_eq!(node.change_id_length(), CHANGE_ID_LENGTH);
        let root = node.read_commit(node.root_commit_id()).block_on().unwrap();
        let write = |commit: jj_lib::backend::Commit, signed: bool| {
            let mut sign = |_: &[u8]| Ok(b"signature".to_vec());
            let sign: Option<&mut SigningFn> = if signed { Some(&mut sign) } else { None };
            let (id, commit) = node.write_commit(commit, sign).block_on().unwrap();
            (id.to_bytes(), commit_to_proto(&commit).encode_to_vec())
        };
        let commit = |parents: Vec<CommitId>| jj_lib::backend::Commit {
            parents,
            change_id: ChangeId::new(vec![7; CHANGE_ID_LENGTH]),
            description: "commit".to_owned(),
            ..root.clone()
        };
        let empty = node.empty_tree_id().clone();
        let labelled = |labels: &[&str]| jj_lib::backend::Commit {
            root_tree: Merge::from_vec(vec![empty.clone(), empty.clone(), empty.clone()]),
            conflict_labels: Merge::from_vec(
                labels.iter().map(|&l| l.to_owned()).collect::<Vec<_>>(),
            ),
            ..commit(vec![node.root_commit_id().clone()])
        };
        let conflicted = labelled(&["a", "b", "c"]);
        let (id, contents) = write(commit(vec![node.root_commit_id().clone()]), false);
        let (signed, _) = write(commit(vec![node.root_commit_id().clone()]), true);
        let (conflicted, _) = write(conflicted, false);
        let hub = SimpleStore::init(&dir.path().join("hub")).unwrap();
        let exported = dir.path().join("exported");
        let wants = [&id, &signed, &conflicted].map(|id| CommitId::new(id.clone()));
        SimpleStore::new(&dir.path().join("node"))
            .export(&wants, &[], &exported)
            .unwrap();
        hub.import(&exported, &wants, &[]).unwrap();
        for id in &wants {
            assert!(hub.has(ObjectKind::Commit, id.as_bytes()));
        }

        let (odd_id, odd_parent) = write(commit(vec![CommitId::new(vec![1; 19])]), false);
        let mut two_terms = simple_store::Commit::decode(&*contents).unwrap();
        two_terms.root_tree.push(two_terms.root_tree[0].clone());
        // Hashing to their ids, as jj writes the first, and would write the second if it could.
        let five_labels = write(labelled(&["a", "b", "c", "d", "e"]), false);
        let short_change = write(
            jj_lib::backend::Commit {
                change_id: ChangeId::new(vec![7; CHANGE_ID_LENGTH - 1]),
                ..commit(vec![node.root_commit_id().clone()])
            },
            false,
        );
        let parentless = commit(vec![]);
        let parentless = (
            blake2b_hash(&parentless).to_vec(),
            commit_to_proto(&parentless).encode_to_vec(),
        );
        let slash = simple_store::Tree {
            entries: vec![simple_store::tree::Entry {
                name: "a/b".to_owned(),
                value: Some(simple_store::TreeValue {
                    value: Some(simple_store::tree_value::Value::TreeId(
                        node.empty_tree_id().to_bytes(),
                    )),
                }),
            }],
        };
        let hub = SimpleStore::init(&dir.path().join("fresh")).unwrap();
        let bad: [(ObjectKind, Vec<u8>, Vec<u8>); 9] = [
            (ObjectKind::Commit, id[..32].to_vec(), contents.clone()),
            (ObjectKind::Commit, vec![9; ID_LENGTH], contents.clone()),
            (ObjectKind::Commit, odd_id, odd_parent),
            (
                ObjectKind::Commit,
                vec![3; ID_LENGTH],
                two_terms.encode_to_vec(),
            ),
            (ObjectKind::Commit, five_labels.0, five_labels.1),
            (ObjectKind::Commit, parentless.0, parentless.1),
            (ObjectKind::Commit, short_change.0, short_change.1),
            (ObjectKind::Tree, vec![4; ID_LENGTH], slash.encode_to_vec()),
            (ObjectKind::File, vec![5; ID_LENGTH], b"file".to_vec()),
        ];
        for (n, (kind, id, contents)) in bad.iter().enumerate() {
            let bundle = bundle(dir.path(), &format!("bad-{n}"), &[(*kind, id, contents)]);
            let err = hub.import(&bundle, &[], &[]).unwrap_err();
            assert!(
                matches!(err, ObjectError::MalformedObject { .. }),
                "{n}: {err:?}"
            );
            assert!(!hub.has(*kind, id), "{n}: stored");
        }
        // Only the root commit's whole id is the root's.
        let empty = CommitId::new(vec![]);
        assert_eq!(hub.missing(std::slice::from_ref(&empty)).unwrap(), [empty]);
    }
}
