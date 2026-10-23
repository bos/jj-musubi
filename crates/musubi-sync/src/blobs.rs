//! Content-addressed blobs and chunked transfer (docs/protocol.md, "Chunked blobs").
//!
//! A transfer session is keyed by the blob's id, so it is never confused with another
//! blob's. Chunks may arrive lost, duplicated, or out of order: the receiver appends only
//! bytes that extend what it has contiguously, reports how much that is, and checks the
//! hash once everything has arrived, starting over on a mismatch. A receiver that already
//! has the blob reports it complete at once. This is the protocol `formal/Musubi/Chunks.lean`
//! verifies.

use std::collections::HashSet;
use std::fs;
use std::fs::File;
use std::fs::OpenOptions;
use std::io;
use std::io::Read as _;
use std::io::Seek as _;
use std::io::SeekFrom;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Mutex;
use std::time::SystemTime;

use musubi_jj::files;
use serde::Deserialize;
use serde::Serialize;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct BlobId(pub [u8; 32]);

impl BlobId {
    pub fn of_file(path: &Path) -> io::Result<(Self, u64)> {
        let mut hasher = blake3::Hasher::new();
        let len = io::copy(&mut File::open(path)?, &mut hasher)?;
        Ok((Self(*hasher.finalize().as_bytes()), len))
    }

    pub fn of_bytes(bytes: &[u8]) -> Self {
        Self(*blake3::hash(bytes).as_bytes())
    }

    pub fn hex(&self) -> String {
        blake3::Hash::from_bytes(self.0).to_hex().to_string()
    }
}

impl std::fmt::Debug for BlobId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BlobId({})", &self.hex()[..12])
    }
}

/// What a receiver has of a blob after taking a chunk.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Received {
    /// The first `n` bytes; send from there.
    Prefix(u64),
    Complete,
}

/// Blobs in a directory: `complete/<id>` and `partial/<id>`.
///
/// Blobs are not synced to disk: they only carry transfers, and syncing a clone's takes
/// seconds. So a blob this store did not write or check itself, as since a crash, is
/// checked before it is trusted, since one left torn would otherwise fail its hash check at
/// every receiver, every time it was sent.
pub struct BlobStore {
    dir: PathBuf,
    /// The complete blobs this store wrote or checked.
    whole: Mutex<HashSet<BlobId>>,
}

impl BlobStore {
    pub fn open(dir: &Path) -> io::Result<Self> {
        fs::create_dir_all(dir.join("complete"))?;
        fs::create_dir_all(dir.join("partial"))?;
        Ok(Self {
            dir: dir.to_owned(),
            whole: Mutex::new(HashSet::new()),
        })
    }

    fn whole(&self) -> std::sync::MutexGuard<'_, HashSet<BlobId>> {
        self.whole
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    fn complete_path(&self, id: &BlobId) -> PathBuf {
        self.dir.join("complete").join(id.hex())
    }

    fn partial_path(&self, id: &BlobId) -> PathBuf {
        self.dir.join("partial").join(id.hex())
    }

    /// The finished blob's file, if this store has it whole. One it did not write or check
    /// is checked now, and removed if torn.
    pub fn get(&self, id: &BlobId) -> Option<PathBuf> {
        let path = self.complete_path(id);
        if !path.exists() {
            return None;
        }
        if !self.whole().contains(id) {
            if !BlobId::of_file(&path).is_ok_and(|(actual, _)| actual == *id) {
                fs::remove_file(&path).ok();
                return None;
            }
            self.whole().insert(*id);
        }
        Some(path)
    }

    /// Adds a file this side created, returning its id and length. The file is linked in
    /// rather than copied where the filesystem allows: a bundle can be gigabytes, and its
    /// creator deletes its own name for it. A blob of that id already here whole is kept:
    /// renaming over it would make ext4 write the new one out to disk. It is wanted again,
    /// so it becomes as new as one just added.
    pub fn insert_file(&self, path: &Path) -> io::Result<(BlobId, u64)> {
        let (id, len) = BlobId::of_file(path)?;
        if let Some(existing) = self.get(&id) {
            renew(&existing)?;
        } else {
            let linked = tempfile::Builder::new().make_in(self.dir.join("partial"), |tmp| {
                fs::hard_link(path, tmp).or_else(|err| match err.kind() {
                    // Taken: tempfile tries another name.
                    io::ErrorKind::AlreadyExists => Err(err),
                    _ => fs::copy(path, tmp).map(drop),
                })
            })?;
            linked
                .persist(self.complete_path(&id))
                .map_err(|err| err.error)?;
            self.whole().insert(id);
        }
        Ok((id, len))
    }

    /// [`Self::insert_file`] for bytes in memory.
    pub fn insert_bytes(&self, bytes: &[u8]) -> io::Result<(BlobId, u64)> {
        let id = BlobId::of_bytes(bytes);
        if let Some(existing) = self.get(&id) {
            renew(&existing)?;
        } else {
            files::replace_through(&self.dir.join("partial"), &self.complete_path(&id), bytes)?;
            self.whole().insert(id);
        }
        Ok((id, bytes.len() as u64))
    }

    /// Takes a chunk of `id`, which is `total` bytes long. See the module docs.
    pub fn receive(
        &self,
        id: &BlobId,
        total: u64,
        offset: u64,
        data: &[u8],
    ) -> io::Result<Received> {
        if self.get(id).is_some() {
            return Ok(Received::Complete);
        }
        let partial = self.partial_path(id);
        let mut file = OpenOptions::new()
            .create(true)
            .read(true)
            .append(true)
            .open(&partial)?;
        let have = file.metadata()?.len();
        // A chunk at an offset near `u64::MAX`, which no honest sender uses, extends nothing.
        let end = offset.saturating_add(data.len() as u64);
        if offset <= have && end > have {
            let skip = usize::try_from(have - offset).expect("chunks are small");
            file.write_all(&data[skip..])?;
        }
        let have = file.metadata()?.len();
        if have < total {
            return Ok(Received::Prefix(have));
        }
        drop(file);
        let (actual, len) = BlobId::of_file(&partial)?;
        if actual != *id || len != total {
            // Corrupt or mismatched data: start over.
            fs::remove_file(&partial)?;
            return Ok(Received::Prefix(0));
        }
        fs::rename(&partial, self.complete_path(id))?;
        self.whole().insert(*id);
        Ok(Received::Complete)
    }

    /// Up to `len` bytes of a finished blob from `offset`, and the blob's total length.
    pub fn read(&self, id: &BlobId, offset: u64, len: usize) -> io::Result<(u64, Vec<u8>)> {
        let path = self
            .get(id)
            .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "no such blob"))?;
        let mut file = File::open(path)?;
        let total = file.metadata()?.len();
        file.seek(SeekFrom::Start(offset.min(total)))?;
        let mut data = vec![];
        file.take(len as u64).read_to_end(&mut data)?;
        Ok((total, data))
    }

    pub fn remove(&self, id: &BlobId) {
        self.whole().remove(id);
        fs::remove_file(self.complete_path(id)).ok();
        fs::remove_file(self.partial_path(id)).ok();
    }

    /// A temporary file, under `partial/`, so that [`Self::sweep`] removes it if a crash
    /// leaves it behind.
    pub fn temp_file(&self) -> io::Result<tempfile::NamedTempFile> {
        tempfile::NamedTempFile::new_in(self.dir.join("partial"))
    }

    /// Removes blobs, finished or not, and temporary files, last modified before `cutoff`.
    pub fn sweep(&self, cutoff: SystemTime) {
        for sub in ["complete", "partial"] {
            sweep_dir(&self.dir.join(sub), cutoff);
        }
    }
}

/// Removes the files in `dir` last modified before `cutoff`.
pub(crate) fn sweep_dir(dir: &Path, cutoff: SystemTime) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let old = entry
            .metadata()
            .and_then(|m| m.modified())
            .is_ok_and(|t| t < cutoff);
        if old {
            fs::remove_file(entry.path()).ok();
        }
    }
}

/// Makes a blob's file as new as one just added, since the hub expires blobs by age.
fn renew(path: &Path) -> io::Result<()> {
    // Open for writing, which Windows needs to set the time; nothing is written.
    OpenOptions::new()
        .write(true)
        .open(path)?
        .set_modified(SystemTime::now())
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use hegel::TestCase;
    use hegel::generators as gs;

    use super::*;

    /// A file this side created goes into the store without being copied.
    #[cfg(unix)]
    #[test]
    fn inserted_files_are_linked() {
        use std::os::unix::fs::MetadataExt as _;
        let dir = tempfile::tempdir().unwrap();
        let store = BlobStore::open(&dir.path().join("blobs")).unwrap();
        let file = dir.path().join("bundle");
        fs::write(&file, b"contents").unwrap();
        let (id, len) = store.insert_file(&file).unwrap();
        assert_eq!(len, 8);
        let stored = store.get(&id).unwrap();
        let inode = |path: &Path| fs::metadata(path).unwrap().ino();
        assert_eq!(inode(&file), inode(&stored));
        fs::remove_file(&file).unwrap();
        assert_eq!(store.read(&id, 0, 100).unwrap(), (8, b"contents".to_vec()));
    }

    /// A temporary file a crash left behind goes with a sweep.
    #[test]
    fn temp_files_are_swept() {
        let dir = tempfile::tempdir().unwrap();
        let store = BlobStore::open(dir.path()).unwrap();
        let (_, path) = store.temp_file().unwrap().keep().unwrap();
        store.sweep(SystemTime::now() + std::time::Duration::from_secs(60));
        assert!(!path.exists());
    }

    /// A blob that a crash left torn, before the store opened, is neither served nor kept.
    #[test]
    fn a_torn_blob_is_replaced() {
        let dir = tempfile::tempdir().unwrap();
        let blobs = dir.path().join("blobs");
        let file = dir.path().join("bundle");
        fs::write(&file, b"contents").unwrap();
        let (id, _) = BlobId::of_file(&file).unwrap();
        let torn = || {
            let store = BlobStore::open(&blobs).unwrap();
            fs::write(store.complete_path(&id), b"cont").unwrap();
            store
        };
        assert!(torn().read(&id, 0, 100).is_err());
        let store = torn();
        store.insert_file(&file).unwrap();
        assert_eq!(store.read(&id, 0, 100).unwrap(), (8, b"contents".to_vec()));
        let store = torn();
        store.insert_bytes(b"contents").unwrap();
        assert_eq!(store.read(&id, 0, 100).unwrap(), (8, b"contents".to_vec()));
    }

    /// A chunk whose offset and length add up past `u64::MAX` is ignored, not an overflow.
    #[test]
    fn chunk_past_the_largest_offset_is_ignored() {
        let dir = tempfile::tempdir().unwrap();
        let store = BlobStore::open(dir.path()).unwrap();
        let id = BlobId::of_bytes(b"blob");
        let received = store.receive(&id, 4, u64::MAX - 1, b"ob").unwrap();
        assert_eq!(received, Received::Prefix(0));
    }

    /// Chunks delivered in any order, duplicated, some corrupt, some lost and resent:
    /// once the receiver reports the blob complete, its content is exactly what was sent.
    #[hegel::test(test_cases = 200)]
    fn chunked_transfer_survives_any_delivery_order(tc: TestCase) {
        let dir = tempfile::tempdir().unwrap();
        let store = BlobStore::open(dir.path()).unwrap();
        let len = tc.draw(gs::integers::<usize>().max_value(300));
        let blob: Vec<u8> = (0..len).map(|i| (i * 7 % 251) as u8).collect();
        let id = BlobId::of_bytes(&blob);
        let chunk = tc.draw(gs::integers::<usize>().min_value(1).max_value(64));
        let mut done = false;
        for _ in 0..1000 {
            // The sender learns the receiver's prefix and sends some chunk at or after a
            // random point, possibly corrupted.
            let offset = tc.draw(gs::integers::<usize>().max_value(len));
            let end = (offset + chunk).min(len);
            let mut data = blob[offset..end].to_vec();
            if !data.is_empty() && tc.draw(gs::integers::<u8>().max_value(9)) == 0 {
                data[0] ^= 1;
            }
            match store
                .receive(&id, len as u64, offset as u64, &data)
                .unwrap()
            {
                Received::Complete => {
                    done = true;
                    break;
                }
                Received::Prefix(have) => {
                    // The well-behaved retransmission from the reported prefix.
                    let have = usize::try_from(have).unwrap();
                    let end = (have + chunk).min(len);
                    if let Received::Complete = store
                        .receive(&id, len as u64, have as u64, &blob[have..end])
                        .unwrap()
                    {
                        done = true;
                        break;
                    }
                }
            }
        }
        assert!(done, "transfer did not finish");
        let (total, data) = store.read(&id, 0, len + 1).unwrap();
        assert_eq!(total, len as u64);
        assert_eq!(data, blob);
    }
}
