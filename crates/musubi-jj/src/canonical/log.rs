//! The canonical store's log: every operation and view it holds, appended to one file.
//!
//! jj's own op store keeps a file for each operation and each view. An operation's encoding
//! is a few hundred bytes but takes a block of the disk, and each view is whole, though
//! consecutive views mostly differ in a few heads. The log keeps each operation as it is
//! encoded, and each view as a zstd delta against the view before it in the log, as views
//! travel in a bundle. Every [`KEYFRAME`]th view is compressed whole instead, so that
//! rebuilding a view never applies more than `KEYFRAME - 1` deltas.
//!
//! A record is `tag:u8 len:u32 check:[u8; 8] body`, the check being the first bytes of the
//! BLAKE3 hash of the tag, length and body. Its body is:
//!
//! | tag | body |
//! | --- | --- |
//! | 1 operation | `id encoded` |
//! | 2 view | `id zstd(view)` |
//! | 3 view delta | `id base delta`, `delta` as [`bundle::view_delta`] makes it |
//!
//! Ids are 64 bytes, as jj's simple op store makes them, and views are in normal form (see
//! `CanonicalStore::normal_view_bytes`).
//!
//! Records are appended under a lock file, so that the daemon and a command can both
//! write. A record cut short or garbled, as a process killed mid-write or a power cut
//! leaves one, ends what a scan reads, and the next writer cuts it off before appending.
//! A delta's base always comes before it, so everything before a damaged record still
//! reads. A reader that doesn't find a record scans again from where it stopped, for
//! records another process has appended since.

use std::collections::BTreeMap;
use std::collections::HashMap;
use std::fs;
use std::fs::File;
use std::io;
use std::io::BufReader;
use std::io::Read as _;
use std::io::Seek as _;
use std::io::SeekFrom;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::PoisonError;

use jj_lib::object_id::HexPrefix;
use jj_lib::object_id::ObjectId as _;
use jj_lib::object_id::PrefixResolution;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::ViewId;

use crate::objects::bundle;

/// The length of an operation or view id.
pub const ID_LEN: usize = 64;

/// How many views in a row share a whole one to rebuild from.
pub const KEYFRAME: u32 = 128;

const OPERATION: u8 = 1;
const VIEW: u8 = 2;
const VIEW_DELTA: u8 = 3;

const CHECK_LEN: usize = 8;
const HEADER_LEN: usize = 1 + 4 + CHECK_LEN;

/// The largest record body, and the largest view, a log holds: far beyond any repository's.
const MAX_LEN: u32 = 1 << 30;

/// zstd's default level, as bundles use.
const LEVEL: i32 = 3;

/// Where a record's payload is: what follows its ids.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Span {
    offset: u64,
    len: u32,
}

#[derive(Debug)]
struct ViewEntry {
    payload: Span,
    /// The view this one is a delta against, or `None` for a whole one.
    base: Option<ViewId>,
    /// How many deltas rebuilding it applies.
    depth: u32,
}

/// What a scan has read of the log.
#[derive(Debug, Default)]
struct Index {
    /// Where the last whole record read ends.
    end: u64,
    ops: BTreeMap<OperationId, Span>,
    views: HashMap<ViewId, ViewEntry>,
    /// The last view in the log, the base of the next delta.
    last_view: Option<ViewId>,
}

impl Index {
    /// Takes in the record whose body `body` begins at `start + HEADER_LEN`. `false` if it
    /// isn't one a log holds, which ends a scan as damage does.
    fn add(&mut self, tag: u8, start: u64, body: &[u8]) -> bool {
        let at = |skip: usize| Span {
            offset: start + (HEADER_LEN + skip) as u64,
            len: (body.len() - skip) as u32,
        };
        match tag {
            OPERATION if body.len() >= ID_LEN => {
                let id = OperationId::from_bytes(&body[..ID_LEN]);
                self.ops.entry(id).or_insert(at(ID_LEN));
            }
            VIEW if body.len() >= ID_LEN => {
                let id = ViewId::from_bytes(&body[..ID_LEN]);
                let entry = ViewEntry {
                    payload: at(ID_LEN),
                    base: None,
                    depth: 0,
                };
                self.views.entry(id.clone()).or_insert(entry);
                self.last_view = Some(id);
            }
            VIEW_DELTA if body.len() >= 2 * ID_LEN => {
                let id = ViewId::from_bytes(&body[..ID_LEN]);
                let base = ViewId::from_bytes(&body[ID_LEN..2 * ID_LEN]);
                let Some(depth) = self.views.get(&base).map(|base| base.depth + 1) else {
                    return false;
                };
                let entry = ViewEntry {
                    payload: at(2 * ID_LEN),
                    base: Some(base),
                    depth,
                };
                self.views.entry(id.clone()).or_insert(entry);
                self.last_view = Some(id);
            }
            _ => return false,
        }
        true
    }
}

pub struct Log {
    path: PathBuf,
    /// Opened to read and write, at given offsets only, so that threads sharing it never
    /// move each other's file position. Not in append mode, which on Windows leaves out the
    /// access cutting off damage takes.
    file: File,
    /// The same file, opened once more for scans, which move its position: used only with
    /// the index locked.
    scanned: File,
    /// Held while appending, so that records from two processes never interleave.
    lock: File,
    index: Mutex<Index>,
    /// The view rebuilt last, which is usually the base of the next one asked for.
    recent: Mutex<Option<(ViewId, Arc<Vec<u8>>)>>,
}

impl std::fmt::Debug for Log {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Log").field("path", &self.path).finish()
    }
}

impl Log {
    /// Opens the log in the directory `dir`, creating it if needed, and reads it.
    pub fn open(dir: &Path) -> io::Result<Self> {
        fs::create_dir_all(dir)?;
        let path = dir.join("log");
        let file = fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(&path)?;
        // Never truncated: ext4 writes out a file truncated to nothing as it is closed.
        let lock = fs::OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(false)
            .open(dir.join("lock"))?;
        let scanned = File::open(&path)?;
        let log = Self {
            path,
            file,
            scanned,
            lock,
            index: Mutex::default(),
            recent: Mutex::default(),
        };
        log.scan(&mut log.index())?;
        Ok(log)
    }

    fn index(&self) -> MutexGuard<'_, Index> {
        self.index.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Reads the records appended since the last scan, through a handle of its own, whose
    /// position no other read moves: the index, locked, keeps scans apart.
    fn scan(&self, index: &mut Index) -> io::Result<()> {
        let mut reader = BufReader::with_capacity(1 << 16, &self.scanned);
        reader.seek(SeekFrom::Start(index.end))?;
        loop {
            let mut header = [0; HEADER_LEN];
            if !read_whole(&mut reader, &mut header)? {
                return Ok(());
            }
            let tag = header[0];
            let len = u32::from_le_bytes(header[1..5].try_into().expect("four bytes"));
            if len > MAX_LEN {
                return Ok(());
            }
            let mut body = vec![0; len as usize];
            if !read_whole(&mut reader, &mut body)?
                || check(&header[..5], &body) != header[5..]
                || !index.add(tag, index.end, &body)
            {
                return Ok(());
            }
            index.end += (HEADER_LEN + body.len()) as u64;
        }
    }

    /// The index, scanned again first if it lacks what `has` looks for: another process may
    /// have appended it.
    fn index_having(&self, has: impl Fn(&Index) -> bool) -> io::Result<MutexGuard<'_, Index>> {
        let mut index = self.index();
        if !has(&index) {
            self.scan(&mut index)?;
        }
        Ok(index)
    }

    /// Appends the record `build` makes, if it makes one, under the lock, once the index has
    /// every record before it and the log has nothing after them.
    fn append(
        &self,
        build: impl FnOnce(&Index) -> io::Result<Option<(u8, Vec<u8>)>>,
    ) -> io::Result<()> {
        let mut index = self.index();
        self.lock.lock()?;
        let appended = (|| {
            self.scan(&mut index)?;
            // What a scan stops at, under the lock, isn't a record being written: it is
            // damage, which would hide every record appended after it.
            if self.file.metadata()?.len() > index.end {
                self.file.set_len(index.end)?;
            }
            let Some((tag, body)) = build(&index)? else {
                return Ok(());
            };
            let len = u32::try_from(body.len())
                .ok()
                .filter(|&len| len <= MAX_LEN)
                .ok_or_else(|| io::Error::other("record too large for the log"))?;
            let mut record = Vec::with_capacity(HEADER_LEN + body.len());
            record.push(tag);
            record.extend_from_slice(&len.to_le_bytes());
            let check = check(&record, &body);
            record.extend_from_slice(&check);
            record.extend_from_slice(&body);
            let start = index.end;
            write_at(&self.file, &record, start)?;
            assert!(index.add(tag, start, &body), "a record the log holds");
            index.end += record.len() as u64;
            Ok(())
        })();
        self.lock.unlock()?;
        appended
    }

    /// Appends an encoded operation, unless the log has it.
    pub fn append_operation(&self, id: &OperationId, encoded: &[u8]) -> io::Result<()> {
        assert_eq!(id.as_bytes().len(), ID_LEN);
        self.append(|index| {
            if index.ops.contains_key(id) {
                return Ok(None);
            }
            Ok(Some((OPERATION, [id.as_bytes(), encoded].concat())))
        })
    }

    /// Appends a view in normal form, unless the log has it: as a delta against the last
    /// view, or whole once that one's depth calls for a keyframe.
    pub fn append_view(&self, id: &ViewId, contents: &[u8]) -> io::Result<()> {
        assert_eq!(id.as_bytes().len(), ID_LEN);
        self.append(|index| {
            if index.views.contains_key(id) {
                return Ok(None);
            }
            let base = index
                .last_view
                .as_ref()
                .filter(|base| index.views[*base].depth + 1 < KEYFRAME);
            let record = match base {
                Some(base) => {
                    let delta = bundle::view_delta(&self.rebuild(index, base)?, contents)?;
                    (
                        VIEW_DELTA,
                        [id.as_bytes(), base.as_bytes(), &delta].concat(),
                    )
                }
                None => {
                    let whole = zstd::encode_all(contents, LEVEL)?;
                    (VIEW, [id.as_bytes(), &whole].concat())
                }
            };
            Ok(Some(record))
        })
    }

    fn read(&self, span: Span) -> io::Result<Vec<u8>> {
        let mut buf = vec![0; span.len as usize];
        read_at(&self.file, &mut buf, span.offset)?;
        Ok(buf)
    }

    pub fn has_operation(&self, id: &OperationId) -> io::Result<bool> {
        Ok(self
            .index_having(|index| index.ops.contains_key(id))?
            .ops
            .contains_key(id))
    }

    pub fn has_view(&self, id: &ViewId) -> io::Result<bool> {
        Ok(self
            .index_having(|index| index.views.contains_key(id))?
            .views
            .contains_key(id))
    }

    /// An operation's encoding, if the log has it.
    pub fn operation(&self, id: &OperationId) -> io::Result<Option<Vec<u8>>> {
        let span = self
            .index_having(|index| index.ops.contains_key(id))?
            .ops
            .get(id)
            .copied();
        span.map(|span| self.read(span)).transpose()
    }

    /// A view in normal form, if the log has it.
    pub fn view(&self, id: &ViewId) -> io::Result<Option<Vec<u8>>> {
        let index = self.index_having(|index| index.views.contains_key(id))?;
        if !index.views.contains_key(id) {
            return Ok(None);
        }
        self.rebuild(&index, id).map(Some)
    }

    /// Rebuilds a view the index has, from the nearest whole view before it, or from the
    /// view rebuilt last.
    fn rebuild(&self, index: &Index, id: &ViewId) -> io::Result<Vec<u8>> {
        let recent = self
            .recent
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone();
        let mut deltas = vec![];
        let mut at = id;
        let mut contents = loop {
            if let Some((recent_id, bytes)) = &recent
                && recent_id == at
            {
                break bytes.to_vec();
            }
            let entry = &index.views[at];
            match &entry.base {
                Some(base) => {
                    deltas.push(entry.payload);
                    at = base;
                }
                None => break decompress(&self.read(entry.payload)?)?,
            }
        };
        for delta in deltas.into_iter().rev() {
            contents = bundle::apply_view_delta(&contents, &self.read(delta)?)
                .map_err(|err| io::Error::new(io::ErrorKind::InvalidData, err))?;
        }
        *self.recent.lock().unwrap_or_else(PoisonError::into_inner) =
            Some((id.clone(), Arc::new(contents.clone())));
        Ok(contents)
    }

    /// Every operation the log holds.
    pub fn operation_ids(&self) -> io::Result<Vec<OperationId>> {
        let mut index = self.index();
        self.scan(&mut index)?;
        Ok(index.ops.keys().cloned().collect())
    }

    /// Every view the log holds.
    pub fn view_ids(&self) -> io::Result<Vec<ViewId>> {
        let mut index = self.index();
        self.scan(&mut index)?;
        Ok(index.views.keys().cloned().collect())
    }

    /// The operation `prefix` names, `root` among the candidates, as jj resolves one.
    pub fn resolve_prefix(
        &self,
        prefix: &HexPrefix,
        root: &OperationId,
    ) -> io::Result<PrefixResolution<OperationId>> {
        let mut index = self.index();
        self.scan(&mut index)?;
        let stored = index
            .ops
            .range(OperationId::from_bytes(prefix.min_prefix_bytes())..)
            .map(|(id, _)| id)
            .take_while(|id| prefix.matches(*id));
        let mut matches = prefix
            .matches(root)
            .then_some(root)
            .into_iter()
            .chain(stored);
        Ok(match (matches.next(), matches.next()) {
            (None, _) => PrefixResolution::NoMatch,
            (Some(id), None) => PrefixResolution::SingleMatch(id.clone()),
            (Some(_), Some(_)) => PrefixResolution::AmbiguousMatch,
        })
    }

    /// The bytes after the last whole record: damage, unless another process is appending.
    pub fn unread(&self) -> io::Result<u64> {
        let mut index = self.index();
        self.scan(&mut index)?;
        Ok(self.file.metadata()?.len() - index.end)
    }
}

/// The check a record's header carries: its tag and length, then its body, hashed.
fn check(tag_and_len: &[u8], body: &[u8]) -> [u8; CHECK_LEN] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(tag_and_len);
    hasher.update(body);
    let mut check = [0; CHECK_LEN];
    check.copy_from_slice(&hasher.finalize().as_bytes()[..CHECK_LEN]);
    check
}

/// A whole view's contents.
fn decompress(compressed: &[u8]) -> io::Result<Vec<u8>> {
    let mut contents = vec![];
    zstd::stream::read::Decoder::new(compressed)?
        .take(u64::from(MAX_LEN))
        .read_to_end(&mut contents)?;
    Ok(contents)
}

/// Fills `buf`, or returns `false` if the reader ends first.
fn read_whole(reader: &mut impl io::Read, buf: &mut [u8]) -> io::Result<bool> {
    match reader.read_exact(buf) {
        Ok(()) => Ok(true),
        Err(err) if err.kind() == io::ErrorKind::UnexpectedEof => Ok(false),
        Err(err) => Err(err),
    }
}

#[cfg(unix)]
fn read_at(file: &File, buf: &mut [u8], offset: u64) -> io::Result<()> {
    std::os::unix::fs::FileExt::read_exact_at(file, buf, offset)
}

#[cfg(unix)]
fn write_at(file: &File, buf: &[u8], offset: u64) -> io::Result<()> {
    std::os::unix::fs::FileExt::write_all_at(file, buf, offset)
}

#[cfg(windows)]
fn write_at(file: &File, mut buf: &[u8], mut offset: u64) -> io::Result<()> {
    use std::os::windows::fs::FileExt as _;
    while !buf.is_empty() {
        match file.seek_write(buf, offset) {
            Ok(0) => return Err(io::ErrorKind::WriteZero.into()),
            Ok(n) => {
                buf = &buf[n..];
                offset += n as u64;
            }
            Err(err) if err.kind() == io::ErrorKind::Interrupted => {}
            Err(err) => return Err(err),
        }
    }
    Ok(())
}

#[cfg(windows)]
fn read_at(file: &File, mut buf: &mut [u8], mut offset: u64) -> io::Result<()> {
    use std::os::windows::fs::FileExt as _;
    while !buf.is_empty() {
        match file.seek_read(buf, offset) {
            Ok(0) => return Err(io::ErrorKind::UnexpectedEof.into()),
            Ok(n) => {
                buf = &mut buf[n..];
                offset += n as u64;
            }
            Err(err) if err.kind() == io::ErrorKind::Interrupted => {}
            Err(err) => return Err(err),
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use std::io::Write as _;

    use hegel::TestCase;
    use hegel::generators as gs;

    use super::*;

    /// A record as written: its id, what it holds, and where the log ended after it.
    struct Written {
        id: Vec<u8>,
        view: bool,
        contents: Vec<u8>,
        end: u64,
    }

    /// Bytes from `seed`, varied enough that zstd can't make them vanish.
    fn bytes(seed: u64, len: usize) -> Vec<u8> {
        let mut x = seed | 1;
        (0..len)
            .map(|_| {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                x as u8
            })
            .collect()
    }

    fn id(kind: u8, i: usize) -> Vec<u8> {
        let mut id = vec![kind; ID_LEN];
        id[1..9].copy_from_slice(&(i as u64).to_le_bytes());
        id
    }

    fn read(log: &Log, record: &Written) -> Option<Vec<u8>> {
        let read = if record.view {
            log.view(&ViewId::from_bytes(&record.id))
        } else {
            log.operation(&OperationId::from_bytes(&record.id))
        };
        read.unwrap()
    }

    fn has(log: &Log, record: &Written) -> bool {
        if record.view {
            log.has_view(&ViewId::from_bytes(&record.id)).unwrap()
        } else {
            log.has_operation(&OperationId::from_bytes(&record.id))
                .unwrap()
        }
    }

    fn append(log: &Log, dir: &Path, view: bool, i: usize, contents: Vec<u8>) -> Written {
        let id = id(if view { 2 } else { 1 }, i);
        if view {
            log.append_view(&ViewId::from_bytes(&id), &contents)
                .unwrap();
        } else {
            log.append_operation(&OperationId::from_bytes(&id), &contents)
                .unwrap();
        }
        let end = fs::metadata(dir.join("log")).unwrap().len();
        Written {
            id,
            view,
            contents,
            end,
        }
    }

    /// Views and operations are written, some twice, then the log's tail is damaged as a
    /// crash can leave it: cut short, zero-filled, garbled, or grown with zeros. Opened
    /// again, each reads back as written or not at all, and only one written whole before
    /// the damage is sure to; no view takes more than `KEYFRAME - 1` deltas to rebuild; and
    /// the next append cuts the damage off, so that it, and what read before it, reads from
    /// the log and from the log opened afresh.
    #[hegel::test(test_cases = 200)]
    fn damage_loses_only_what_follows_it(tc: TestCase) {
        let dir = musubi_testutil::tempdir();
        let log = Log::open(dir.path()).unwrap();
        let count = tc.draw(gs::integers::<usize>().min_value(1).max_value(300));
        let base = bytes(tc.draw(gs::integers::<u64>()), 400);
        let mut written: Vec<Written> = vec![];
        for i in 0..count {
            if i > 0 && tc.draw(gs::integers::<u8>().max_value(15)) == 0 {
                // Written again: nothing is appended.
                let again = &written[tc.draw(gs::integers::<usize>().max_value(written.len() - 1))];
                let before = fs::metadata(dir.path().join("log")).unwrap().len();
                let (view, contents) = (again.view, again.contents.clone());
                let i = usize::from_le_bytes(again.id[1..9].try_into().unwrap());
                append(&log, dir.path(), view, i, contents);
                assert_eq!(fs::metadata(dir.path().join("log")).unwrap().len(), before);
                continue;
            }
            let view = tc.draw(gs::booleans());
            let contents = if view {
                // Mostly like the last view, as consecutive views are.
                let mut contents = base.clone();
                let at = tc.draw(gs::integers::<usize>().max_value(base.len() - 1));
                contents[at] ^= 0xff;
                contents.extend(bytes(
                    i as u64,
                    tc.draw(gs::integers::<usize>().max_value(40)),
                ));
                contents
            } else {
                bytes(
                    tc.draw(gs::integers::<u64>()),
                    tc.draw(gs::integers::<usize>().max_value(600)),
                )
            };
            written.push(append(&log, dir.path(), view, i, contents));
        }
        for record in &written {
            assert_eq!(read(&log, record).as_ref(), Some(&record.contents));
        }
        assert!(
            log.index()
                .views
                .values()
                .all(|entry| entry.depth < KEYFRAME)
        );

        let path = dir.path().join("log");
        let len = fs::metadata(&path).unwrap().len();
        let at = tc.draw(gs::integers::<u64>().max_value(len));
        let mut file = fs::OpenOptions::new().write(true).open(&path).unwrap();
        let mut overwrite = |bytes: &[u8]| {
            file.seek(SeekFrom::Start(at)).unwrap();
            file.write_all(bytes).unwrap();
        };
        match tc.draw(gs::integers::<u8>().max_value(3)) {
            0 => file.set_len(at).unwrap(),
            1 => overwrite(&vec![0; (len - at) as usize]),
            2 => {
                let span = tc.draw(gs::integers::<u64>().min_value(1).max_value(64));
                overwrite(&bytes(
                    tc.draw(gs::integers::<u64>()),
                    span.min(len - at) as usize,
                ));
            }
            _ => file
                .set_len(len + tc.draw(gs::integers::<u64>().min_value(1).max_value(4096)))
                .unwrap(),
        }
        drop(file);

        let log = Log::open(dir.path()).unwrap();
        let mut kept = vec![];
        for record in &written {
            let read = read(&log, record);
            assert_eq!(read.is_some(), has(&log, record));
            match read {
                Some(contents) => {
                    assert_eq!(contents, record.contents);
                    kept.push(record);
                }
                None => assert!(record.end > at, "lost a record written before the damage"),
            }
        }
        assert!(
            log.index()
                .views
                .values()
                .all(|entry| entry.depth < KEYFRAME)
        );

        let op = append(&log, dir.path(), false, count, bytes(1, 100));
        let view = append(&log, dir.path(), true, count + 1, base.clone());
        assert_eq!(log.unread().unwrap(), 0);
        let reopened = Log::open(dir.path()).unwrap();
        for record in kept.iter().copied().chain([&op, &view]) {
            assert_eq!(read(&log, record).as_ref(), Some(&record.contents));
            assert_eq!(read(&reopened, record).as_ref(), Some(&record.contents));
        }
    }

    /// Two processes share a log: each finds what the other appended, and appends after it,
    /// a view as a delta against the other's last.
    #[test]
    fn two_writers_share_the_log() {
        let dir = musubi_testutil::tempdir();
        let a = Log::open(dir.path()).unwrap();
        let b = Log::open(dir.path()).unwrap();
        let base = bytes(7, 300);
        let first = append(&a, dir.path(), true, 0, base.clone());
        let mut changed = base.clone();
        changed[3] ^= 1;
        let second = append(&b, dir.path(), true, 1, changed);
        let op = append(&a, dir.path(), false, 2, bytes(8, 50));
        for log in [&a, &b] {
            for record in [&first, &second, &op] {
                assert_eq!(read(log, record).as_ref(), Some(&record.contents));
            }
        }
        let second_id = ViewId::from_bytes(&second.id);
        assert_eq!(
            b.index().views[&second_id].base,
            Some(ViewId::from_bytes(&first.id))
        );
        assert_eq!(a.unread().unwrap(), 0);
    }
}
