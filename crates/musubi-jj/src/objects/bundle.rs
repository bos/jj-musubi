//! The bundle file format.
//!
//! ```text
//! bundle  = "MUSUBI-BUNDLE 2\n" record*
//! record  = tag:u8 length:u64le payload[length]
//! ```
//!
//! | tag | payload |
//! | --- | --- |
//! | 1 `extras` | `id_len:u8 commit_id value` |
//! | 2 `pack` | a git packfile, possibly thin |
//! | 3 `object` | `kind:u8 id_len:u8 id contents` (simple backend store file) |
//! | 4 `view` | `id_len:u8 view_id contents` (canonical view) |
//! | 5 `operation` | `id_len:u8 operation_id contents` (canonical operation) |
//! | 6 `compressed` | a zstd frame holding records other than `pack` and `compressed` |
//! | 7 `view delta` | `id_len:u8 view_id base_len:u8 base_view_id delta` |
//!
//! A view delta is the view compressed by zstd with the base view as a prefix it may refer
//! back to ([`view_delta`]). Ids are of the uncompressed contents.
//!
//! Packs can be gigabytes, so they stream into a bundle as they are produced, and out of
//! one in place, never through memory or a copy.

use std::fs::File;
use std::io;
use std::io::BufReader;
use std::io::BufWriter;
use std::io::Read;
use std::io::Seek as _;
use std::io::SeekFrom;
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;

use super::ObjectError;

const MAGIC: &[u8] = b"MUSUBI-BUNDLE 2\n";
const TAG_EXTRAS: u8 = 1;
const TAG_PACK: u8 = 2;
const TAG_OBJECT: u8 = 3;
const TAG_VIEW: u8 = 4;
const TAG_OPERATION: u8 = 5;
const TAG_COMPRESSED: u8 = 6;
const TAG_VIEW_DELTA: u8 = 7;

/// The zstd level for compressed records and view deltas: zstd's default, fast, and
/// small records gain little from more.
const LEVEL: i32 = 3;

/// The largest window a view delta may use, 2^27 bytes: what every zstd decoder accepts.
const MAX_WINDOW_LOG: u32 = 27;
/// How much of a view delta's base zstd's usual match finding indexes at `LEVEL`: the last
/// 2^(hashLog + 3) bytes, a megabyte. Long-distance matching, slower, indexes all of it.
const INDEXED_BASE: usize = 1 << 20;

/// The largest record a compressed record may decompress to. Views of this size are far
/// beyond any repository's; anything larger is malformed, not a view.
const MAX_COMPRESSED_RECORD: u64 = 1 << 30;

/// The kinds of simple-backend store file.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ObjectKind {
    Commit,
    Tree,
    File,
    Symlink,
}

impl ObjectKind {
    pub fn dir(self) -> &'static str {
        match self {
            Self::Commit => "commits",
            Self::Tree => "trees",
            Self::File => "files",
            Self::Symlink => "symlinks",
        }
    }

    fn to_byte(self) -> u8 {
        self as u8
    }

    fn from_byte(byte: u8) -> Option<Self> {
        [Self::Commit, Self::Tree, Self::File, Self::Symlink]
            .get(usize::from(byte))
            .copied()
    }
}

pub struct BundleWriter {
    out: BufWriter<File>,
    /// Records written since [`Self::begin_compressed`], compressed together.
    compressed: Option<zstd::stream::write::Encoder<'static, Vec<u8>>>,
}

impl BundleWriter {
    pub fn create(path: &Path) -> Result<Self, ObjectError> {
        let mut out = BufWriter::new(File::create(path)?);
        out.write_all(MAGIC)?;
        Ok(Self {
            out,
            compressed: None,
        })
    }

    /// Where records go: into the compressed record, if one is open.
    fn sink(&mut self) -> &mut dyn Write {
        match &mut self.compressed {
            Some(encoder) => encoder,
            None => &mut self.out,
        }
    }

    fn header(&mut self, tag: u8, len: u64) -> io::Result<()> {
        let sink = self.sink();
        sink.write_all(&[tag])?;
        sink.write_all(&len.to_le_bytes())
    }

    fn keyed(&mut self, tag: u8, id: &[u8], contents: &[u8]) -> Result<(), ObjectError> {
        let id_len = u8::try_from(id.len()).expect("ids are short");
        self.header(tag, 1 + id.len() as u64 + contents.len() as u64)?;
        let sink = self.sink();
        sink.write_all(&[id_len])?;
        sink.write_all(id)?;
        sink.write_all(contents)?;
        Ok(())
    }

    /// Compresses the records that follow, until [`Self::end_compressed`] or
    /// [`Self::finish`], into one `compressed` record. They cannot include packs, which
    /// are compressed already.
    pub fn begin_compressed(&mut self) -> Result<(), ObjectError> {
        self.end_compressed()?;
        self.compressed = Some(zstd::stream::write::Encoder::new(Vec::new(), LEVEL)?);
        Ok(())
    }

    pub fn end_compressed(&mut self) -> Result<(), ObjectError> {
        if let Some(encoder) = self.compressed.take() {
            let bytes = encoder.finish()?;
            self.header(TAG_COMPRESSED, bytes.len() as u64)?;
            self.out.write_all(&bytes)?;
        }
        Ok(())
    }

    pub fn extras(&mut self, commit: &[u8], value: &[u8]) -> Result<(), ObjectError> {
        self.keyed(TAG_EXTRAS, commit, value)
    }

    pub fn view(&mut self, id: &[u8], contents: &[u8]) -> Result<(), ObjectError> {
        self.keyed(TAG_VIEW, id, contents)
    }

    /// A view as a delta against `base`, a view the reader has: one earlier in the bundle,
    /// or one it already stores.
    pub fn view_delta(
        &mut self,
        id: &[u8],
        base_id: &[u8],
        base: &[u8],
        contents: &[u8],
    ) -> Result<(), ObjectError> {
        let delta = view_delta(base, contents)?;
        let (id_len, base_len) = (
            u8::try_from(id.len()).expect("ids are short"),
            u8::try_from(base_id.len()).expect("ids are short"),
        );
        self.header(
            TAG_VIEW_DELTA,
            2 + id.len() as u64 + base_id.len() as u64 + delta.len() as u64,
        )?;
        let sink = self.sink();
        sink.write_all(&[id_len])?;
        sink.write_all(id)?;
        sink.write_all(&[base_len])?;
        sink.write_all(base_id)?;
        sink.write_all(&delta)?;
        Ok(())
    }

    pub fn operation(&mut self, id: &[u8], contents: &[u8]) -> Result<(), ObjectError> {
        self.keyed(TAG_OPERATION, id, contents)
    }

    /// A pack, written by `produce` straight into the bundle as it is produced: writing it
    /// to a file of its own first, only to copy it here, would write it twice.
    pub fn pack_from(
        &mut self,
        produce: impl FnOnce(&mut dyn Write) -> Result<(), ObjectError>,
    ) -> Result<(), ObjectError> {
        self.end_compressed()?;
        self.out.write_all(&[TAG_PACK])?;
        self.out.flush()?;
        let len_at = self.out.get_mut().stream_position()?;
        self.out.write_all(&0u64.to_le_bytes())?;
        let mut counted = Counted {
            inner: &mut self.out,
            len: 0,
        };
        produce(&mut counted)?;
        let len = counted.len;
        self.out.flush()?;
        let file = self.out.get_mut();
        file.seek(SeekFrom::Start(len_at))?;
        file.write_all(&len.to_le_bytes())?;
        file.seek(SeekFrom::End(0))?;
        Ok(())
    }

    pub fn pack(&mut self, pack: &Path) -> Result<(), ObjectError> {
        let mut file = File::open(pack)?;
        self.pack_from(|out| {
            io::copy(&mut file, out)?;
            Ok(())
        })
    }

    pub fn object(
        &mut self,
        kind: ObjectKind,
        id: &[u8],
        contents: &[u8],
    ) -> Result<(), ObjectError> {
        let id_len = u8::try_from(id.len()).expect("ids are short");
        self.header(TAG_OBJECT, 2 + id.len() as u64 + contents.len() as u64)?;
        let sink = self.sink();
        sink.write_all(&[kind.to_byte(), id_len])?;
        sink.write_all(id)?;
        sink.write_all(contents)?;
        Ok(())
    }

    pub fn finish(mut self) -> Result<(), ObjectError> {
        self.end_compressed()?;
        self.out.flush()?;
        self.out
            .into_inner()
            .map_err(|err| err.into_error())?
            .sync_all()?;
        Ok(())
    }
}

/// A writer that counts what passes through it.
struct Counted<'a> {
    inner: &'a mut dyn Write,
    len: u64,
}

impl Write for Counted<'_> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let n = self.inner.write(buf)?;
        self.len += n as u64;
        Ok(n)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}

/// A pack in a bundle, read where it is rather than copied out.
pub struct PackRecord {
    path: PathBuf,
    offset: u64,
    len: u64,
}

impl PackRecord {
    pub fn len(&self) -> u64 {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The pack's bytes.
    pub fn reader(&self) -> io::Result<io::Take<BufReader<File>>> {
        let mut file = File::open(&self.path)?;
        file.seek(SeekFrom::Start(self.offset))?;
        Ok(BufReader::new(file).take(self.len))
    }
}

/// A record read from a bundle.
pub enum Record {
    Extras {
        commit: Vec<u8>,
        value: Vec<u8>,
    },
    Pack(PackRecord),
    Object {
        kind: ObjectKind,
        id: Vec<u8>,
        contents: Vec<u8>,
    },
    View {
        id: Vec<u8>,
        contents: Vec<u8>,
    },
    /// A view as a delta against the view `base`; see [`apply_view_delta`].
    ViewDelta {
        id: Vec<u8>,
        base: Vec<u8>,
        delta: Vec<u8>,
    },
    Operation {
        id: Vec<u8>,
        contents: Vec<u8>,
    },
}

fn malformed(what: &str) -> ObjectError {
    ObjectError::MalformedBundle(what.to_owned())
}

/// Reads every record of the bundle at `path`, in order. Compressed records are read as
/// the records they hold. A pack is not read at all: its record says where it is.
pub fn read(
    path: &Path,
    mut on_record: impl FnMut(Record) -> Result<(), ObjectError>,
) -> Result<(), ObjectError> {
    let file = File::open(path)?;
    let file_len = file.metadata()?.len();
    let mut input = BufReader::new(file);
    let mut magic = vec![0; MAGIC.len()];
    input
        .read_exact(&mut magic)
        .map_err(|_| malformed("missing header"))?;
    if magic != MAGIC {
        return Err(malformed("bad header"));
    }
    while let Some((tag, len)) = read_header(&mut input)? {
        match tag {
            TAG_PACK => {
                let offset = input.stream_position()?;
                if offset.checked_add(len).is_none_or(|end| end > file_len) {
                    return Err(malformed("truncated pack"));
                }
                input.seek(SeekFrom::Start(offset + len))?;
                on_record(Record::Pack(PackRecord {
                    path: path.to_owned(),
                    offset,
                    len,
                }))?;
            }
            TAG_COMPRESSED => {
                let mut body = (&mut input).take(len);
                let mut decoder = zstd::stream::read::Decoder::new(&mut body)
                    .map_err(|_| malformed("bad compressed record"))?;
                read_compressed(&mut decoder, &mut on_record).map_err(|err| match err {
                    ObjectError::Io(_) => malformed("bad compressed record"),
                    other => other,
                })?;
                drop(decoder);
                if io::copy(&mut body, &mut io::sink())? != 0 {
                    return Err(malformed("trailing data in a compressed record"));
                }
            }
            _ => on_record(read_small(tag, &mut (&mut input).take(len), len)?)?,
        }
    }
    Ok(())
}

/// A record's tag and length, or `None` at the end.
fn read_header(input: &mut dyn Read) -> Result<Option<(u8, u64)>, ObjectError> {
    let mut tag = [0u8];
    if input.read(&mut tag)? == 0 {
        return Ok(None);
    }
    let mut len = [0u8; 8];
    input
        .read_exact(&mut len)
        .map_err(|_| malformed("truncated record"))?;
    Ok(Some((tag[0], u64::from_le_bytes(len))))
}

/// The records of a compressed record: neither packs nor compressed records.
fn read_compressed(
    input: &mut dyn Read,
    on_record: &mut dyn FnMut(Record) -> Result<(), ObjectError>,
) -> Result<(), ObjectError> {
    while let Some((tag, len)) = read_header(input)? {
        if len > MAX_COMPRESSED_RECORD || matches!(tag, TAG_PACK | TAG_COMPRESSED) {
            return Err(malformed("bad record in a compressed record"));
        }
        on_record(read_small(tag, &mut input.take(len), len)?)?;
    }
    Ok(())
}

fn read_small(tag: u8, body: &mut dyn Read, len: u64) -> Result<Record, ObjectError> {
    if !matches!(
        tag,
        TAG_EXTRAS | TAG_OBJECT | TAG_VIEW | TAG_VIEW_DELTA | TAG_OPERATION
    ) {
        return Err(malformed("unknown record tag"));
    }
    let mut bytes = Vec::with_capacity(usize::try_from(len).unwrap_or(0).min(1 << 20));
    body.read_to_end(&mut bytes)?;
    if bytes.len() as u64 != len {
        return Err(malformed("truncated record"));
    }
    parse_small(tag, bytes).ok_or_else(|| malformed("bad record"))
}

fn parse_small(tag: u8, bytes: Vec<u8>) -> Option<Record> {
    if tag == TAG_VIEW_DELTA {
        let (&id_len, rest) = bytes.split_first()?;
        let (id, rest) = rest.split_at_checked(usize::from(id_len))?;
        let (&base_len, rest) = rest.split_first()?;
        let (base, delta) = rest.split_at_checked(usize::from(base_len))?;
        Some(Record::ViewDelta {
            id: id.to_vec(),
            base: base.to_vec(),
            delta: delta.to_vec(),
        })
    } else if tag != TAG_OBJECT {
        let (&id_len, rest) = bytes.split_first()?;
        let (id, contents) = rest.split_at_checked(usize::from(id_len))?;
        let (id, contents) = (id.to_vec(), contents.to_vec());
        Some(match tag {
            TAG_EXTRAS => Record::Extras {
                commit: id,
                value: contents,
            },
            TAG_VIEW => Record::View { id, contents },
            _ => Record::Operation { id, contents },
        })
    } else {
        let (&kind, rest) = bytes.split_first()?;
        let (&id_len, rest) = rest.split_first()?;
        let (id, contents) = rest.split_at_checked(usize::from(id_len))?;
        Some(Record::Object {
            kind: ObjectKind::from_byte(kind)?,
            id: id.to_vec(),
            contents: contents.to_vec(),
        })
    }
}

/// `contents` compressed with `base` as a prefix that zstd may refer back to: for a view
/// that differs from its parent's in a few bookmarks, a few hundred bytes.
pub fn view_delta(base: &[u8], contents: &[u8]) -> io::Result<Vec<u8>> {
    let mut encoder = zstd::stream::write::Encoder::with_ref_prefix(Vec::new(), LEVEL, base)?;
    // The window must reach back over the whole base.
    let span = (base.len() + contents.len()).max(1);
    let window_log = span
        .next_power_of_two()
        .trailing_zeros()
        .clamp(10, MAX_WINDOW_LOG);
    encoder.window_log(window_log)?;
    encoder.long_distance_matching(base.len() > INDEXED_BASE)?;
    encoder.include_contentsize(true)?;
    encoder.set_pledged_src_size(Some(contents.len() as u64))?;
    encoder.write_all(contents)?;
    encoder.finish()
}

/// The view a [`view_delta`] against `base` encodes.
pub fn apply_view_delta(base: &[u8], delta: &[u8]) -> Result<Vec<u8>, ObjectError> {
    let bad = |_| malformed("bad view delta");
    let mut decoder = zstd::stream::read::Decoder::with_ref_prefix(delta, base).map_err(bad)?;
    decoder.window_log_max(MAX_WINDOW_LOG).map_err(bad)?;
    let mut contents = vec![];
    (&mut decoder)
        .take(MAX_COMPRESSED_RECORD)
        .read_to_end(&mut contents)
        .map_err(bad)?;
    Ok(contents)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn records_round_trip() {
        let dir = tempfile::tempdir().unwrap();
        let pack = dir.path().join("pack");
        std::fs::write(&pack, b"PACK-bytes").unwrap();
        let bundle = dir.path().join("bundle");
        let mut writer = BundleWriter::create(&bundle).unwrap();
        writer.extras(b"commit-id", b"value").unwrap();
        writer.pack(&pack).unwrap();
        writer.object(ObjectKind::Tree, b"tree-id", b"").unwrap();
        writer.finish().unwrap();

        let mut seen = vec![];
        read(&bundle, |record| {
            seen.push(match record {
                Record::Extras { commit, value } => format!("extras {commit:?} {value:?}"),
                Record::Pack(pack) => format!("pack {:?}", pack_bytes(&pack)),
                Record::Object { kind, id, contents } => format!("{kind:?} {id:?} {contents:?}"),
                Record::View { .. } | Record::ViewDelta { .. } | Record::Operation { .. } => {
                    unreachable!()
                }
            });
            Ok(())
        })
        .unwrap();
        assert_eq!(
            seen,
            [
                format!("extras {:?} {:?}", b"commit-id", b"value"),
                format!("pack {:?}", b"PACK-bytes"),
                format!("Tree {:?} {:?}", b"tree-id", b""),
            ]
        );
    }

    fn pack_bytes(pack: &PackRecord) -> Vec<u8> {
        let mut bytes = vec![];
        pack.reader().unwrap().read_to_end(&mut bytes).unwrap();
        assert_eq!(bytes.len() as u64, pack.len());
        bytes
    }

    /// A pack streams into a bundle, and the records after it are read where they are.
    #[test]
    fn streamed_pack_round_trips() {
        let dir = tempfile::tempdir().unwrap();
        let bundle = dir.path().join("bundle");
        let pack: Vec<u8> = (0..3_000_000u32).map(|i| (i % 251) as u8).collect();
        let mut writer = BundleWriter::create(&bundle).unwrap();
        writer.extras(b"commit", b"value").unwrap();
        writer
            .pack_from(|out| {
                for chunk in pack.chunks(4096) {
                    out.write_all(chunk)?;
                }
                Ok(())
            })
            .unwrap();
        writer.object(ObjectKind::File, b"id", b"after").unwrap();
        writer.finish().unwrap();
        let mut seen = vec![];
        read(&bundle, |record| {
            seen.push(match record {
                Record::Pack(record) => {
                    assert_eq!(pack_bytes(&record), pack);
                    "pack".to_owned()
                }
                Record::Extras { .. } => "extras".to_owned(),
                Record::Object { contents, .. } => String::from_utf8(contents).unwrap(),
                Record::View { .. } | Record::ViewDelta { .. } | Record::Operation { .. } => {
                    unreachable!()
                }
            });
            Ok(())
        })
        .unwrap();
        assert_eq!(seen, ["extras", "pack", "after"]);
        // A pack that runs past the end of the bundle is caught.
        let bytes = std::fs::read(&bundle).unwrap();
        std::fs::write(&bundle, &bytes[..bytes.len() / 2]).unwrap();
        assert!(matches!(
            read(&bundle, |_| Ok(())),
            Err(ObjectError::MalformedBundle(_))
        ));
    }

    /// Lines like a view's bookmarks: similar, but not trivially compressible.
    fn view_like(lines: usize, changed: Option<usize>) -> Vec<u8> {
        use std::hash::Hash as _;
        use std::hash::Hasher as _;
        let mut bytes = vec![];
        for i in 0..lines {
            write!(bytes, "refs/heads/bookmark-{i} ").unwrap();
            for half in 0..2 {
                let mut hasher = std::hash::DefaultHasher::new();
                (i, half, Some(i) == changed).hash(&mut hasher);
                write!(bytes, "{:016x}", hasher.finish()).unwrap();
            }
            bytes.push(b'\n');
        }
        bytes
    }

    #[test]
    fn compressed_records_round_trip() {
        let dir = tempfile::tempdir().unwrap();
        let pack = dir.path().join("pack");
        std::fs::write(&pack, b"PACK-bytes").unwrap();
        let base = view_like(1000, None);
        let view = view_like(1000, Some(7));
        let bundle = dir.path().join("bundle");
        let mut writer = BundleWriter::create(&bundle).unwrap();
        writer.begin_compressed().unwrap();
        writer.view(b"base", &base).unwrap();
        writer.view_delta(b"view", b"base", &base, &view).unwrap();
        writer.operation(b"op", b"operation").unwrap();
        writer.end_compressed().unwrap();
        writer.pack(&pack).unwrap();
        writer.begin_compressed().unwrap();
        writer.operation(b"op2", b"another").unwrap();
        writer.finish().unwrap();
        // Compressed, the base view is a fraction of its size, and the view a tiny one.
        assert!(std::fs::metadata(&bundle).unwrap().len() < base.len() as u64 / 2);

        let mut seen = vec![];
        read(&bundle, |record| {
            seen.push(match record {
                Record::View { id, contents } => (id, contents),
                Record::ViewDelta {
                    id,
                    base: base_id,
                    delta,
                } => {
                    assert_eq!(base_id, b"base");
                    (id, apply_view_delta(&base, &delta).unwrap())
                }
                Record::Operation { id, contents } => (id, contents),
                Record::Pack(pack) => (b"pack".to_vec(), pack_bytes(&pack)),
                Record::Extras { .. } | Record::Object { .. } => unreachable!(),
            });
            Ok(())
        })
        .unwrap();
        assert_eq!(
            seen,
            [
                (b"base".to_vec(), base),
                (b"view".to_vec(), view),
                (b"op".to_vec(), b"operation".to_vec()),
                (b"pack".to_vec(), b"PACK-bytes".to_vec()),
                (b"op2".to_vec(), b"another".to_vec()),
            ]
        );
    }

    /// A delta costs about what changed, however large the view: beyond that, a few bytes
    /// for each of zstd's 128 KiB blocks.
    #[test]
    fn view_delta_is_about_the_size_of_the_change() {
        // Without long-distance matching, up to a base of a megabyte, and with it beyond.
        for lines in [10, 1_000, 17_000, 18_500, 100_000] {
            let base = view_like(lines, None);
            let view = view_like(lines, Some(lines / 2));
            let delta = view_delta(&base, &view).unwrap();
            assert!(
                delta.len() < 100 + base.len() / 5000,
                "{lines} lines, {} bytes: {} bytes",
                base.len(),
                delta.len()
            );
            assert_eq!(apply_view_delta(&base, &delta).unwrap(), view);
            // The wrong base gives something else, or nothing.
            let other = view_like(lines, Some(0));
            assert_ne!(apply_view_delta(&other, &delta).ok(), Some(view));
        }
    }

    #[test]
    fn corrupt_compressed_record_is_rejected() {
        let dir = tempfile::tempdir().unwrap();
        let bundle = dir.path().join("bundle");
        let mut writer = BundleWriter::create(&bundle).unwrap();
        writer.begin_compressed().unwrap();
        writer.operation(b"op", &view_like(100, None)).unwrap();
        writer.finish().unwrap();
        let mut bytes = std::fs::read(&bundle).unwrap();
        let middle = bytes.len() - 40;
        bytes[middle] ^= 0xff;
        std::fs::write(&bundle, &bytes).unwrap();
        assert!(matches!(
            read(&bundle, |_| Ok(())),
            Err(ObjectError::MalformedBundle(_))
        ));
    }

    #[test]
    fn truncated_bundle_is_rejected() {
        let dir = tempfile::tempdir().unwrap();
        let bundle = dir.path().join("bundle");
        let mut writer = BundleWriter::create(&bundle).unwrap();
        writer.object(ObjectKind::File, b"id", b"contents").unwrap();
        writer.finish().unwrap();
        let bytes = std::fs::read(&bundle).unwrap();
        std::fs::write(&bundle, &bytes[..bytes.len() - 1]).unwrap();
        assert!(matches!(
            read(&bundle, |_| Ok(())),
            Err(ObjectError::MalformedBundle(_))
        ));
    }
}
