//! The bundle file format.
//!
//! ```text
//! bundle  = "MUSUBI-BUNDLE 1\n" record*
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
//!
//! Packs can be gigabytes, so records stream through files rather than memory.

use std::fs::File;
use std::io;
use std::io::BufReader;
use std::io::BufWriter;
use std::io::Read as _;
use std::io::Write as _;
use std::path::Path;

use super::ObjectError;

const MAGIC: &[u8] = b"MUSUBI-BUNDLE 1\n";
const TAG_EXTRAS: u8 = 1;
const TAG_PACK: u8 = 2;
const TAG_OBJECT: u8 = 3;
const TAG_VIEW: u8 = 4;
const TAG_OPERATION: u8 = 5;

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
}

impl BundleWriter {
    pub fn create(path: &Path) -> Result<Self, ObjectError> {
        let mut out = BufWriter::new(File::create(path)?);
        out.write_all(MAGIC)?;
        Ok(Self { out })
    }

    fn header(&mut self, tag: u8, len: u64) -> io::Result<()> {
        self.out.write_all(&[tag])?;
        self.out.write_all(&len.to_le_bytes())
    }

    fn keyed(&mut self, tag: u8, id: &[u8], contents: &[u8]) -> Result<(), ObjectError> {
        let id_len = u8::try_from(id.len()).expect("ids are short");
        self.header(tag, 1 + id.len() as u64 + contents.len() as u64)?;
        self.out.write_all(&[id_len])?;
        self.out.write_all(id)?;
        self.out.write_all(contents)?;
        Ok(())
    }

    pub fn extras(&mut self, commit: &[u8], value: &[u8]) -> Result<(), ObjectError> {
        self.keyed(TAG_EXTRAS, commit, value)
    }

    pub fn view(&mut self, id: &[u8], contents: &[u8]) -> Result<(), ObjectError> {
        self.keyed(TAG_VIEW, id, contents)
    }

    pub fn operation(&mut self, id: &[u8], contents: &[u8]) -> Result<(), ObjectError> {
        self.keyed(TAG_OPERATION, id, contents)
    }

    pub fn pack(&mut self, pack: &Path) -> Result<(), ObjectError> {
        let mut file = File::open(pack)?;
        self.header(TAG_PACK, file.metadata()?.len())?;
        io::copy(&mut file, &mut self.out)?;
        Ok(())
    }

    pub fn object(
        &mut self,
        kind: ObjectKind,
        id: &[u8],
        contents: &[u8],
    ) -> Result<(), ObjectError> {
        let id_len = u8::try_from(id.len()).expect("ids are short");
        self.header(TAG_OBJECT, 2 + id.len() as u64 + contents.len() as u64)?;
        self.out.write_all(&[kind.to_byte(), id_len])?;
        self.out.write_all(id)?;
        self.out.write_all(contents)?;
        Ok(())
    }

    pub fn finish(mut self) -> Result<(), ObjectError> {
        self.out.flush()?;
        self.out
            .into_inner()
            .map_err(|err| err.into_error())?
            .sync_all()?;
        Ok(())
    }
}

/// A record read from a bundle. Packs are copied to a temporary file.
pub enum Record {
    Extras {
        commit: Vec<u8>,
        value: Vec<u8>,
    },
    Pack(tempfile::NamedTempFile),
    Object {
        kind: ObjectKind,
        id: Vec<u8>,
        contents: Vec<u8>,
    },
    View {
        id: Vec<u8>,
        contents: Vec<u8>,
    },
    Operation {
        id: Vec<u8>,
        contents: Vec<u8>,
    },
}

/// Reads every record of the bundle at `path`, in order.
pub fn read(
    path: &Path,
    mut on_record: impl FnMut(Record) -> Result<(), ObjectError>,
) -> Result<(), ObjectError> {
    let malformed = |what: &str| ObjectError::MalformedBundle(what.to_owned());
    let mut input = BufReader::new(File::open(path)?);
    let mut magic = vec![0; MAGIC.len()];
    input
        .read_exact(&mut magic)
        .map_err(|_| malformed("missing header"))?;
    if magic != MAGIC {
        return Err(malformed("bad header"));
    }
    loop {
        let mut tag = [0u8];
        if input.read(&mut tag)? == 0 {
            return Ok(());
        }
        let mut len = [0u8; 8];
        input
            .read_exact(&mut len)
            .map_err(|_| malformed("truncated record"))?;
        let len = u64::from_le_bytes(len);
        let mut body = (&mut input).take(len);
        let record = match tag[0] {
            TAG_PACK => {
                let mut file = tempfile::NamedTempFile::new()?;
                let copied = io::copy(&mut body, file.as_file_mut())?;
                if copied != len {
                    return Err(malformed("truncated pack"));
                }
                Record::Pack(file)
            }
            TAG_EXTRAS | TAG_OBJECT | TAG_VIEW | TAG_OPERATION => {
                let mut bytes = Vec::with_capacity(usize::try_from(len).unwrap_or(0).min(1 << 20));
                body.read_to_end(&mut bytes)?;
                if bytes.len() as u64 != len {
                    return Err(malformed("truncated record"));
                }
                parse_small(tag[0], bytes).ok_or_else(|| malformed("bad record"))?
            }
            _ => return Err(malformed("unknown record tag")),
        };
        on_record(record)?;
    }
}

fn parse_small(tag: u8, bytes: Vec<u8>) -> Option<Record> {
    if tag != TAG_OBJECT {
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
                Record::Pack(file) => format!("pack {:?}", std::fs::read(file.path()).unwrap()),
                Record::Object { kind, id, contents } => format!("{kind:?} {id:?} {contents:?}"),
                Record::View { .. } | Record::Operation { .. } => unreachable!(),
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
