//! Persistent cache of the local ↔ canonical operation correspondence.
//!
//! Everything here can be recomputed: canonicalizing an original local operation is
//! deterministic, and every realization names its canonical operation in an attribute. The
//! file only saves re-walking the operation log on startup, so it is append-only, written
//! without fsync, and a line that a power cut tore, or that the next line was appended to,
//! is ignored.
//!
//! Rows start with `walked`: older two-field rows could cache a child above an identity-only
//! source alias without walking its parents. Ignore those disposable entries and rebuild them.

use std::collections::HashMap;
use std::fs;
use std::fs::File;
use std::fs::OpenOptions;
use std::io;
use std::io::BufRead as _;
use std::io::BufReader;
use std::io::Write as _;
use std::path::Path;

use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;

use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;

/// The length of an operation id in hex, local or canonical: 64 bytes, as jj's simple op
/// store, the only one musubi opens, makes them. jj takes hex of any even length for an id,
/// so a torn line could otherwise name one.
pub(crate) const ID_HEX_LEN: usize = 128;

pub struct TranslationMap {
    file: File,
    to_canonical: HashMap<LocalOp, CanonicalOp>,
    to_local: HashMap<CanonicalOp, LocalOp>,
    /// Whether the file's last line, torn, has no newline: the next line ends it first, so
    /// that it isn't lost with it. A lost line wouldn't be canonicalized again, since
    /// canonicalizing stops at operations it knows.
    unended: bool,
}

impl TranslationMap {
    pub fn open(path: &Path) -> io::Result<Self> {
        if let Some(dir) = path.parent() {
            fs::create_dir_all(dir)?;
        }
        let mut map = Self {
            file: OpenOptions::new().create(true).append(true).open(path)?,
            to_canonical: HashMap::new(),
            to_local: HashMap::new(),
            unended: false,
        };
        let mut reader = BufReader::new(File::open(path)?);
        let mut line = vec![];
        while reader.read_until(b'\n', &mut line)? > 0 {
            map.unended = line.pop_if(|b| *b == b'\n').is_none();
            if let Some((local, canonical)) = parse(&line) {
                map.remember(local, canonical);
            }
            line.clear();
        }
        Ok(map)
    }

    pub fn canonical_of(&self, local: &LocalOp) -> Option<&CanonicalOp> {
        self.to_canonical.get(local)
    }

    /// The local operation most recently recorded for `canonical`. Older ones, left by a
    /// crash, are unreachable garbage.
    pub fn local_of(&self, canonical: &CanonicalOp) -> Option<&LocalOp> {
        self.to_local.get(canonical)
    }

    pub fn insert(&mut self, local: LocalOp, canonical: CanonicalOp) -> io::Result<()> {
        if self.to_canonical.get(&local) == Some(&canonical)
            && self.to_local.get(&canonical) == Some(&local)
        {
            return Ok(());
        }
        self.write(&local, &canonical)?;
        self.remember(local, canonical);
        Ok(())
    }

    /// Records a translation whose local operation isn't written yet, in memory only: the
    /// file gets it from [`Self::write`] once the operation is written, so that it never
    /// names an operation that isn't there.
    pub fn insert_unwritten(&mut self, local: LocalOp, canonical: CanonicalOp) {
        self.remember(local, canonical);
    }

    /// Adds a translation [`Self::insert_unwritten`] recorded to the file.
    pub fn write(&mut self, local: &LocalOp, canonical: &CanonicalOp) -> io::Result<()> {
        // In one write, not writeln!'s several, so that two processes appending at once
        // don't interleave their lines.
        let start = if self.unended { "\n" } else { "" };
        let line = format!("{start}walked {} {}\n", local.0.hex(), canonical.0.hex());
        self.file.write_all(line.as_bytes())?;
        self.unended = false;
        Ok(())
    }

    /// Forgets a translation [`Self::insert_unwritten`] recorded, whose operation was never
    /// written.
    pub fn forget(&mut self, local: &LocalOp, canonical: &CanonicalOp) {
        if self.to_canonical.get(local) == Some(canonical) {
            self.to_canonical.remove(local);
        }
        if self.to_local.get(canonical) == Some(local) {
            self.to_local.remove(canonical);
        }
    }

    fn remember(&mut self, local: LocalOp, canonical: CanonicalOp) {
        self.to_canonical.insert(local.clone(), canonical.clone());
        self.to_local.insert(canonical, local);
    }
}

/// A line's local and canonical ids, if it is whole.
fn parse(line: &[u8]) -> Option<(LocalOp, CanonicalOp)> {
    let (local, canonical) = std::str::from_utf8(line)
        .ok()?
        .strip_prefix("walked ")?
        .split_once(' ')?;
    Some((LocalOp(whole_id(local)?), CanonicalOp(whole_id(canonical)?)))
}

/// The operation id `hex` names, if it is a whole one.
pub(crate) fn whole_id(hex: &str) -> Option<OperationId> {
    (hex.len() == ID_HEX_LEN)
        .then(|| OperationId::try_from_hex(hex))
        .flatten()
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use hegel::TestCase;
    use hegel::generators as gs;

    use super::*;

    fn id(byte: u8) -> OperationId {
        OperationId::new(vec![byte; 64])
    }

    fn local(byte: u8) -> LocalOp {
        LocalOp(id(byte))
    }

    fn canonical(byte: u8) -> CanonicalOp {
        CanonicalOp(id(byte))
    }

    #[test]
    fn old_rows_do_not_claim_complete_ancestry() {
        let dir = musubi_testutil::tempdir();
        let path = dir.path().join("translation");
        let (local, canonical) = (local(0xa), canonical(0xb));
        fs::write(&path, format!("{} {}\n", local.0.hex(), canonical.0.hex())).unwrap();
        let mut map = TranslationMap::open(&path).unwrap();
        assert_eq!(map.canonical_of(&local), None);
        assert_eq!(map.local_of(&canonical), None);
        map.insert(local.clone(), canonical.clone()).unwrap();
        drop(map);
        let map = TranslationMap::open(&path).unwrap();
        assert_eq!(map.canonical_of(&local), Some(&canonical));
        assert_eq!(map.local_of(&canonical), Some(&local));
    }

    /// A line torn by a power cut names nothing, and the next line is not lost with it.
    #[test]
    fn a_torn_line_names_nothing() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("translation");
        let [a, c, e] = [0xa, 0xc, 0xe].map(local);
        let [b, d, f] = [0xb, 0xd, 0xf].map(canonical);
        // Torn within the canonical id, at an even length, which jj would take for an id.
        fs::write(
            &path,
            format!(
                "walked {} {}\nwalked {} {}",
                a.0.hex(),
                b.0.hex(),
                c.0.hex(),
                &d.0.hex()[..40]
            ),
        )
        .unwrap();
        let mut map = TranslationMap::open(&path).unwrap();
        assert_eq!(map.local_of(&b), Some(&a));
        assert_eq!(map.canonical_of(&c), None);
        map.insert(c.clone(), d.clone()).unwrap();
        map.insert(e.clone(), f.clone()).unwrap();
        drop(map);
        let map = TranslationMap::open(&path).unwrap();
        assert_eq!(map.local_of(&b), Some(&a));
        assert_eq!(map.local_of(&d), Some(&c));
        assert_eq!(map.local_of(&f), Some(&e));
    }

    /// Among whole lines, any torn anywhere names nothing, the last perhaps unended: the
    /// whole ones are read, and none is lost to a line inserted after them.
    #[hegel::test(test_cases = 200)]
    fn torn_lines_lose_only_themselves(tc: TestCase) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("translation");
        let lines = tc.draw(gs::integers::<u8>().max_value(6));
        let (mut text, mut whole, mut torn) = (String::new(), vec![], vec![]);
        for i in 0..lines {
            let (local, canonical) = (local(2 * i), canonical(2 * i + 1));
            let line = format!("walked {} {}", local.0.hex(), canonical.0.hex());
            if tc.draw(gs::booleans()) {
                let cut = tc.draw(gs::integers::<usize>().max_value(line.len() - 1));
                text.push_str(&line[..cut]);
                torn.push(local);
            } else {
                text.push_str(&line);
                whole.push((local, canonical));
            }
            if i + 1 < lines || tc.draw(gs::booleans()) {
                text.push('\n');
            }
        }
        fs::write(&path, &text).unwrap();
        let mut map = TranslationMap::open(&path).unwrap();
        for (local, canonical) in &whole {
            assert_eq!(map.canonical_of(local), Some(canonical));
            assert_eq!(map.local_of(canonical), Some(local));
        }
        for local in &torn {
            assert_eq!(map.canonical_of(local), None);
        }
        let (local, canonical) = (local(0xfe), canonical(0xff));
        map.insert(local.clone(), canonical.clone()).unwrap();
        drop(map);
        let map = TranslationMap::open(&path).unwrap();
        for (local, canonical) in whole.iter().chain([&(local, canonical)]) {
            assert_eq!(map.canonical_of(local), Some(canonical));
        }
    }
}
