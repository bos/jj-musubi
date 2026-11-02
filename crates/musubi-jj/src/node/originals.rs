//! Local nonparent content associated with an immutable canonical original. Unlike the
//! translation cache, this evidence must survive jj collecting the old local operations.

use std::collections::HashMap;
use std::collections::HashSet;
use std::fs::File;
use std::fs::OpenOptions;
use std::io;
use std::io::BufRead as _;
use std::io::BufReader;
use std::io::Write as _;
use std::path::Path;

use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;

use crate::translation_map::whole_id;

pub(super) struct Originals {
    file: File,
    fingerprints: HashMap<OperationId, HashSet<String>>,
    unended: bool,
}

impl Originals {
    pub(super) fn open(path: &Path) -> io::Result<Self> {
        let mut originals = Self {
            file: OpenOptions::new().create(true).append(true).open(path)?,
            fingerprints: HashMap::new(),
            unended: false,
        };
        let mut reader = BufReader::new(File::open(path)?);
        let mut line = String::new();
        while reader.read_line(&mut line)? > 0 {
            originals.unended = !line.ends_with('\n');
            if let Some((original, fingerprint)) = line.strip_suffix('\n').and_then(parse) {
                originals
                    .fingerprints
                    .entry(original)
                    .or_default()
                    .insert(fingerprint);
            }
            line.clear();
        }
        Ok(originals)
    }

    pub(super) fn fingerprints(&self, original: &OperationId) -> Option<&HashSet<String>> {
        self.fingerprints.get(original)
    }

    pub(super) fn record(&mut self, original: OperationId, fingerprint: String) -> io::Result<()> {
        if self
            .fingerprints
            .get(&original)
            .is_some_and(|known| known.contains(&fingerprint))
        {
            return Ok(());
        }
        // One append, ending any torn tail first. No fsync: missing evidence is refused,
        // never replaced with a guess about an operation's identity.
        let start = if self.unended { "\n" } else { "" };
        self.file
            .write_all(format!("{start}{} {fingerprint}\n", original.hex()).as_bytes())?;
        self.unended = false;
        self.fingerprints
            .entry(original)
            .or_default()
            .insert(fingerprint);
        Ok(())
    }
}

fn parse(line: &str) -> Option<(OperationId, String)> {
    let (original, fingerprint) = line.split_once(' ')?;
    Some((whole_id(original)?, whole_id(fingerprint)?.hex()))
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use hegel::TestCase;
    use hegel::generators as gs;

    use super::*;

    /// A torn row establishes no identity, and cannot swallow the next complete append.
    /// Several local forms of one original and equal fingerprints of different originals
    /// all remain evidence: neither direction is a last-writer-wins map.
    #[hegel::test(test_cases = 100)]
    fn torn_rows_never_establish_an_identity(tc: TestCase) {
        let dir = musubi_testutil::tempdir();
        let path = dir.path().join("originals");
        let id = |byte| OperationId::new(vec![byte; 64]);
        let mut text = String::new();
        let mut expected: HashMap<OperationId, HashSet<String>> = HashMap::new();
        for n in 0..tc.draw(gs::integers::<u8>().max_value(8)) {
            let original = id(n / 2);
            let fingerprint = id(n % 3).hex();
            let row = format!("{} {fingerprint}\n", original.hex());
            let written = tc.draw(gs::integers::<usize>().max_value(row.len()));
            text.push_str(&row[..written]);
            if written < row.len() {
                text.push('\n');
            }
            if written >= row.len() - 1 {
                expected.entry(original).or_default().insert(fingerprint);
            }
        }
        text.push_str("torn");
        std::fs::write(&path, text).unwrap();
        let mut originals = Originals::open(&path).unwrap();
        assert_eq!(originals.fingerprints, expected);
        originals.record(id(255), id(254).hex()).unwrap();
        expected.entry(id(255)).or_default().insert(id(254).hex());
        drop(originals);
        assert_eq!(Originals::open(&path).unwrap().fingerprints, expected);
    }
}
