//! Persistent cache of the local ↔ canonical operation correspondence.
//!
//! Everything here can be recomputed: canonicalizing an original local operation is
//! deterministic, and every realization names its canonical operation in an attribute. The
//! file only saves re-walking the operation log on startup, so it is append-only, written
//! without fsync, and a torn last line is ignored.

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

pub struct TranslationMap {
    file: File,
    to_canonical: HashMap<OperationId, OperationId>,
    to_local: HashMap<OperationId, OperationId>,
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
        };
        for line in BufReader::new(File::open(path)?).lines() {
            let line = line?;
            let parsed = line.split_once(' ').and_then(|(local, canonical)| {
                Some((
                    OperationId::try_from_hex(local)?,
                    OperationId::try_from_hex(canonical)?,
                ))
            });
            if let Some((local, canonical)) = parsed {
                map.remember(local, canonical);
            }
        }
        Ok(map)
    }

    pub fn canonical_of(&self, local: &OperationId) -> Option<&OperationId> {
        self.to_canonical.get(local)
    }

    /// The local operation most recently recorded for `canonical`. Older ones, left by a
    /// crash, are unreachable garbage.
    pub fn local_of(&self, canonical: &OperationId) -> Option<&OperationId> {
        self.to_local.get(canonical)
    }

    pub fn insert(&mut self, local: OperationId, canonical: OperationId) -> io::Result<()> {
        if self.to_canonical.get(&local) == Some(&canonical)
            && self.to_local.get(&canonical) == Some(&local)
        {
            return Ok(());
        }
        writeln!(self.file, "{} {}", local.hex(), canonical.hex())?;
        self.remember(local, canonical);
        Ok(())
    }

    /// Records a translation whose local operation isn't written yet, in memory only: the
    /// file gets it from [`Self::write`] once the operation is written, so that it never
    /// names an operation that isn't there.
    pub fn insert_unwritten(&mut self, local: OperationId, canonical: OperationId) {
        self.remember(local, canonical);
    }

    /// Adds a translation [`Self::insert_unwritten`] recorded to the file.
    pub fn write(&mut self, local: &OperationId, canonical: &OperationId) -> io::Result<()> {
        writeln!(self.file, "{} {}", local.hex(), canonical.hex())
    }

    /// Forgets a translation [`Self::insert_unwritten`] recorded, whose operation was never
    /// written.
    pub fn forget(&mut self, local: &OperationId, canonical: &OperationId) {
        if self.to_canonical.get(local) == Some(canonical) {
            self.to_canonical.remove(local);
        }
        if self.to_local.get(canonical) == Some(local) {
            self.to_local.remove(canonical);
        }
    }

    fn remember(&mut self, local: OperationId, canonical: OperationId) {
        self.to_canonical.insert(local.clone(), canonical.clone());
        self.to_local.insert(canonical, local);
    }
}
