//! Provenance of histories offered to the hub, including offers with a lost reply.
//!
//! Persist exact ancestry frontiers, not original identities: an earlier release's contraction,
//! and cleanup's of native parents, can keep an original identity while removing ancestors an
//! older offer already shared.

use std::collections::BTreeSet;
use std::collections::HashSet;
use std::fs;

use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use serde::Deserialize;
use serde::Serialize;

use super::NodeError;
use super::NodeRepo;
use crate::node::PublicationError;
use crate::op_id::CanonicalOp;

pub(in crate::node) const OFFERS_FILE: &str = "publication-offers.json";

#[derive(Deserialize, Serialize)]
struct PublicationOffers {
    heads: Vec<String>,
    checksum: String,
}

impl NodeRepo {
    /// Start tracking before the first attempt under this guard. Existing copies freeze
    /// their pre-activation heads: latest-push markers cannot rule out an older lost reply.
    pub fn initialize_publication_offers(&mut self) -> Result<(), NodeError> {
        let path = self.repo_path.join("musubi").join(OFFERS_FILE);
        if path.exists() {
            return Ok(());
        }
        let legacy = ["pushed", "accepted_push", "accepted_base"]
            .iter()
            .any(|name| self.repo_path.join("musubi").join(name).exists());
        let mut heads = if legacy {
            self.canonical_heads()?
        } else {
            vec![]
        };
        for name in ["pushed", "accepted_push"] {
            match fs::read_to_string(self.repo_path.join("musubi").join(name)) {
                Ok(text) => {
                    let id = OperationId::try_from_hex(text.trim())
                        .filter(|id| {
                            id.as_bytes().len()
                                == self.canonical.root_operation_id().0.as_bytes().len()
                        })
                        .ok_or(PublicationError::UnreadableMarker(name))?;
                    heads.push(CanonicalOp(id));
                }
                Err(err) if err.kind() == std::io::ErrorKind::NotFound => {}
                Err(source) => {
                    return Err(NodeError::Io {
                        path: path.clone(),
                        source,
                    });
                }
            }
        }
        use std::io::Write as _;
        let data = Self::encode_publication_offers(&heads)?;
        match fs::OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(&path)
        {
            Ok(mut file) => file
                .write_all(&data)
                .map_err(|source| NodeError::Io { path, source }),
            Err(err) if err.kind() == std::io::ErrorKind::AlreadyExists => Ok(()),
            Err(source) => Err(NodeError::Io { path, source }),
        }
    }

    pub(super) fn read_publication_offers(&self) -> Result<Vec<CanonicalOp>, NodeError> {
        let path = self.repo_path.join("musubi").join(OFFERS_FILE);
        let text = fs::read_to_string(&path).map_err(|source| NodeError::Io {
            path: path.clone(),
            source,
        })?;
        let encoded: PublicationOffers = serde_json::from_str(&text)
            .map_err(|err| PublicationError::UnreadableOffers(err.to_string()))?;
        let body = serde_json::to_vec(&encoded.heads).map_err(PublicationError::Json)?;
        if blake3::hash(&body).to_hex().as_str() != encoded.checksum {
            return Err(PublicationError::UnreadableOffers("checksum mismatch".to_owned()).into());
        }
        encoded
            .heads
            .into_iter()
            .map(|hex| {
                let id = OperationId::try_from_hex(&hex)
                    .filter(|id| {
                        id.as_bytes().len() == self.canonical.root_operation_id().0.as_bytes().len()
                    })
                    .map(CanonicalOp)
                    .ok_or(PublicationError::InvalidOfferedId)?;
                if !self.canonical.has_operation(&id) {
                    return Err(PublicationError::MissingOfferedHistory.into());
                }
                Ok(id)
            })
            .collect()
    }

    fn encode_publication_offers(heads: &[CanonicalOp]) -> Result<Vec<u8>, NodeError> {
        let values: BTreeSet<_> = heads.iter().map(|id| id.0.hex()).collect();
        let heads: Vec<_> = values.into_iter().collect();
        let body = serde_json::to_vec(&heads).map_err(PublicationError::Json)?;
        let offers = PublicationOffers {
            heads,
            checksum: blake3::hash(&body).to_hex().to_string(),
        };
        Ok(serde_json::to_vec(&offers).map_err(PublicationError::Json)?)
    }

    fn write_publication_offers(&self, heads: &[CanonicalOp]) -> Result<(), NodeError> {
        use std::io::Write as _;
        let path = self.repo_path.join("musubi").join(OFFERS_FILE);
        let data = Self::encode_publication_offers(heads)?;
        if fs::read(&path).ok().as_deref() == Some(&data) {
            return Ok(());
        }
        let write = || -> std::io::Result<()> {
            let mut file = fs::OpenOptions::new()
                .create(true)
                .write(true)
                .truncate(false)
                .open(&path)?;
            file.write_all(&data)?;
            file.set_len(data.len() as u64)
        };
        write().map_err(|source| NodeError::Io { path, source })
    }

    /// A compact frontier of every attempted upload. Only exact ancestry can subsume an
    /// older offer: a contraction, an earlier release's or cleanup's, may keep its head's
    /// original identity while dropping ancestors that were part of the original upload.
    pub fn record_publication_offer(&mut self, head: &CanonicalOp) -> Result<(), NodeError> {
        self.initialize_publication_offers()?;
        let previous = self.read_publication_offers()?;
        for old in &previous {
            if self.canonical.is_ancestor_of(head, old)? {
                return Ok(());
            }
        }
        let mut next = vec![];
        for old in previous {
            if !self.canonical.is_ancestor_of(&old, head)? {
                next.push(old);
            }
        }
        next.push(head.clone());
        self.write_publication_offers(&next)
    }

    pub(super) fn publication_offered_origins(&self) -> Result<HashSet<OperationId>, NodeError> {
        let offered = self.read_publication_offers()?;
        let mut pending = offered;
        let mut seen = HashSet::new();
        let mut origins = HashSet::new();
        while let Some(id) = pending.pop() {
            if id == *self.canonical.root_operation_id() || !seen.insert(id.clone()) {
                continue;
            }
            // ancestors_until deliberately skips missing bodies for other callers. A gap
            // cannot establish that an operation was never offered, so read strictly here.
            let operation = self.canonical.read_operation(&id)?;
            origins.insert(self.canonical.original_id(&id)?);
            pending.extend(operation.parents.into_iter().map(CanonicalOp));
        }
        Ok(origins)
    }
}
