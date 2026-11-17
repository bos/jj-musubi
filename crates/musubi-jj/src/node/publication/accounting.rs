//! Exact publication reports and the accepted-basis/content-size cache they reuse.
//!
//! Policy facts come from `intent`; raw reachability and sizes come from `content`.
//! This module combines them without changing either interpretation or provenance.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use jj_lib::config::ConfigGetResultExt as _;
use jj_lib::object_id::ObjectId as _;
use serde::Deserialize;
use serde::Serialize;
use thiserror::Error;

use super::Checkpoint;
use super::NodeError;
use super::NodeRepo;
use super::content::Closure;
use super::content::ContentGraph;
use super::content::ContentId;
use super::content::FileVersion;
use super::intent::Intent;
use crate::op_id::CanonicalOp;

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct PublicationLimits {
    pub files: u64,
    pub bytes: u64,
}

impl PublicationLimits {
    pub fn load(settings: &jj_lib::settings::UserSettings) -> Result<Self, NodeError> {
        let config = settings.config();
        Ok(Self {
            files: config
                .get("musubi.publication.max-files")
                .optional()?
                .unwrap_or(1000),
            bytes: config
                .get_value_with(
                    "musubi.publication.max-bytes",
                    jj_lib::settings::HumanByteSize::try_from,
                )
                .optional()?
                .map_or(64 * 1024 * 1024, |bytes| bytes.0),
        })
    }

    pub fn fits(self, files: u64, bytes: u64) -> bool {
        (self.files == 0 || files <= self.files) && (self.bytes == 0 || bytes <= self.bytes)
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct PublicationFile {
    pub path: String,
    pub bytes: u64,
    pub versions: usize,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct PublicationOperation {
    /// An unambiguous local jj operation prefix, usable with jj and the cleanup selector.
    pub id: String,
    pub description: String,
    pub snapshot: bool,
    pub files: usize,
    pub bytes: u64,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct PublicationReport {
    pub token: String,
    pub files: Vec<PublicationFile>,
    pub bytes: u64,
    pub operations: Vec<PublicationOperation>,
    pub limits: PublicationLimits,
    pub cleanup_available: bool,
    #[serde(skip)]
    pub(super) content: BTreeSet<FileVersion>,
}

impl PublicationReport {
    pub fn held(&self) -> bool {
        !self.limits.fits(self.files.len() as u64, self.bytes)
    }
}

#[derive(Debug, Error)]
#[error(
    "sending held: snapshots retain {files} files ({bytes} bytes), exceeding the publication budget\nHint: run `musubi sync --outgoing` to inspect or approve them"
)]
pub struct PublicationHeld {
    pub files: usize,
    pub bytes: u64,
}

#[derive(Default)]
pub struct PublicationCache {
    base: Option<CanonicalOp>,
    known: Closure,
    sizes: BTreeMap<ContentId, u64>,
    last: Option<(
        Vec<CanonicalOp>,
        CanonicalOp,
        PublicationLimits,
        PublicationReport,
    )>,
}

pub(super) fn report(
    node: &NodeRepo,
    ops: &[CanonicalOp],
    base: &CanonicalOp,
    cache: &mut PublicationCache,
    checkpoint: Option<Checkpoint>,
) -> Result<PublicationReport, NodeError> {
    let limits = PublicationLimits::load(node.loader.settings())?;
    let projected = checkpoint.is_some();
    if !projected
        && let Some((previous, basis, old_limits, report)) = &cache.last
        && previous == ops
        && basis == base
        && *old_limits == limits
    {
        return Ok(report.clone());
    }
    let graph = ContentGraph::new(node.loader.store(), &node.repo_path);
    let intent = Intent::new(node);
    if cache.base.as_ref() != Some(base) {
        if cache
            .base
            .as_ref()
            .is_some_and(|old| !node.canonical.is_ancestor_of(old, base).unwrap_or(false))
        {
            cache.known = Closure::default();
            cache.base = None;
        }
        let stop = cache.base.as_ref();
        let previous = node
            .canonical
            .ancestors_until(std::slice::from_ref(base), |id| Some(id) == stop)?;
        let roots = node.required_commits(&previous)?;
        graph.extend(roots, &mut cache.known, &Closure::default())?;
        cache.base = Some(base.clone());
    }
    let mut details = vec![];
    let mut protected = BTreeSet::new();
    let mut cleanup_available = true;
    for id in ops {
        let op = node.canonical.read_operation(id)?;
        let view = node.canonical.read_view(&op.view_id)?;
        let (intentional, known) = intent.facts(id, &op, &view)?;
        protected.extend(intentional);
        cleanup_available &= known;
        let roots = node.required_commits(std::slice::from_ref(id))?;
        details.push((id.clone(), op, roots));
    }
    if let Some(checkpoint) = checkpoint {
        protected.extend(checkpoint.intentional);
        details.push((checkpoint.id, checkpoint.operation, checkpoint.required));
    }
    let mut intentional = Closure::default();
    graph.extend(protected, &mut intentional, &cache.known)?;
    let mut all = BTreeSet::new();
    let mut contributions = vec![];
    for (id, op, roots) in details {
        let files = graph.files(roots, &cache.known, &intentional)?;
        all.extend(files.iter().cloned());
        contributions.push((id, op, files));
    }
    let mut sizes = BTreeMap::new();
    for file in &all {
        if !sizes.contains_key(&file.id) {
            if cache.known.contains_content(&file.id) || intentional.contains_content(&file.id) {
                sizes.insert(file.id.clone(), 0);
                continue;
            }
            let bytes = match cache.sizes.get(&file.id) {
                Some(bytes) => *bytes,
                None => {
                    let bytes = graph.content_bytes(file)?;
                    cache.sizes.insert(file.id.clone(), bytes);
                    bytes
                }
            };
            sizes.insert(file.id.clone(), bytes);
        }
    }
    let bytes_of = |files: &BTreeSet<FileVersion>| -> u64 {
        files
            .iter()
            .map(|f| &f.id)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .map(|id| sizes[id])
            .fold(0_u64, u64::saturating_add)
    };
    let bytes = bytes_of(&all);
    let mut paths: BTreeMap<String, (u64, usize)> = BTreeMap::new();
    for file in &all {
        let total = paths
            .entry(file.path.as_internal_file_string().to_owned())
            .or_default();
        total.0 = total.0.saturating_add(sizes[&file.id]);
        total.1 += 1;
    }
    let pending_ids: Vec<_> = ops
        .iter()
        .map(|id| {
            node.local_of(id)
                .map_or_else(|| id.0.hex(), |local| local.0.hex())
        })
        .collect();
    let prefix = |id: String| {
        let length = (12..=id.len())
            .find(|length| {
                pending_ids
                    .iter()
                    .filter(|other| other.starts_with(&id[..*length]))
                    .count()
                    == 1
            })
            .unwrap_or(id.len());
        id[..length].to_owned()
    };
    let operations = contributions
        .into_iter()
        .filter(|(_, _, files)| !files.is_empty())
        .map(|(id, op, files)| PublicationOperation {
            id: prefix(
                node.local_of(&id)
                    .map_or_else(|| id.0.hex(), |local| local.0.hex()),
            ),
            description: op.metadata.description,
            snapshot: op.metadata.is_snapshot,
            files: files.iter().map(|f| &f.path).collect::<BTreeSet<_>>().len(),
            bytes: bytes_of(&files),
        })
        .collect();
    let mut hash = blake3::Hasher::new();
    hash.update(node.machine.key().as_bytes());
    hash.update(base.0.as_bytes());
    hash.update(&limits.files.to_le_bytes());
    hash.update(&limits.bytes.to_le_bytes());
    let mut ordered = ops.to_vec();
    ordered.sort();
    for id in &ordered {
        hash.update(id.0.as_bytes());
    }
    hash.update(&bytes.to_le_bytes());
    hash.update(&(all.len() as u64).to_le_bytes());
    for file in &all {
        let path = file.path.as_internal_file_string();
        hash.update(&(path.len() as u64).to_le_bytes());
        hash.update(path.as_bytes());
        let (kind, id) = match &file.id {
            ContentId::File(id) => (0_u8, id.as_bytes()),
            ContentId::Symlink(id) => (1_u8, id.as_bytes()),
            ContentId::Submodule(id) => (2_u8, id.as_bytes()),
        };
        hash.update(&[kind]);
        hash.update(&(id.len() as u64).to_le_bytes());
        hash.update(id);
    }
    let token = hash.finalize().to_hex().to_string();
    let report = PublicationReport {
        content: all,
        token,
        bytes,
        limits,
        cleanup_available,
        operations,
        files: paths
            .into_iter()
            .map(|(path, (bytes, versions))| PublicationFile {
                path,
                bytes,
                versions,
            })
            .collect(),
    };
    if !projected {
        cache.last = Some((ops.to_vec(), base.clone(), limits, report.clone()));
    }
    Ok(report)
}
