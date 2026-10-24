//! Joining a hive: what a hub matches a joining repository against, and the join
//! operation that stands for its history (see "Joining" in docs/internals/design.md).

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashSet;
use std::fs;
use std::io;
use std::io::Write as _;
use std::path::PathBuf;

use futures::TryStreamExt as _;
use jj_lib::backend::CommitId;
use jj_lib::backend::Timestamp;
use jj_lib::content_hash::blake2b_hash;
use jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::Operation as StoreOperation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::OperationMetadata;
use jj_lib::op_store::TimestampRange;
use jj_lib::repo::Repo as _;
use jj_lib::revset::RevsetExpression;
use pollster::FutureExt as _;

use super::CANONICAL_ATTRIBUTE;
use super::NodeError;
use super::NodeRepo;
use super::index_err;
use crate::hive_settings;
use crate::objects::Backend;
use crate::presence;
use crate::presence::Kind;
use crate::translation_map::whole_id;

/// What a hub matches a joining repository against: see [`NodeRepo::join_summary`].
#[derive(Clone, Debug)]
pub struct JoinSummary {
    pub backend: Backend,
    pub remotes: BTreeMap<String, hive_settings::Remote>,
    /// Visible commits whose parent is the root commit, other than an empty working-copy
    /// commit with no description.
    pub roots: Vec<CommitId>,
    /// The commits remote bookmarks point to.
    pub remote_targets: Vec<CommitId>,
}

impl NodeRepo {
    fn joins_path(&self) -> PathBuf {
        self.repo_path.join("musubi/joins")
    }

    /// Join records are the one part of the translation that cannot be recomputed, so they
    /// live apart from the translation cache: each line holds the local join point, the
    /// canonical join operation, and the join point's fingerprint. A line a power cut tore,
    /// or a killed join left unfinished, names nothing.
    pub(super) fn read_joins(&self) -> Result<Vec<(OperationId, OperationId, String)>, NodeError> {
        let path = self.joins_path();
        let bytes = match fs::read(&path) {
            Ok(bytes) => bytes,
            Err(err) if err.kind() == io::ErrorKind::NotFound => return Ok(vec![]),
            Err(source) => return Err(NodeError::Io { path, source }),
        };
        Ok(parse_joins(&bytes))
    }

    fn record_join(
        &mut self,
        local: OperationId,
        local_op: &StoreOperation,
        canonical: OperationId,
    ) -> Result<(), NodeError> {
        let path = self.joins_path();
        let io_err = |source| NodeError::Io {
            path: path.clone(),
            source,
        };
        // A record a killed join left unfinished is ended first, so that this one is whole.
        let unended = fs::read(&path).is_ok_and(|bytes| bytes.last().is_some_and(|&b| b != b'\n'));
        let mut file = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)
            .map_err(io_err)?;
        let fingerprint = fingerprint(local_op);
        let line = format!(
            "{}{} {} {fingerprint}\n",
            if unended { "\n" } else { "" },
            local.hex(),
            canonical.hex()
        );
        // In one write, not writeln!'s several, so that a kill seldom tears it.
        file.write_all(line.as_bytes()).map_err(io_err)?;
        self.joins.insert(fingerprint, canonical.clone());
        self.insert_map(local, canonical)
    }

    /// Whether `head` descends from history this repository shared with a hive: an operation
    /// canonicalized already, a realization of another machine's, or a join point, as
    /// `canonicalize` knows them.
    fn descends_from_canonical(&self, head: &OperationId) -> Result<bool, NodeError> {
        // A repository that never shared anything has none, and needn't walk its history.
        // The canonical store, unlike the translation cache, is never lost.
        if self.joins.is_empty() && !self.canonical.has_operations()? {
            return Ok(false);
        }
        let op_store = self.loader.op_store();
        let mut seen = HashSet::new();
        let mut stack = vec![head.clone()];
        while let Some(id) = stack.pop() {
            if id == *self.root_op_id() || !seen.insert(id.clone()) {
                continue;
            }
            if self.canonical_of(&id).is_some() {
                return Ok(true);
            }
            let op = op_store.read_operation(&id).block_on()?;
            if op.metadata.attributes.contains_key(CANONICAL_ATTRIBUTE)
                || self.joins.contains_key(&fingerprint(&op))
            {
                return Ok(true);
            }
            stack.extend(op.parents);
        }
        Ok(false)
    }

    /// Creates the canonical operation that replicates this repository's current state in
    /// place of its operation history, and records that the current op head canonicalizes
    /// to it. See "Joining" in docs/internals/design.md.
    pub fn create_join_operation(&mut self, description: &str) -> Result<OperationId, NodeError> {
        let head = self.merge_heads()?;
        // A repository that was part of a hive before, and left, has canonical history
        // already: if its head descends from it, carry on from it, as any operation does. A
        // join operation on the root would hide that history from the head, and the head the
        // old hub last accepted, which this node keeps, would no longer be reachable from it:
        // which musubi takes for an op abandon, whichever hive the repository joins.
        let carried = match self.canonical_of(&head) {
            Some(canonical) => Some(canonical),
            None if self.descends_from_canonical(&head)? => Some(self.canonicalize(&head)?),
            None => None,
        };
        if carried.is_some() {
            return self.mark_joined(description);
        }
        let op = self.loader.op_store().read_operation(&head).block_on()?;
        self.check_format(&head, &op)?;
        let view = self.loader.op_store().read_view(&op.view_id).block_on()?;
        let root = self.canonical.root_operation_id().clone();
        // Joining is this machine's work: it is present from its join on.
        let attributes = BTreeMap::from([(
            presence::WORK_ATTRIBUTE.to_owned(),
            self.machine.key().to_owned(),
        )]);
        let kind = Kind {
            work: Some(self.machine.key().to_owned()),
            ..Kind::default()
        };
        let (view, presence) =
            self.canonical_view(&head, view, std::slice::from_ref(&root), None, &kind)?;
        let settings = self.loader.settings();
        let now = settings
            .operation_timestamp()
            .unwrap_or_else(Timestamp::now);
        let join = StoreOperation {
            view_id: self.canonical.write_view(&view)?,
            parents: vec![self.canonical.root_operation_id().clone()],
            metadata: OperationMetadata {
                time: TimestampRange {
                    start: now,
                    end: now,
                },
                description: description.to_owned(),
                hostname: settings.operation_hostname().to_owned(),
                username: settings.operation_username().to_owned(),
                is_snapshot: false,
                workspace_name: None,
                attributes,
            },
            commit_predecessors: Some(BTreeMap::new()),
        };
        let canonical = self.canonical.write_operation(&join)?;
        self.remember_presence(canonical.clone(), presence.apply(&canonical, &kind));
        self.record_join(head, &op, canonical.clone())?;
        Ok(canonical)
    }

    /// Makes joining this machine's work, as it is: if the hive would not show this machine
    /// as of its op head, as after it left or with its whole history joined, an operation
    /// that changes nothing else says so. Returns the canonical form of the op head.
    pub fn mark_joined(&mut self, description: &str) -> Result<OperationId, NodeError> {
        let head = self.merge_heads()?;
        let canonical = self.canonicalize(&head)?;
        if self.presence(&canonical)?.is_present(self.machine.key()) {
            return Ok(canonical);
        }
        let repo = self.repo_at(&head)?;
        let mut tx = repo.start_transaction();
        tx.set_attribute(
            presence::WORK_ATTRIBUTE.to_owned(),
            self.machine.key().to_owned(),
        );
        let joined = tx.commit(description).block_on()?;
        self.canonicalize(joined.op_id())
    }

    /// What a hub needs to know to decide which hive this repository belongs to.
    pub fn join_summary(&self) -> Result<JoinSummary, NodeError> {
        self.check_complete()?;
        let repo = self.load_at_head()?;
        let view = repo.view();
        let working_copies: BTreeSet<&CommitId> = view.wc_commit_ids().values().collect();
        let empty_tree = repo.store().empty_merged_tree().tree_ids().clone();
        let children: Vec<CommitId> = RevsetExpression::root()
            .children()
            .evaluate(repo.as_ref())
            .map_err(index_err)?
            .stream()
            .try_collect()
            .block_on()
            .map_err(index_err)?;
        let mut roots = vec![];
        for id in children {
            let commit = repo.store().get_commit(&id)?;
            // A new repository's working-copy commit is no history to share.
            let placeholder = working_copies.contains(&id)
                && commit.description().is_empty()
                && *commit.tree_ids() == empty_tree;
            if !placeholder {
                roots.push(id);
            }
        }
        let remote_targets = view
            .all_remote_bookmarks()
            .filter(|(symbol, _)| symbol.remote != REMOTE_NAME_FOR_LOCAL_GIT_REPO)
            .flat_map(|(_, remote)| remote.target.adds().flatten().cloned())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        Ok(JoinSummary {
            backend: self.backend(),
            remotes: self.remotes()?,
            roots,
            remote_targets,
        })
    }
}

/// The records of a joins file, one for each whole line.
fn parse_joins(bytes: &[u8]) -> Vec<(OperationId, OperationId, String)> {
    String::from_utf8_lossy(bytes)
        .lines()
        .filter_map(|line| {
            let [local, canonical, fingerprint] = *line.split(' ').collect::<Vec<_>>() else {
                return None;
            };
            whole_id(fingerprint)?;
            Some((
                whole_id(local)?,
                whole_id(canonical)?,
                fingerprint.to_owned(),
            ))
        })
        .collect()
}

/// What identifies an operation apart from its parents: its view, metadata, and the
/// rewrites it records. `jj op abandon` changes only the parents of the operations it
/// rewrites.
pub(super) fn fingerprint(op: &StoreOperation) -> String {
    let without_parents = StoreOperation {
        parents: vec![],
        ..op.clone()
    };
    OperationId::new(blake2b_hash(&without_parents).to_vec()).hex()
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

    /// Among whole lines, any torn anywhere names nothing, the last perhaps unended: the
    /// whole ones are read, in order.
    #[hegel::test(test_cases = 200)]
    fn torn_joins_lose_only_themselves(tc: TestCase) {
        let lines = tc.draw(gs::integers::<u8>().max_value(6));
        let (mut text, mut whole) = (String::new(), vec![]);
        for i in 0..lines {
            let (local, canonical) = (id(3 * i), id(3 * i + 1));
            let fingerprint = id(3 * i + 2).hex();
            let line = format!("{} {} {fingerprint}", local.hex(), canonical.hex());
            if tc.draw(gs::booleans()) {
                let cut = tc.draw(gs::integers::<usize>().max_value(line.len() - 1));
                text.push_str(&line[..cut]);
            } else {
                text.push_str(&line);
                whole.push((local, canonical, fingerprint));
            }
            if i + 1 < lines || tc.draw(gs::booleans()) {
                text.push('\n');
            }
        }
        assert_eq!(parse_joins(text.as_bytes()), whole);
    }
}
