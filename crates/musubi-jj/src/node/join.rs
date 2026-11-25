//! Joining a hive: what a hub matches a joining repository against, and the join
//! operation that stands for its history (see "Joining" in docs/internals/design.md).

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashSet;
use std::fs;
use std::io;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;

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

use super::NodeError;
use super::NodeRepo;
use super::index_err;
use crate::objects::Backend;
use crate::op_attrs::OpAttrs;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
use crate::presence;
use crate::presence::Kind;
use crate::remote_url::{JOIN_HIVE, JoinRemotes, Remote};
use crate::translation_map::whole_id;

/// Marks a discard of the shared history under way: see [`NodeRepo::discard_shared_history`].
const DISCARDING: &str = "discarding-history";

/// What a repository keeps of the history it shared with hives, in its `musubi` directory, in
/// the order [`NodeRepo::discard_shared_history`] removes it.
const SHARED_HISTORY: [&str; 8] = [
    "joins",
    "translation",
    "canonical",
    "accepted_base",
    "pushed",
    super::ACCEPTED_PUSH,
    super::publication::OFFERS_FILE,
    super::APPROVAL_FILE,
];

/// How far [`NodeRepo::discard_shared_history`] has got, for a test to stop it there.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Discarded {
    /// The discard is marked under way.
    Marked,
    /// The first of what it removes is gone.
    Some,
    /// All of it is gone, and the mark is still there.
    All,
    /// The mark is gone too.
    Done,
}

/// What a hub matches a joining repository against: see [`NodeRepo::join_summary`].
#[derive(Clone, Debug)]
pub struct JoinSummary {
    pub backend: Backend,
    pub remotes: BTreeMap<String, Remote>,
    /// Visible commits whose parent is the root commit, other than an empty working-copy
    /// commit with no description.
    pub roots: Vec<CommitId>,
    /// The commits remote bookmarks point to.
    pub remote_targets: Vec<CommitId>,
}

/// The history a repository shared with hives before: see [`NodeRepo::shared_history`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SharedHistory {
    /// How many operations it has.
    pub operations: usize,
    /// The ids of the hives it joined.
    pub hives: BTreeSet<String>,
}

impl JoinSummary {
    pub fn remote_snapshot(&self) -> JoinRemotes {
        JoinRemotes::from_remotes(&self.remotes)
    }
}

impl NodeRepo {
    /// Conflicted shared bookmarks by Git remote, once concurrent heads have been merged
    /// and exported. The local `git` pseudo-remote is not an upstream to fetch.
    pub fn conflicted_git_bookmarks(&mut self) -> Result<BTreeMap<String, Vec<String>>, NodeError> {
        let repo = self.merged_repo()?;
        let mut remotes: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for (symbol, _) in repo
            .view()
            .all_remote_bookmarks()
            .filter(|(symbol, remote)| {
                symbol.remote != REMOTE_NAME_FOR_LOCAL_GIT_REPO
                    && symbol.name.as_str() != "HEAD"
                    && !remote.target.is_resolved()
            })
        {
            remotes
                .entry(symbol.remote.as_str().to_owned())
                .or_default()
                .push(symbol.name.as_str().to_owned());
        }
        Ok(remotes)
    }

    fn joins_path(&self) -> PathBuf {
        self.repo_path.join("musubi/joins")
    }

    /// Join records are the one part of the translation that cannot be recomputed, so they
    /// live apart from the translation cache: each line holds the local join point, the
    /// canonical join operation, and the join point's fingerprint. A line a power cut tore,
    /// or a killed join left unfinished, names nothing.
    pub(super) fn read_joins(&self) -> Result<Vec<(LocalOp, CanonicalOp, String)>, NodeError> {
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
        local: LocalOp,
        local_op: &StoreOperation,
        canonical: CanonicalOp,
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
            local.0.hex(),
            canonical.0.hex()
        );
        // In one write, not writeln!'s several, so that a kill seldom tears it.
        file.write_all(line.as_bytes()).map_err(io_err)?;
        self.joins
            .record(local.clone(), canonical.clone(), fingerprint);
        self.insert_map(local, canonical)
    }

    /// Whether the local operation `op` is a join point, which a canonical join operation
    /// stands for.
    pub(super) fn is_join_point(&self, op: &jj_lib::operation::Operation) -> bool {
        self.joins.join_of(op.store_operation()).is_some()
    }

    /// Whether this repository has history it shared with a hive: a join point, or a
    /// canonical operation. The canonical store, unlike the translation cache, is never lost,
    /// but [`Self::discard_shared_history`] drops both.
    fn has_shared_history(&self) -> Result<bool, NodeError> {
        Ok(!self.joins.is_empty() || self.canonical.has_operations()?)
    }

    /// The history this repository shared with hives before, which a join carries into the
    /// hive it joins: how many operations it has, and the ids of the hives it joined. `None`
    /// if it has none.
    pub fn shared_history(&self) -> Result<Option<SharedHistory>, NodeError> {
        if !self.has_shared_history()? {
            return Ok(None);
        }
        let ids = self.canonical.operation_ids()?;
        let mut hives = BTreeSet::new();
        for id in &ids {
            let op = self.canonical.read_operation(id)?;
            if let Some(hive) = op.metadata.attributes.get(JOIN_HIVE) {
                hives.insert(hive.clone());
            }
        }
        Ok(Some(SharedHistory {
            operations: ids.len(),
            hives,
        }))
    }

    /// Whether `head` descends from history this repository shared with a hive: an operation
    /// canonicalized already, a realization of another machine's, or a join point, as
    /// `canonicalize` knows them.
    fn descends_from_canonical(&self, head: &LocalOp) -> Result<bool, NodeError> {
        // A repository that never shared anything has none, and needn't walk its history.
        if !self.has_shared_history()? {
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
            let op = op_store.read_operation(&id.0).block_on()?;
            if OpAttrs(&op.metadata.attributes).canonical().is_some()
                || self.joins.join_of(&op).is_some()
            {
                return Ok(true);
            }
            stack.extend(LocalOp::parents_of(&op));
        }
        Ok(false)
    }

    /// Drops the history the repository whose `.jj/repo` directory is `repo_path` shared with
    /// hives: its canonical operations, join records and translations, and what it knows of
    /// what a hub took, so that it next joins as a repository that never shared any does,
    /// with a join operation on the root. Its own operation log and the keys it retired stay.
    /// For a repository that is part of no hive, under the join lock.
    ///
    /// Marked first, and the mark removed last: some of it gone, the rest would make a join
    /// carry a history with holes, so a join that finds the mark finishes this first
    /// ([`Self::discarding_shared_history`]).
    pub fn discard_shared_history(
        repo_path: &Path,
        mut after: impl FnMut(Discarded),
    ) -> Result<(), NodeError> {
        let dir = repo_path.join("musubi");
        let mark = dir.join(DISCARDING);
        let io = |path: &Path| {
            let path = path.to_owned();
            move |source| NodeError::Io { path, source }
        };
        let present: Vec<PathBuf> = SHARED_HISTORY
            .iter()
            .map(|name| dir.join(name))
            .filter(|path| path.symlink_metadata().is_ok())
            .collect();
        if present.is_empty() && !mark.exists() {
            return Ok(());
        }
        fs::write(&mark, b"").map_err(io(&mark))?;
        after(Discarded::Marked);
        for (i, path) in present.iter().enumerate() {
            let removed = if path.is_dir() {
                fs::remove_dir_all(path)
            } else {
                fs::remove_file(path)
            };
            match removed {
                Ok(()) => {}
                Err(err) if err.kind() == io::ErrorKind::NotFound => {}
                Err(err) => return Err(io(path)(err)),
            }
            if i == 0 {
                after(Discarded::Some);
            }
        }
        after(Discarded::All);
        fs::remove_file(&mark).map_err(io(&mark))?;
        after(Discarded::Done);
        Ok(())
    }

    /// Whether [`Self::discard_shared_history`] stopped partway in the repository whose
    /// `.jj/repo` directory is `repo_path`.
    pub fn discarding_shared_history(repo_path: &Path) -> bool {
        repo_path.join("musubi").join(DISCARDING).exists()
    }

    /// Creates the canonical operation that replicates this repository's current state in
    /// place of its operation history, and records that the current op head canonicalizes
    /// to it. See "Joining" in docs/internals/design.md.
    pub fn create_join_operation(&mut self, description: &str) -> Result<CanonicalOp, NodeError> {
        let remotes = JoinRemotes::from_remotes(&self.remotes()?);
        self.create_join_operation_with_remotes(description, "", &remotes)
    }

    /// Records exactly the snapshot approved by the hub's join preflight.
    pub fn create_join_operation_with_remotes(
        &mut self,
        description: &str,
        hive: &str,
        remotes: &JoinRemotes,
    ) -> Result<CanonicalOp, NodeError> {
        let head = self.merge_heads()?;
        // A repository that was part of a hive before, and left, has canonical history
        // already: if its head descends from it, carry on from it, as any operation does. A
        // join operation on the root would hide that history from the head, and the head the
        // old hub last accepted, which this node keeps, would no longer be reachable from it:
        // which musubi takes for an op abandon, whichever hive the repository joins.
        // A repository that discarded its shared history joins as one that never had any,
        // though it keeps the keys it retired.
        let carried = match self.canonical_of(&head) {
            Some(canonical) => Some(canonical),
            None if self.has_shared_history()?
                && (self.identities.has_retired_keys()
                    || self.descends_from_canonical(&head)?) =>
            {
                Some(self.canonicalize(&head)?)
            }
            None => None,
        };
        if carried.is_some() {
            return self.mark_joined_with_remotes(description, hive, remotes);
        }
        let head = self.forget_workspaces_left_behind(head)?;
        let op = self.loader.op_store().read_operation(&head.0).block_on()?;
        self.check_format(&head, &op)?;
        let view = self.loader.op_store().read_view(&op.view_id).block_on()?;
        let root = self.canonical.root_operation_id().clone();
        // Joining is this machine's work: it is present from its join on.
        let mut attributes = BTreeMap::from([(
            presence::WORK_ATTRIBUTE.to_owned(),
            self.machine.key().to_owned(),
        )]);
        attributes.extend(remotes.attributes(hive));
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
            parents: vec![root.0],
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
        let work = crate::canonical::Work::of(&self.canonical, &canonical)?;
        self.remember_presence(canonical.clone(), presence.apply(&work, &kind));
        self.record_join(head, &op, canonical.clone())?;
        // Start provenance before a first fetch can write accepted_base. A fresh member
        // must not be mistaken for an older sender when its first publication is held.
        self.initialize_publication_offers()?;
        Ok(canonical)
    }

    /// Removes, before a join on the root, other machines' workspaces that `head` still shows,
    /// as in a copy that discarded the history it shared ([`Self::discard_shared_history`]),
    /// which nothing would remove otherwise: the hive it joins shows its own machines' again.
    /// A name with a `/` is never this machine's own, but for one jj's workspace store records
    /// a directory for, which joining refuses ([`Self::slashed_workspaces`]) and this keeps.
    /// Returns the head to join at.
    fn forget_workspaces_left_behind(&mut self, head: LocalOp) -> Result<LocalOp, NodeError> {
        let own: BTreeSet<String> = self
            .slashed_workspaces()?
            .iter()
            .flat_map(|slashed| slashed.workspaces().map(|(name, _)| name.to_owned()))
            .collect();
        let repo = self.repo_at(&head)?;
        let left: Vec<_> = repo
            .view()
            .wc_commit_ids()
            .keys()
            .filter(|name| name.as_str().contains('/') && !own.contains(name.as_str()))
            .cloned()
            .collect();
        if left.is_empty() {
            return Ok(head);
        }
        let mut tx = repo.start_transaction();
        for name in &left {
            tx.repo_mut()
                .remove_workspace(name)
                .block_on()
                .map_err(index_err)?;
        }
        tx.repo_mut().rebase_descendants().block_on()?;
        let repo = tx
            .commit("musubi: forget the workspaces of machines of another hive")
            .block_on()?;
        Ok(LocalOp(repo.op_id().clone()))
    }

    /// Records an explicit join as this machine's work and its current URL hints, even
    /// when it is already present. Returns the canonical form of the new op head.
    pub fn mark_joined(&mut self, description: &str) -> Result<CanonicalOp, NodeError> {
        let remotes = JoinRemotes::from_remotes(&self.remotes()?);
        self.mark_joined_with_remotes(description, "", &remotes)
    }

    /// Records exactly the snapshot approved by the hub's join preflight.
    pub fn mark_joined_with_remotes(
        &mut self,
        description: &str,
        hive: &str,
        remotes: &JoinRemotes,
    ) -> Result<CanonicalOp, NodeError> {
        let head = self.merge_heads()?;
        let repo = self.repo_at(&head)?;
        let mut tx = repo.start_transaction();
        tx.set_attribute(
            presence::WORK_ATTRIBUTE.to_owned(),
            self.machine.key().to_owned(),
        );
        for (key, url) in remotes.attributes(hive) {
            tx.set_attribute(key, url);
        }
        let joined = tx.commit(description).block_on()?;
        self.canonicalize(&LocalOp(joined.op_id().clone()))
    }

    /// Restores known name constraints before remaking a lost hub. This runs only for an
    /// explicit rejoin, never on ordinary syncs; no mutable config or journal is written.
    pub fn check_recorded_remote_bindings(
        &self,
        hive: &str,
        remotes: &mut JoinRemotes,
    ) -> Result<(), NodeError> {
        let mut conflicts = BTreeSet::new();
        for id in self.canonical.operation_ids()? {
            let op = self.canonical.read_operation(&id)?;
            if op.metadata.attributes.get(JOIN_HIVE).map(String::as_str) != Some(hive) {
                continue;
            }
            for (name, binding) in JoinRemotes::recorded_bindings(&op.metadata.attributes) {
                if remotes
                    .bindings
                    .get(&name)
                    .is_some_and(|old| old != &binding)
                {
                    conflicts.insert(name);
                } else {
                    remotes.bindings.insert(name, binding);
                }
            }
        }
        if !conflicts.is_empty() {
            return Err(NodeError::RemoteBindings(
                conflicts.into_iter().collect::<Vec<_>>().join(", "),
            ));
        }
        Ok(())
    }

    fn remotes(&self) -> Result<BTreeMap<String, Remote>, NodeError> {
        Ok(match &self.git {
            Some(git) => git.remotes()?,
            None => BTreeMap::new(),
        })
    }

    /// What a hub needs to know to decide which hive this repository belongs to.
    pub fn join_summary(&self) -> Result<JoinSummary, NodeError> {
        self.check_complete()?;
        let repo = self.load_head(None)?;
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
fn parse_joins(bytes: &[u8]) -> Vec<(LocalOp, CanonicalOp, String)> {
    String::from_utf8_lossy(bytes)
        .lines()
        .filter_map(|line| {
            let [local, canonical, fingerprint] = *line.split(' ').collect::<Vec<_>>() else {
                return None;
            };
            whole_id(fingerprint)?;
            Some((
                LocalOp(whole_id(local)?),
                CanonicalOp(whole_id(canonical)?),
                fingerprint.to_owned(),
            ))
        })
        .collect()
}

/// This repository's join points, the canonical join operations they stand for, and the
/// history from before them. `ancestors` is kept until a join point is recorded; `before` is
/// never forgotten.
#[derive(Default)]
pub(super) struct Joins {
    /// The canonical join operation each join point maps to, by the join point's
    /// fingerprint, so that a copy of it that `jj op abandon` rewrote maps there too.
    by_fingerprint: BTreeMap<String, CanonicalOp>,
    /// The local join points, as recorded.
    pub(super) points: Vec<LocalOp>,
    /// The ancestors of the join points, once needed: the history from before the joins.
    pub(super) ancestors: Option<Arc<HashSet<LocalOp>>>,
    /// Local operations found to come from before this repository joined: ancestors of a
    /// join point, and operations all of whose parents are (see [`NodeRepo::canonicalize`]).
    pub(super) before: BTreeSet<LocalOp>,
}

impl Joins {
    /// Records the join point `local`, whose fingerprint is `fingerprint`, as standing for
    /// the canonical join operation `canonical`.
    pub(super) fn record(&mut self, local: LocalOp, canonical: CanonicalOp, fingerprint: String) {
        self.by_fingerprint.insert(fingerprint, canonical);
        self.points.push(local);
        self.ancestors = None;
    }

    /// Whether this repository has joined no hive.
    pub(super) fn is_empty(&self) -> bool {
        self.by_fingerprint.is_empty()
    }

    /// The canonical join operation the local operation `op` stands for, if it is a join
    /// point or a copy of one that `jj op abandon` rewrote.
    pub(super) fn join_of(&self, op: &StoreOperation) -> Option<&CanonicalOp> {
        // Fingerprinting hashes the whole operation: not for a repository that never joined.
        if self.is_empty() {
            return None;
        }
        self.by_fingerprint.get(&fingerprint(op))
    }

    /// Whether `canonical` is a join operation a join point here stands for.
    pub(super) fn is_join(&self, canonical: &CanonicalOp) -> bool {
        self.by_fingerprint.values().any(|join| join == canonical)
    }
}

/// What identifies an operation apart from its parents: its view, metadata, and the
/// rewrites it records. `jj op abandon` changes only the parents of the operations it
/// rewrites. The local marker used to keep a restored op head distinct preserves this
/// identity too.
pub(super) fn fingerprint(op: &StoreOperation) -> String {
    let mut without_parents = StoreOperation {
        parents: vec![],
        ..op.clone()
    };
    OpAttrs(&mut without_parents.metadata.attributes).remove_reconciled_from();
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
            let (local, canonical) = (LocalOp(id(3 * i)), CanonicalOp(id(3 * i + 1)));
            let fingerprint = id(3 * i + 2).hex();
            let line = format!("{} {} {fingerprint}", local.0.hex(), canonical.0.hex());
            let is_torn = tc.draw(gs::booleans());
            if is_torn {
                let cut = tc.draw(gs::integers::<usize>().max_value(line.len() - 1));
                text.push_str(&line[..cut]);
            } else {
                text.push_str(&line);
                whole.push((local, canonical, fingerprint));
            }
            let ended = i + 1 < lines || tc.draw(gs::booleans());
            if ended {
                text.push('\n');
            }
        }
        assert_eq!(parse_joins(text.as_bytes()), whole);
    }
}
