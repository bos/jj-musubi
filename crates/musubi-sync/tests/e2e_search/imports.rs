//! No spurious revert: every change a machine's import of git refs makes to a bookmark,
//! remote bookmark or tag follows a move of that ref in this machine's `.git` since jj last
//! imported there (`noSpuriousRevert` and `remoteNoSpuriousRevert` in
//! `formal/Musubi/Refs.lean`).
//!
//! In a colocated repository every `jj` command imports any difference between its op
//! head's record of git's refs and `.git` as a change made with git, and jj writes that
//! import as an operation of its own, "import git refs" (`import_git_refs` in jj-cli's
//! `cli_util.rs`). A record musubi got wrong is imported as a move nobody made, which then
//! replicates to every machine. The reference (`reference.rs`) can't judge imports, since
//! each machine's `.git` differs, so this does, operation by operation: the search itself
//! makes every move git makes of a machine's refs outside `jj` (`git_set_branch` and
//! `git_delete_branch`); `jj git fetch` and `jj git push` move refs and record them in the
//! same operation, and musubi writes `.git` only through jj's export, or with
//! `export_conflicted_remote_bookmarks`.
//!
//! jj 0.47 selects refs to import by comparing their physical values with `git_refs`.
//! A conflicted remote bookmark or an undo that changes only a remote bookmark does not
//! cause an import. A git move explains a change when `git_refs` matched `.git` before it.
//! With no git move, the only allowed explanation is jj's merge of concurrent op heads
//! that both changed `git_refs`, even if one changed it back (`concurrent_records_revert`).
//! Every record along that history must come from a native import, export or fetch, or a
//! merge of those records. Merges of more heads at once, or with closest common ancestors
//! that disagree, aren't modeled, and fail as unexplained.
//!
//! Anything else is a finding: the operation that left the record differing from `.git`, if
//! any, is named in the failure.
//!
//! Each import is judged once, against the parent it was written on: `jj op abandon` gives the
//! operations after the one it abandons new parents, and so new ids, but keeps their metadata
//! and views, and an import judged again against its new parent would seem to make what the
//! abandoned operation made.
//!
//! Imports of git's HEAD are checked the same way. Every `jj` command first compares its op
//! head's record of the workspace's HEAD (`git_heads`) with `.git`'s, and where they differ
//! writes "import git head", which takes `.git`'s and moves the working copy onto it, making a
//! new working-copy commit (`import_git_head` in jj-cli's `cli_util.rs`). git moves HEAD here
//! only where it is still a symbolic ref to the branch git moves, as it is in a new repository
//! until jj first writes it; the import then takes that move, as for a ref. Otherwise jj writes
//! HEAD only as it records it, in the same operation (`reset_head` in jj-lib's `git.rs`), so
//! the record matches `.git` but where jj's merge of two op heads that both changed it made it
//! something else, `.git` having one head's: as after a command at an older operation
//! (`--at-op`), which still writes HEAD, without checking it where the older operation has no
//! record of it, as for a workspace renamed since; jj merges it with the operations made since.
//! A record musubi got wrong would move a working copy with nobody having moved HEAD, and bring
//! back any rewritten commit it moved onto, which then diverges.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use std::sync::Arc;

use futures::executor::block_on;
use jj_lib::backend::CommitId;
use jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::RefTarget;
use jj_lib::op_store::RemoteRefState;
use jj_lib::op_store::View;
use jj_lib::ref_name::GitRefName;
use jj_lib::ref_name::RefName;
use jj_lib::ref_name::RemoteName;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::refs::merge_ref_targets;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use jj_lib::repo::RepoLoader;
use musubi_jj::node::CANONICAL_ATTRIBUTE;

use crate::coverage::fired;
use crate::view::ROOT;
use crate::world::World;

const ORIGIN: &str = "origin";

/// Descriptions of the operations that restore an older view: jj's undo, redo, `op restore`
/// and `op revert`.
const RESTORES: &[&str] = &["undo", "redo", "restore to operation", "revert operation"];

#[derive(Default)]
pub struct Imports {
    /// Whether the setup's operations are recorded, and later ones checked.
    started: bool,
    /// Each machine's operations at setup, where the walk back stops.
    setup: Vec<HashSet<OperationId>>,
    /// Each machine's operations already looked at.
    seen: Vec<HashSet<OperationId>>,
    /// Each machine's imports already judged, by their native command metadata. The seeded
    /// command clock gives each import its own times; contraction and per-machine exports
    /// can change both parents and views without running another import (`judged_key`).
    judged: Vec<HashSet<String>>,
    /// Each machine's git refs that git moved since jj last imported there, with what `.git`
    /// had before each of those moves.
    moved: Vec<BTreeMap<String, Vec<RefTarget>>>,
    /// Each machine's HEAD, where git moved it through the branch it is a symbolic ref to,
    /// since jj last imported it, by its workspace's name: what HEAD had before each move.
    head_moved: Vec<BTreeMap<String, Vec<RefTarget>>>,
}

/// A ref an import compares with `.git`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Kind {
    /// `x@git`, for bookmark `x`.
    Bookmark,
    /// `x@origin`.
    Remote,
    /// `x@git`, for tag `x`.
    Tag,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct Ref {
    kind: Kind,
    name: String,
}

impl Ref {
    fn git_ref(&self) -> String {
        match self.kind {
            Kind::Bookmark => format!("refs/heads/{}", self.name),
            Kind::Remote => format!("refs/remotes/{ORIGIN}/{}", self.name),
            Kind::Tag => format!("refs/tags/{}", self.name),
        }
    }

    /// The remote ref the import compares with `.git`.
    fn remote<'a>(&self, view: &'a View) -> Option<&'a RefTarget> {
        let remote = match self.kind {
            Kind::Remote => RemoteName::new(ORIGIN),
            Kind::Bookmark | Kind::Tag => REMOTE_NAME_FOR_LOCAL_GIT_REPO,
        };
        let remote = view.remote_views.get(remote)?;
        let refs = match self.kind {
            Kind::Tag => &remote.tags,
            Kind::Bookmark | Kind::Remote => &remote.bookmarks,
        };
        refs.get(RefName::new(&self.name)).map(|r| &r.target)
    }

    /// Whether the remote ref is tracked, so that the import merges its changes into the
    /// bookmark (`tracked_target` in `import_refs`).
    fn tracked(&self, view: &View) -> bool {
        let remote = match self.kind {
            Kind::Remote => RemoteName::new(ORIGIN),
            Kind::Bookmark | Kind::Tag => REMOTE_NAME_FOR_LOCAL_GIT_REPO,
        };
        view.remote_views
            .get(remote)
            .and_then(|remote| remote.bookmarks.get(RefName::new(&self.name)))
            .is_some_and(|r| r.state == RemoteRefState::Tracked)
    }

    /// What jj exports to the ref: the bookmark or tag, or the remote bookmark itself.
    fn local(&self, view: &View) -> RefTarget {
        let target = match self.kind {
            Kind::Bookmark => view.local_bookmarks.get(RefName::new(&self.name)),
            Kind::Tag => view.local_tags.get(RefName::new(&self.name)),
            Kind::Remote => self.remote(view),
        };
        target.cloned().unwrap_or_else(RefTarget::absent)
    }

    /// jj's record of the ref: the remote ref, and `git_refs`.
    fn record(&self, view: &View) -> Record {
        let absent = RefTarget::absent();
        Record(
            self.remote(view).cloned().unwrap_or_else(|| absent.clone()),
            view.git_refs
                .get(GitRefName::new(&self.git_ref()))
                .cloned()
                .unwrap_or(absent),
        )
    }
}

impl fmt::Display for Ref {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            Kind::Bookmark | Kind::Tag => write!(f, "{}@git", self.name),
            Kind::Remote => write!(f, "{}@{ORIGIN}", self.name),
        }
    }
}

#[derive(PartialEq, Eq)]
struct Record(RefTarget, RefTarget);

impl fmt::Display for Record {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} (git_refs {})", show(&self.0), show(&self.1))
    }
}

fn show(target: &RefTarget) -> String {
    if target.is_absent() {
        return "absent".to_owned();
    }
    target
        .iter()
        .map(|id| {
            id.as_ref()
                .map_or("-".to_owned(), |id| id.hex()[..12].to_owned())
        })
        .collect::<Vec<_>>()
        .join(",")
}

/// Whether jj's export can write `target`: not a conflict, nor the root commit
/// (`collect_changed_refs_to_export` in jj-lib's `git.rs`).
fn exportable(target: &RefTarget) -> bool {
    target.is_absent() || target.as_normal().is_some_and(|id| id.hex() != ROOT)
}

/// One of jj's undo, redo, `op restore` or `op revert`.
fn restore(op: &op_store::Operation) -> bool {
    RESTORES
        .iter()
        .any(|prefix| op.metadata.description.starts_with(prefix))
}

/// Whose a marked operation is, to tell a machine's own from a realization of another's
/// (`world::realized`): the machine's key and host, and each canonical operation's work.
struct Owner {
    key: String,
    host: String,
    works: HashMap<String, Option<String>>,
}

/// Whether `op` is the machine's own rather than a realization of another machine's.
fn own(owner: &Owner, op: &op_store::Operation) -> bool {
    let Some(canonical) = op.metadata.attributes.get(CANONICAL_ATTRIBUTE) else {
        return true;
    };
    match owner.works.get(canonical) {
        Some(Some(work)) => *work == owner.key,
        Some(None) => op.metadata.hostname == owner.host,
        None => false,
    }
}

fn own_import(owner: &Owner, op: &op_store::Operation) -> bool {
    own(owner, op) && op.metadata.description.starts_with("import git refs")
}

/// One of this machine's own imports of git's HEAD.
fn own_head_import(owner: &Owner, op: &op_store::Operation) -> bool {
    own(owner, op) && op.metadata.description.starts_with("import git head")
}

/// An operation a `jj` command of this machine's made, which names its workspace, unlike
/// musubi's own.
fn jj_command(owner: &Owner, op: &op_store::Operation) -> bool {
    own(owner, op) && op.metadata.workspace_name.is_some()
}

/// jj's record of workspace `ws`'s HEAD in `view`.
fn head(view: &View, ws: &str) -> RefTarget {
    view.git_heads
        .get(WorkspaceName::new(ws))
        .cloned()
        .unwrap_or_else(RefTarget::absent)
}

/// A native import's identity across contraction and per-machine export. Each command gets
/// unique seeded times, and its ref and HEAD imports have distinct descriptions. A rewritten
/// representation can have a different view as well as parents; neither is a new import.
fn judged_key(op: &op_store::Operation) -> String {
    let metadata = &op.metadata;
    format!(
        "{} {} {} {} {}",
        metadata.time.start.timestamp.0,
        metadata.time.end.timestamp.0,
        metadata.hostname,
        metadata.username,
        metadata.description,
    )
}

fn describe(owner: &Owner, id: &OperationId, op: &op_store::Operation) -> String {
    format!(
        "\"{}\" ({}{})",
        op.metadata.description.lines().next().unwrap_or_default(),
        &id.hex()[..12],
        if own(owner, op) {
            ""
        } else {
            ", a realization"
        }
    )
}

/// What one check reads of a machine's operation log, cached.
struct Log {
    /// Whose its marked operations are.
    owner: Owner,
    loader: RepoLoader,
    store: Arc<dyn op_store::OpStore>,
    ops: HashMap<OperationId, op_store::Operation>,
    views: HashMap<OperationId, View>,
    repos: HashMap<OperationId, Arc<ReadonlyRepo>>,
    native_sources: BTreeMap<String, op_store::Operation>,
    validated: HashSet<(OperationId, RecordKind)>,
    head_writers: HashMap<(OperationId, String), Arc<HashSet<Option<CommitId>>>>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum RecordKind {
    Ref(Ref),
    Head(String),
}

impl Log {
    /// Possible physical HEAD values come from native writers, not from the value a merge
    /// computes for jj's record. Even a resolved record can be synthesized by cancellation.
    fn possible_heads(
        &mut self,
        id: &OperationId,
        ws: &str,
        setup: &HashSet<OperationId>,
    ) -> Result<Arc<HashSet<Option<CommitId>>>, String> {
        let wanted = (id.clone(), ws.to_owned());
        let mut pending = vec![(wanted.clone(), false)];
        let mut visiting = HashSet::new();
        while let Some((key, ready)) = pending.pop() {
            if self.head_writers.contains_key(&key) {
                continue;
            }
            let (id, ws) = &key;
            let op = self.record_operation(id);
            let now = self.head(id, ws);
            let renamed = op
                .metadata
                .description
                .strip_prefix("Renamed workspace '")
                .and_then(|rest| rest.strip_suffix(&format!("' to '{ws}'")));
            let writes = renamed.is_none()
                && op.parents.len() == 1
                && !op.metadata.attributes.contains_key(CANONICAL_ATTRIBUTE)
                && jj_command(&self.owner, &op)
                && op
                    .metadata
                    .workspace_name
                    .as_ref()
                    .is_some_and(|name| name.as_str() == ws)
                && (!now.is_absent() || own_head_import(&self.owner, &op))
                && (own_head_import(&self.owner, &op) || self.head(&op.parents[0], ws) != now);
            if now.is_resolved()
                && (setup.contains(id) || writes || id == self.store.root_operation_id())
            {
                self.head_writers
                    .insert(key, Arc::new(HashSet::from([now.as_normal().cloned()])));
                continue;
            }
            let parents: Vec<_> = op
                .parents
                .iter()
                .map(|parent| (parent.clone(), renamed.unwrap_or(ws).to_owned()))
                .collect();
            if ready {
                let mut values = HashSet::new();
                for parent in parents {
                    values.extend(self.head_writers[&parent].iter().cloned());
                }
                self.head_writers.insert(key.clone(), Arc::new(values));
                visiting.remove(&key);
            } else {
                if !visiting.insert(key.clone()) {
                    return Err("physical HEAD provenance has a cycle".to_owned());
                }
                pending.push((key, true));
                pending.extend(parents.into_iter().rev().map(|parent| (parent, false)));
            }
        }
        Ok(self.head_writers[&wanted].clone())
    }

    fn record_operation(&mut self, id: &OperationId) -> op_store::Operation {
        let op = self.op(id).clone();
        self.native_sources
            .get(&crate::world::merge_key(&op))
            .filter(|source| !source.metadata.attributes.contains_key(CANONICAL_ATTRIBUTE))
            .filter(|source| crate::world::same_source_body(source, &op))
            .cloned()
            .unwrap_or(op)
    }

    /// Validate the whole provenance of a record, including ancestors a trim erased from
    /// physical history. A matching source body authenticates bytes, not their correctness.
    fn validate_record(
        &mut self,
        id: &OperationId,
        setup: &HashSet<OperationId>,
        record: &RecordKind,
    ) -> Result<(), String> {
        let mut pending = vec![(id.clone(), false)];
        let mut visiting = HashSet::new();
        while let Some((id, ready)) = pending.pop() {
            let key = (id.clone(), record.clone());
            if id == *self.store.root_operation_id()
                || setup.contains(&id)
                || self.validated.contains(&key)
            {
                continue;
            }
            if ready {
                self.validated.insert(key);
                visiting.remove(&id);
                continue;
            }
            if !visiting.insert(id.clone()) {
                return Err("the record's source history has a cycle".to_owned());
            }
            match record {
                RecordKind::Ref(r) => self.plausible(&id, r)?,
                RecordKind::Head(ws) => self.head_plausible(&id, ws)?,
            }
            let op = self.record_operation(&id);
            pending.push((id, true));
            pending.extend(op.parents.into_iter().rev().map(|p| (p, false)));
        }
        Ok(())
    }

    fn op(&mut self, id: &OperationId) -> &op_store::Operation {
        self.ops
            .entry(id.clone())
            .or_insert_with(|| block_on(self.store.read_operation(id)).unwrap())
    }

    fn view(&mut self, id: &OperationId) -> &View {
        if !self.views.contains_key(id) {
            let view_id = self.op(id).view_id.clone();
            let view = block_on(self.store.read_view(&view_id)).unwrap();
            self.views.insert(id.clone(), view);
        }
        &self.views[id]
    }

    fn record(&mut self, id: &OperationId, r: &Ref) -> Record {
        r.record(self.view(id))
    }

    /// Whether any operation after `before` (the bases and their ancestors) up to `op`
    /// (included) records `r` other than as `base`: whether that head changed the record since
    /// the fork, as `touch` has it in `Refs.lean`, even if it changed it back. Every one that
    /// changed it must have done so as jj does (`plausible`), since the model's merge
    /// assumes both heads reachable (`FReach`).
    fn touched(
        &mut self,
        op: &OperationId,
        before: &HashSet<OperationId>,
        setup: &HashSet<OperationId>,
        r: &Ref,
        base: &Record,
    ) -> Result<bool, String> {
        let mut pending = vec![op.clone()];
        let mut visited = HashSet::new();
        let mut touched = false;
        while let Some(id) = pending.pop() {
            if before.contains(&id) || !visited.insert(id.clone()) {
                continue;
            }
            touched |= self.record(&id, r).1 != base.1;
            if setup.contains(&id) {
                continue;
            }
            self.validate_record(&id, setup, &RecordKind::Ref(r.clone()))?;
            pending.extend(self.op(&id).parents.iter().cloned());
        }
        Ok(touched)
    }

    /// An operation that changed the record of `r` did so as jj does: an import, a restore of
    /// what the export can't write, an export or fetch that wrote it, or for a merge, one
    /// parent's record or jj's merge of two. The remote's conflicts are exported by musubi
    /// instead.
    fn plausible(&mut self, id: &OperationId, r: &Ref) -> Result<(), String> {
        let op = self.record_operation(id);
        let now = self.record(id, r);
        let local = r.local(self.view(id));
        // As an export that wrote the ref leaves it: in step with `git_refs` and the bookmark,
        // tag or remote bookmark. jj's export leaves a ref it can't write alone. musubi exports
        // its merges too (`Colocation::export_refs`).
        let exported = exportable(&local) && now.0 == now.1 && now.0 == local;
        let [parent] = op.parents.as_slice() else {
            // A merge takes one parent's record, makes jj's merge of two, or exports.
            if exported || op.parents.iter().any(|p| self.record(p, r) == now) {
                return Ok(());
            }
            let bases = self.bases(&op.parents);
            let base = bases.first().map(|b| self.record(b, r));
            if let ([left, right], Some(base)) = (op.parents.as_slice(), base)
                && bases.iter().all(|b| self.record(b, r) == base)
                && self.merge(id, r, left, &base, right) == now
            {
                return Ok(());
            }
            return Err(format!(
                "the merge {} made jj's record of {r} {now}, which isn't jj's merge of its \
                 parents'",
                describe(&self.owner, id, &op)
            ));
        };
        // A restore whose export could write the bookmark leaves it as an export does.
        if self.record(parent, r) == now
            || own_import(&self.owner, &op)
            || own(&self.owner, &op) && restore(&op) && !exportable(&local)
            || r.kind == Kind::Remote && !now.0.is_resolved()
        {
            return Ok(());
        }
        if exported {
            return Ok(());
        }
        Err(format!(
            "{} left jj's record of {r} {now}, as no export or fetch does",
            describe(&self.owner, id, &op)
        ))
    }

    fn head(&mut self, id: &OperationId, ws: &str) -> RefTarget {
        head(self.view(id), ws)
    }

    /// [`Self::touched`], for the record of workspace `ws`'s HEAD: whether any operation after
    /// `before` up to `op` records it other than as `base`. Only a `jj` command changes it, as it
    /// writes or imports HEAD, or adds, renames or forgets the workspace: a realization, or an
    /// operation of musubi's own, keeps its parent's, and a merge takes one parent's or jj's
    /// merge of two.
    fn head_touched(
        &mut self,
        op: &OperationId,
        before: &HashSet<OperationId>,
        setup: &HashSet<OperationId>,
        ws: &str,
        base: &RefTarget,
    ) -> Result<bool, String> {
        let mut pending = vec![op.clone()];
        let mut visited = HashSet::new();
        let mut touched = false;
        while let Some(id) = pending.pop() {
            if before.contains(&id) || !visited.insert(id.clone()) {
                continue;
            }
            let now = self.head(&id, ws);
            touched |= now != *base;
            if setup.contains(&id) {
                continue;
            }
            self.validate_record(&id, setup, &RecordKind::Head(ws.to_owned()))?;
            let op = self.op(&id).clone();
            pending.extend(op.parents.iter().cloned());
        }
        Ok(touched)
    }

    fn head_plausible(&mut self, id: &OperationId, ws: &str) -> Result<(), String> {
        let op = self.record_operation(id);
        let now = self.head(id, ws);
        let parents: Vec<RefTarget> = op.parents.iter().map(|p| self.head(p, ws)).collect();
        let plausible = match parents.as_slice() {
            [parent] => jj_command(&self.owner, &op) || *parent == now,
            [left, right] if !parents.contains(&now) => {
                let bases = self.bases(&op.parents);
                let base_heads: Vec<RefTarget> = bases.iter().map(|b| self.head(b, ws)).collect();
                match base_heads.first() {
                    Some(base) if base_heads.iter().all(|b| b == base) => {
                        self.merge_targets(id, left, base, right) == now
                    }
                    _ => false,
                }
            }
            _ => parents.contains(&now),
        };
        if !plausible {
            return Err(format!(
                "{} made jj's record of {ws}'s HEAD {}, as jj doesn't",
                describe(&self.owner, id, &op),
                show(&now)
            ));
        }
        Ok(())
    }

    /// jj's three-way merge of the records of `r` at `left` and `right` against `base`, as
    /// `merge_view` merges them (`merge_ref_targets`), with the commit index at `at`.
    fn merge(
        &mut self,
        at: &OperationId,
        r: &Ref,
        left: &OperationId,
        base: &Record,
        right: &OperationId,
    ) -> Record {
        let left = self.record(left, r);
        let right = self.record(right, r);
        Record(
            self.merge_targets(at, &left.0, &base.0, &right.0),
            self.merge_targets(at, &left.1, &base.1, &right.1),
        )
    }

    /// `merge_ref_targets`, with the commit index at `at`.
    fn merge_targets(
        &mut self,
        at: &OperationId,
        left: &RefTarget,
        base: &RefTarget,
        right: &RefTarget,
    ) -> RefTarget {
        if !self.repos.contains_key(at) {
            let op = block_on(self.loader.load_operation(at)).unwrap();
            let repo = block_on(self.loader.load_at(&op)).unwrap();
            self.repos.insert(at.clone(), repo);
        }
        block_on(merge_ref_targets(self.repos[at].index(), left, base, right)).unwrap()
    }

    /// `ops` and their ancestors.
    fn ancestors(&mut self, mut pending: Vec<OperationId>) -> HashSet<OperationId> {
        let mut ancestors = HashSet::new();
        while let Some(id) = pending.pop() {
            if ancestors.insert(id.clone()) {
                pending.extend(self.op(&id).parents.iter().cloned());
            }
        }
        ancestors
    }

    /// The closest common ancestors of `ops`.
    fn bases(&mut self, ops: &[OperationId]) -> Vec<OperationId> {
        let mut common: Option<HashSet<OperationId>> = None;
        for op in ops {
            let ancestors = self.ancestors(vec![op.clone()]);
            common = Some(match common {
                None => ancestors,
                Some(common) => common.intersection(&ancestors).cloned().collect(),
            });
        }
        let common = common.unwrap_or_default();
        let mut parents = vec![];
        for id in &common {
            parents.extend(self.op(id).parents.iter().cloned());
        }
        let below = self.ancestors(parents);
        let mut bases: Vec<OperationId> = common.difference(&below).cloned().collect();
        bases.sort();
        bases
    }
}

#[test]
fn physical_head_writers_are_distinct_from_merge_record_terms() {
    use crate::world::{Naming, Setup};

    let world = World::new(Setup {
        nodes: 3,
        naming: Naming::Default,
        prejoin: false,
        secondary: false,
    });
    let loader = world.fx.hive.members[0].adapter.repo().loader().clone();
    let store = loader.op_store().clone();
    let root = store.root_operation_id().clone();
    let native = OperationId::try_from_hex(world.latest_op_head(0)).unwrap();
    let template = block_on(store.read_operation(&native)).unwrap();
    let base_view = block_on(store.read_view(&template.view_id)).unwrap();
    let mut commits: Vec<_> = base_view.wc_commit_ids.values().cloned().collect();
    commits.sort();
    commits.dedup();
    assert!(commits.len() >= 3);
    let [a, x, c] = [0, 1, 2].map(|i| commits[i].clone());
    let target = |id: &CommitId| RefTarget::normal(id.clone());
    let make = |description: &str, record: RefTarget, parents: Vec<OperationId>, writer: bool| {
        let mut op = template.clone();
        op.metadata.attributes.clear();
        op.metadata.workspace_name = writer.then(|| WorkspaceName::DEFAULT.to_owned());
        op.metadata.description = description.to_owned();
        op.metadata.time.end.timestamp.0 += 1000;
        let mut view = base_view.clone();
        view.git_heads
            .insert(WorkspaceName::DEFAULT.to_owned(), record);
        op.view_id = block_on(store.write_view(&view)).unwrap();
        op.parents = parents;
        block_on(store.write_operation(&op)).unwrap()
    };
    // Native writers can be imports after explicit HEAD moves. A merge changes only the
    // record. jj's real ref merge below checks the cancellation counterexample.
    let wrote_x = make("import git head: X", target(&x), vec![root.clone()], true);
    let wrote_a = make(
        "import git head: A",
        target(&a),
        vec![wrote_x.clone()],
        true,
    );
    let wrote_c = make("import git head: C", target(&c), vec![wrote_x], true);
    let conflict =
        RefTarget::from_removes_adds([Some(x.clone())], [Some(a.clone()), Some(c.clone())]);
    let base = make(
        "reconcile divergent operations",
        conflict,
        vec![wrote_a, wrote_c.clone()],
        false,
    );
    let a_again = make(
        "import git head: A again",
        target(&a),
        vec![base.clone()],
        true,
    );
    let c_again = make("import git head: C again", target(&c), vec![base], true);
    let synthesized = make(
        "reconcile divergent operations",
        target(&x),
        vec![a_again.clone(), c_again.clone()],
        false,
    );
    let a_later = make("import git head: A later", target(&a), vec![wrote_c], true);
    let nested =
        RefTarget::from_removes_adds([Some(c.clone())], [Some(x.clone()), Some(a.clone())]);
    let final_merge = make(
        "reconcile divergent operations",
        nested,
        vec![synthesized.clone(), a_later],
        false,
    );
    let inherited = make(
        "describe commit without updating the working copy",
        target(&x),
        vec![synthesized.clone()],
        true,
    );
    let wrote_after = make(
        "reset git head after merge",
        target(&x),
        vec![final_merge.clone()],
        true,
    );
    let mut log = Log {
        owner: world.owner(0),
        loader,
        store,
        ops: HashMap::new(),
        views: HashMap::new(),
        repos: HashMap::new(),
        native_sources: BTreeMap::new(),
        validated: HashSet::new(),
        head_writers: HashMap::new(),
    };
    let setup = HashSet::from([root]);
    log.validate_record(
        &final_merge,
        &setup,
        &RecordKind::Head("default".to_owned()),
    )
    .unwrap();
    let op = log.op(&synthesized).clone();
    let bases = log.bases(&op.parents);
    let base_target = log.head(&bases[0], "default");
    assert_eq!(
        log.merge_targets(&synthesized, &target(&a), &base_target, &target(&c)),
        target(&x)
    );
    for id in [&synthesized, &final_merge, &inherited] {
        let possible = log.possible_heads(id, "default", &setup).unwrap();
        assert!(possible.contains(&Some(a.clone())));
        assert!(possible.contains(&Some(c.clone())));
        assert!(
            !possible.contains(&Some(x.clone())),
            "a synthesized record is no HEAD writer"
        );
    }
    assert_eq!(
        &*log.possible_heads(&wrote_after, "default", &setup).unwrap(),
        &HashSet::from([Some(x)])
    );
}

#[test]
fn trimmed_record_sources_preserve_provenance_without_hiding_invalid_ancestors() {
    use crate::world::{Naming, Setup};

    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Default,
        prejoin: true,
        secondary: false,
    });
    world.jj(0, &["bookmark", "create", "kept", "-r", "@"]);
    world.forget_copy(0, 1);
    let native = OperationId::try_from_hex(world.latest_op_head(0)).unwrap();
    let loader = world.fx.hive.members[0].adapter.repo().loader().clone();
    let store = loader.op_store().clone();
    let source = block_on(store.read_operation(&native)).unwrap();
    assert_eq!(source.metadata.description, "musubi: forget beta");
    world.trim_below_accepted_push(0);
    let sources = world.native_record_sources(0);
    let key = crate::world::merge_key(&source);
    assert!(sources.contains_key(&key));
    let root = store.root_operation_id().clone();
    let mut trimmed = source.clone();
    trimmed.parents = vec![root.clone()];
    let trimmed_id = block_on(store.write_operation(&trimmed)).unwrap();
    let view = block_on(store.read_view(&source.view_id)).unwrap();
    assert!(!head(&view, "default").is_absent());
    let records = [
        RecordKind::Head("default".to_owned()),
        RecordKind::Ref(Ref {
            kind: Kind::Bookmark,
            name: "kept".to_owned(),
        }),
    ];
    let log = |native_sources| Log {
        owner: world.owner(0),
        loader: loader.clone(),
        store: store.clone(),
        ops: HashMap::new(),
        views: HashMap::new(),
        repos: HashMap::new(),
        native_sources,
        validated: HashSet::new(),
        head_writers: HashMap::new(),
    };
    let setup = &world.imports.setup[0];
    for record in &records {
        log(sources.clone())
            .validate_record(&trimmed_id, setup, record)
            .unwrap();
    }
    let before = HashSet::from([root]);
    let mut checked = log(sources.clone());
    assert!(
        checked
            .head_touched(&trimmed_id, &before, setup, "default", &RefTarget::absent())
            .unwrap()
    );
    assert!(
        !checked
            .head_touched(
                &trimmed_id,
                &before,
                setup,
                "default",
                &head(&view, "default")
            )
            .unwrap()
    );
    assert!(
        log(BTreeMap::new())
            .validate_record(&trimmed_id, setup, &records[0])
            .is_err()
    );

    let write = |mut op: op_store::Operation, view: &View| {
        op.view_id = block_on(store.write_view(view)).unwrap();
        let id = block_on(store.write_operation(&op)).unwrap();
        (id, op)
    };
    let mut altered = view.clone();
    let other = loader.store().root_commit_id().clone();
    altered.git_heads.insert(
        WorkspaceName::DEFAULT.to_owned(),
        RefTarget::normal(other.clone()),
    );
    altered
        .git_refs
        .insert("refs/heads/kept".into(), RefTarget::normal(other));
    let (altered_id, _) = write(trimmed.clone(), &altered);
    let mut different_body = view.clone();
    different_body.local_bookmarks.insert(
        "extra".into(),
        RefTarget::normal(loader.store().root_commit_id().clone()),
    );
    let (different_body_id, _) = write(trimmed.clone(), &different_body);
    assert!(
        log(sources.clone())
            .validate_record(&different_body_id, setup, &records[0])
            .is_err()
    );
    for record in &records {
        assert!(
            log(sources.clone())
                .validate_record(&altered_id, setup, record)
                .is_err(),
            "altered record body"
        );
    }
    let mut collision = trimmed.clone();
    collision.metadata.username.push_str(" different user");
    let collision_id = block_on(store.write_operation(&collision)).unwrap();
    assert!(
        log(sources.clone())
            .validate_record(&collision_id, setup, &records[0])
            .is_err()
    );
    let mut marked = sources.clone();
    marked
        .get_mut(&key)
        .unwrap()
        .metadata
        .attributes
        .insert(CANONICAL_ATTRIBUTE.to_owned(), "not independent".to_owned());
    assert!(
        log(marked)
            .validate_record(&trimmed_id, setup, &records[0])
            .is_err()
    );

    // An exact captured source can itself be invalid, or inherit an invalid record from
    // an operation a trim removed. Validate both original histories rather than trusting
    // equality with the captured view or just with its immediate parent.
    let (_, invalid_source) = write(source.clone(), &altered);
    let mut invalid = sources.clone();
    invalid.insert(key.clone(), invalid_source);
    for record in &records {
        assert!(
            log(invalid.clone())
                .validate_record(&altered_id, setup, record)
                .is_err(),
            "invalid original transition"
        );
    }
    let mut ancestor = source.clone();
    ancestor.metadata.description = "musubi: forget hidden ancestor".to_owned();
    let (ancestor_id, ancestor) = write(ancestor, &altered);
    let mut inheriting = source;
    inheriting.parents = vec![ancestor_id];
    let (_, inheriting) = write(inheriting, &altered);
    invalid.insert(key, inheriting);
    invalid.insert(crate::world::merge_key(&ancestor), ancestor);
    assert!(
        log(invalid.clone())
            .head_plausible(&altered_id, "default")
            .is_ok()
    );
    if let RecordKind::Ref(r) = &records[1] {
        assert!(log(invalid.clone()).plausible(&altered_id, r).is_ok());
    }
    for record in &records {
        assert!(
            log(invalid.clone())
                .validate_record(&altered_id, setup, record)
                .is_err(),
            "invalid erased ancestor"
        );
    }
}

impl World {
    /// Starts the check: the operations so far are the setup's.
    pub fn start_imports(&mut self) {
        for m in 0..self.nodes() {
            self.imports.seen.push(HashSet::new());
            self.imports.judged.push(HashSet::new());
            self.imports.moved.push(BTreeMap::new());
            self.imports.head_moved.push(BTreeMap::new());
            self.check_imports(m);
            self.imports.setup.push(self.imports.seen[m].clone());
        }
        self.imports.started = true;
    }

    /// Starts again on machine `m`, a new copy that has just joined and synced: what its
    /// operations so far did is its setup's.
    pub fn restart_imports(&mut self, m: usize) {
        if m == self.imports.seen.len() {
            self.imports.seen.push(HashSet::new());
            self.imports.judged.push(HashSet::new());
            self.imports.moved.push(BTreeMap::new());
            self.imports.head_moved.push(BTreeMap::new());
            self.imports.setup.push(HashSet::new());
        }
        self.imports.seen[m].clear();
        self.imports.judged[m].clear();
        self.imports.moved[m].clear();
        self.imports.head_moved[m].clear();
        self.imports.started = false;
        self.check_imports(m);
        self.imports.started = true;
        self.imports.setup[m] = self.imports.seen[m].clone();
    }

    /// git is about to move `git_ref` on machine `m`: imports before now can't follow it.
    pub fn git_moves(&mut self, m: usize, git_ref: &str) {
        self.check_imports(m);
        let value = self
            .fx
            .repo(m)
            .git(&["for-each-ref", "--format=%(objectname)", git_ref]);
        let value = match value.trim() {
            "" => RefTarget::absent(),
            hex => RefTarget::normal(CommitId::try_from_hex(hex).unwrap()),
        };
        // A new repository's HEAD is a symbolic ref to `main` until jj first writes it.
        let head = std::fs::read_to_string(self.fx.repo(m).path().join(".git/HEAD")).unwrap();
        if head.trim().strip_prefix("ref: ") == Some(git_ref)
            && let Some(primary) = self.workspaces[m]
                .iter()
                .find(|ws| ws.path.is_none())
                .map(|ws| ws.name.clone())
        {
            self.imports.head_moved[m]
                .entry(primary)
                .or_default()
                .push(value.clone());
        }
        self.imports.moved[m]
            .entry(git_ref.to_owned())
            .or_default()
            .push(value);
    }

    /// Whose machine `m`'s marked operations are.
    fn owner(&self, m: usize) -> Owner {
        let node = self.fx.hive.members[m].adapter.repo();
        let store = node.canonical_store();
        let works = store
            .operation_ids()
            .unwrap()
            .into_iter()
            .filter_map(|id| {
                let op = store.read_operation(&id).ok()?;
                Some((id.0.hex(), musubi_jj::presence::Kind::of(&op.metadata).work))
            })
            .collect();
        let key = node.machine().key().to_owned();
        Owner {
            host: musubi_jj::workspaces::machine_name(&key).to_owned(),
            key,
            works,
        }
    }

    /// Checks machine `m`'s imports since the last check, oldest first.
    pub fn check_imports(&mut self, m: usize) {
        let loader = self.fx.hive.members[m].adapter.repo().loader().clone();
        let mut log = Log {
            owner: self.owner(m),
            store: loader.op_store().clone(),
            loader,
            ops: HashMap::new(),
            views: HashMap::new(),
            repos: HashMap::new(),
            native_sources: BTreeMap::new(),
            validated: HashSet::new(),
            head_writers: HashMap::new(),
        };
        let root = log.store.root_operation_id().clone();
        let mut new: Vec<OperationId> = vec![];
        let mut pending: Vec<OperationId> = self
            .op_heads(m)
            .iter()
            .map(|hex| OperationId::try_from_hex(hex).unwrap())
            .collect();
        while let Some(id) = pending.pop() {
            if id == root || !self.imports.seen[m].insert(id.clone()) {
                continue;
            }
            // A crash can lose the file of an operation nothing else refers to.
            let Ok(op) = block_on(log.store.read_operation(&id)) else {
                continue;
            };
            pending.extend(op.parents.iter().cloned());
            log.ops.insert(id.clone(), op);
            new.push(id);
        }
        if !self.imports.started {
            for id in &new {
                let op = &log.ops[id];
                if own_import(&log.owner, op) || own_head_import(&log.owner, op) {
                    self.imports.judged[m].insert(judged_key(op));
                }
            }
            return;
        }
        // Parents first.
        let mut done: HashSet<OperationId> = HashSet::new();
        let mut order = vec![];
        let new_set: HashSet<OperationId> = new.iter().cloned().collect();
        while order.len() < new.len() {
            for id in &new {
                if !done.contains(id)
                    && log.ops[id]
                        .parents
                        .iter()
                        .all(|p| !new_set.contains(p) || done.contains(p))
                {
                    done.insert(id.clone());
                    order.push(id.clone());
                }
            }
        }
        let mut failures = vec![];
        let mut sources_loaded = false;
        for id in order {
            let refs = own_import(&log.owner, &log.ops[&id]);
            if (!refs && !own_head_import(&log.owner, &log.ops[&id]))
                || !self.imports.judged[m].insert(judged_key(&log.ops[&id]))
            {
                continue;
            }
            if !sources_loaded {
                log.native_sources = self.native_record_sources(m);
                sources_loaded = true;
            }
            // Reading the log fails only if musubi lost an operation file it refers to.
            let checked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                if refs {
                    self.check_import(m, &mut log, &id)
                } else {
                    self.check_head_import(m, &mut log, &id)
                }
            }));
            match checked {
                Ok(Ok(())) => {}
                Ok(Err(failure)) => failures.push(failure),
                Err(panic) => failures.push(format!(
                    "checking the import {} failed: {}",
                    &id.hex()[..12],
                    panic
                        .downcast_ref::<String>()
                        .map(String::as_str)
                        .or_else(|| panic.downcast_ref::<&str>().copied())
                        .unwrap_or("a panic")
                )),
            }
            if refs {
                self.imports.moved[m].clear();
            } else if let Some(ws) = &log.ops[&id].metadata.workspace_name {
                self.imports.head_moved[m].remove(ws.as_str());
            }
        }
        if !failures.is_empty() {
            self.fail(&format!(
                "an import on {} changed what git didn't move:\n{}",
                self.machine(m),
                failures.join("\n")
            ));
        }
    }

    fn check_import(&self, m: usize, log: &mut Log, id: &OperationId) -> Result<(), String> {
        let native = self
            .commands
            .get(&crate::world::merge_key(log.op(id)))
            .map(|source| source.id.clone());
        let id = native.as_ref().unwrap_or(id);
        let op = log.op(id).clone();
        let [parent] = op.parents.as_slice() else {
            return Err(format!(
                "{} has several parents",
                describe(&log.owner, id, &op)
            ));
        };
        let before = log.view(parent).clone();
        let after = log.view(id).clone();
        // Each name the import changed, with the refs it compared that it changed.
        let mut changed: Vec<(String, Vec<Ref>)> = vec![];
        let names = |a: &View, b: &View, kind: Kind| -> BTreeSet<String> {
            let keys = |v: &View| -> Vec<String> {
                match kind {
                    Kind::Bookmark => v
                        .local_bookmarks
                        .keys()
                        .map(|n| n.as_str().to_owned())
                        .collect(),
                    Kind::Tag => v.local_tags.keys().map(|n| n.as_str().to_owned()).collect(),
                    Kind::Remote => v
                        .remote_views
                        .get(RemoteName::new(ORIGIN))
                        .map(|r| r.bookmarks.keys().map(|n| n.as_str().to_owned()).collect())
                        .unwrap_or_default(),
                }
            };
            keys(a).into_iter().chain(keys(b)).collect()
        };
        // jj drops a remote ref with no target where a tracked one stands for a deleted
        // bookmark, so a missing one is absent.
        let moved_remote = |r: &Ref| r.record(&before).0 != r.record(&after).0;
        for name in names(&before, &after, Kind::Bookmark) {
            let local = |v: &View| v.local_bookmarks.get(RefName::new(&name)).cloned();
            if local(&before) == local(&after) {
                continue;
            }
            let mut refs: Vec<Ref> = [Kind::Bookmark, Kind::Remote]
                .into_iter()
                .map(|kind| Ref {
                    kind,
                    name: name.clone(),
                })
                .filter(moved_remote)
                .collect();
            // The import's own export (jj-cli's `finish_transaction`) copies a bookmark that
            // `x@origin` moved to `x@git`. Where `x@origin`'s change alone gives the bookmark
            // its new value, as `import_refs` merges it in, `x@git` moved only by that export.
            if let [git, origin] = refs.as_slice() {
                let target = |v: &View| git.local(v);
                let merged = log.merge_targets(
                    id,
                    &target(&before),
                    &origin.record(&before).0,
                    &origin.record(&after).0,
                );
                if origin.tracked(&before)
                    && git.record(&after).0 == target(&after)
                    && merged == target(&after)
                {
                    refs.remove(0);
                }
            }
            changed.push((format!("bookmark {name}"), refs));
        }
        for name in names(&before, &after, Kind::Remote) {
            let r = Ref {
                kind: Kind::Remote,
                name: name.clone(),
            };
            if moved_remote(&r) {
                changed.push((format!("remote bookmark {r}"), vec![r]));
            }
        }
        for name in names(&before, &after, Kind::Tag) {
            let local = |v: &View| v.local_tags.get(RefName::new(&name)).cloned();
            if local(&before) == local(&after) {
                continue;
            }
            let r = Ref {
                kind: Kind::Tag,
                name: name.clone(),
            };
            let refs = if moved_remote(&r) { vec![r] } else { vec![] };
            changed.push((format!("tag {name}"), refs));
        }
        let mut failures = vec![];
        for (what, refs) in changed {
            if refs.is_empty() {
                failures.push(format!(
                    "{} changed {what} without changing jj's record of git's refs",
                    describe(&log.owner, id, &op)
                ));
            }
            for r in refs {
                if let Err(why) = self.justify(m, log, parent, &r) {
                    failures.push(format!(
                        "{} changed {what}: {why}",
                        describe(&log.owner, id, &op)
                    ));
                }
            }
        }
        if failures.is_empty() {
            Ok(())
        } else {
            Err(failures.join("\n"))
        }
    }

    /// Why an import on top of `parent` could change `r` with no git move, if it could.
    fn justify(
        &self,
        m: usize,
        log: &mut Log,
        parent: &OperationId,
        r: &Ref,
    ) -> Result<(), String> {
        let target = log.record(parent, r);
        // Unless git moved the ref, jj's record matches `.git` (`LInv`). After a move, an
        // export's compare-and-swap succeeds only where `.git` already has the bookmark's
        // value, so the record matches what `.git` had before one of git's moves since the
        // last import, and the import takes git's move.
        if let Some(values) = self.imports.moved[m].get(&r.git_ref())
            && values.contains(&target.1)
        {
            fired("import:git_move");
            return Ok(());
        }
        // Back from `parent` to the operation that made the record what it is.
        let mut at = parent.clone();
        loop {
            if self.imports.setup[m].contains(&at) {
                return Err(format!(
                    "git didn't move {}, and jj's record of {r}, {target}, is the same as at setup",
                    r.git_ref()
                ));
            }
            // Trace this record's origin, including its authenticated pre-trim parents.
            let op = log.record_operation(&at);
            if own_import(&log.owner, &op) {
                return Err(format!(
                    "git didn't move {}, and jj's record of {r}, {target}, is the same as at the \
                     import {}",
                    r.git_ref(),
                    describe(&log.owner, &at, &op)
                ));
            }
            if let [before] = op.parents.as_slice() {
                let was = log.record(before, r);
                let now = log.record(&at, r);
                if was.1 == now.1 {
                    at = before.clone();
                    continue;
                }
                return Err(format!(
                    "git didn't move {}, and {} changed jj's record of {r} from {was} to {now}",
                    r.git_ref(),
                    describe(&log.owner, &at, &op)
                ));
            }
            let bases = log.bases(&op.parents);
            let base_records: Vec<Record> = bases.iter().map(|b| log.record(b, r)).collect();
            let Some(base) = base_records.first() else {
                return Err(format!(
                    "{} has no common ancestor",
                    describe(&log.owner, &at, &op)
                ));
            };
            let now = log.record(&at, r);
            if base_records.iter().any(|b| b.1 != base.1) {
                return Err(format!(
                    "the merge {}, whose closest common ancestors record {r} differently, made \
                     jj's record of it {now}; criss-cross merges aren't modeled",
                    describe(&log.owner, &at, &op),
                ));
            }
            let before = log.ancestors(bases.clone());
            let mut touched: Vec<OperationId> = vec![];
            for parent in &op.parents {
                if log.touched(parent, &before, &self.imports.setup[m], r, base)? {
                    touched.push(parent.clone());
                }
            }
            if touched.len() > 1 {
                let [left, right] = op.parents.as_slice() else {
                    return Err(format!(
                        "the merge {} of {} heads, several of which changed jj's record of {r}, \
                         made it {now}; such merges aren't modeled",
                        describe(&log.owner, &at, &op),
                        op.parents.len()
                    ));
                };
                let merged = log.merge(&at, r, left, base, right);
                if merged.1 == now.1 {
                    fired("import:concurrent_records");
                    return Ok(());
                }
                return Err(format!(
                    "git didn't move {}, and the merge {} made jj's record of {r} {now}, where \
                     jj's merge of its parents' makes {merged}",
                    r.git_ref(),
                    describe(&log.owner, &at, &op),
                ));
            }
            let next = touched.first().unwrap_or(&bases[0]).clone();
            if log.record(&next, r).1 != now.1 {
                return Err(format!(
                    "the merge {} made jj's record of {r} {now}, which neither the one parent \
                     that changed it nor their common ancestor have",
                    describe(&log.owner, &at, &op),
                ));
            }
            at = next;
        }
    }

    /// An import of git's HEAD changes jj's record of it, and so moves the working copy, only
    /// where git moved HEAD through the branch it is a symbolic ref to, or where jj's merge of
    /// two op heads that both changed the record left it differing from `.git`.
    fn check_head_import(&self, m: usize, log: &mut Log, id: &OperationId) -> Result<(), String> {
        let native = self
            .commands
            .get(&crate::world::merge_key(log.op(id)))
            .map(|source| source.id.clone());
        let id = native.as_ref().unwrap_or(id);
        let op = log.op(id).clone();
        let [parent] = op.parents.as_slice() else {
            return Err(format!(
                "{} has several parents",
                describe(&log.owner, id, &op)
            ));
        };
        let Some(ws) = op.metadata.workspace_name.clone() else {
            return Err(format!(
                "{} names no workspace",
                describe(&log.owner, id, &op)
            ));
        };
        let (was, taken) = (log.head(parent, ws.as_str()), log.head(id, ws.as_str()));
        if was == taken {
            return Ok(());
        }
        if self.imports.head_moved[m]
            .get(ws.as_str())
            .is_some_and(|values| values.contains(&was))
        {
            fired("import:head_git_move");
            return Ok(());
        }
        self.justify_head(m, log, parent, ws.as_str(), &taken)
            .map_err(|why| {
                format!(
                    "{} moved {}'s working copy, taking HEAD {} for jj's record of it, {}: \
                     git didn't move HEAD from that, and {why}",
                    describe(&log.owner, id, &op),
                    ws.as_str(),
                    show(&taken),
                    show(&was),
                )
            })
    }

    /// Why jj's record of workspace `ws`'s HEAD at `parent` could differ from `.git`'s, which
    /// has `taken`, if it could: back from `parent` to the operation that made the record what
    /// it is.
    fn justify_head(
        &self,
        m: usize,
        log: &mut Log,
        parent: &OperationId,
        ws: &str,
        taken: &RefTarget,
    ) -> Result<(), String> {
        let mut ws = ws.to_owned();
        let mut at = parent.clone();
        loop {
            if self.imports.setup[m].contains(&at) {
                return Err("the record is the same as at setup".to_owned());
            }
            let op = log.record_operation(&at);
            let now = log.head(&at, &ws);
            if let [before] = op.parents.as_slice() {
                let was = log.head(before, &ws);
                if was == now {
                    at = before.clone();
                    continue;
                }
                // A rename takes the record with it.
                if jj_command(&log.owner, &op)
                    && let Some(old) = op
                        .metadata
                        .description
                        .strip_prefix("Renamed workspace '")
                        .and_then(|rest| rest.strip_suffix(&format!("' to '{ws}'")))
                    && log.head(before, old) == now
                {
                    ws = old.to_owned();
                    at = before.clone();
                    continue;
                }
                // jj records HEAD as it writes or imports it, so `.git` had this record then.
                return Err(format!(
                    "{} changed the record from {} to {}{}",
                    describe(&log.owner, &at, &op),
                    show(&was),
                    show(&now),
                    if jj_command(&log.owner, &op) {
                        ", as HEAD was then"
                    } else {
                        ", as only jj does"
                    },
                ));
            }
            let bases = log.bases(&op.parents);
            let base_heads: Vec<RefTarget> = bases.iter().map(|b| log.head(b, &ws)).collect();
            let Some(base) = base_heads.first().cloned() else {
                return Err(format!(
                    "{} has no common ancestor",
                    describe(&log.owner, &at, &op)
                ));
            };
            if base_heads.iter().any(|b| *b != base) {
                return Err(format!(
                    "the merge {}, whose closest common ancestors record it differently, made it \
                     {}; criss-cross merges aren't modeled",
                    describe(&log.owner, &at, &op),
                    show(&now)
                ));
            }
            let before = log.ancestors(bases.clone());
            let mut touched: Vec<OperationId> = vec![];
            for parent in &op.parents {
                if log.head_touched(parent, &before, &self.imports.setup[m], &ws, &base)? {
                    touched.push(parent.clone());
                }
            }
            if touched.len() > 1 {
                let [left, right] = op.parents.as_slice() else {
                    return Err(format!(
                        "the merge {} of {} heads, several of which changed the record, made it \
                         {}; such merges aren't modeled",
                        describe(&log.owner, &at, &op),
                        op.parents.len(),
                        show(&now)
                    ));
                };
                let (left, right) = (log.head(left, &ws), log.head(right, &ws));
                let merged = log.merge_targets(&at, &left, &base, &right);
                // `.git` has what the head that wrote HEAD last left.
                let possible = if merged == now && taken.is_resolved() {
                    let left = log.possible_heads(&op.parents[0], &ws, &self.imports.setup[m])?;
                    let right = log.possible_heads(&op.parents[1], &ws, &self.imports.setup[m])?;
                    let taken = taken.as_normal().cloned();
                    left.contains(&taken) || right.contains(&taken)
                } else {
                    false
                };
                if possible {
                    fired("import:concurrent_heads");
                    return Ok(());
                }
                if merged == now {
                    return Err(format!(
                        "the merge {} of records {} and {} can't have left HEAD {}",
                        describe(&log.owner, &at, &op),
                        show(&left),
                        show(&right),
                        show(taken)
                    ));
                }
                return Err(format!(
                    "the merge {} made the record {}, where jj's merge of its parents' makes {}",
                    describe(&log.owner, &at, &op),
                    show(&now),
                    show(&merged)
                ));
            }
            let next = touched.first().unwrap_or(&bases[0]).clone();
            if log.head(&next, &ws) != now {
                return Err(format!(
                    "the merge {} made the record {}, which neither the one parent that changed \
                     it nor their common ancestor have",
                    describe(&log.owner, &at, &op),
                    show(&now)
                ));
            }
            at = next;
        }
    }
}
