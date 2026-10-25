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
//! `export_conflicted_remote_bookmarks`, whose conflicts are excepted below.
//!
//! The ref behind a change is the record the import compared with `.git`: `x@git` for a
//! bookmark `x` or a tag, `x@origin` for a remote bookmark, and for a bookmark tracking
//! `x@origin`, that too (`diff_refs_to_import` in jj-lib's `git.rs`). The import's own export
//! then copies a bookmark that `x@origin` moved to `x@git`, which needs no reason of its own.
//! A git move explains a change if jj's record matched `.git` before it, as it does unless git
//! moved the ref (`LInv`). An import may change a ref otherwise only where jj itself would, in
//! one repository:
//!
//! - a conflicted remote bookmark, which it resolves to `.git`'s value: jj's export never
//!   writes a conflicted target (`collect_changed_refs_to_export`), so `.git` always differs
//!   from it and every import resets it, as on one machine after concurrent fetches
//!   (`remote_reset_without_export`), where `.git` has the latest. That is one of the
//!   conflict's sides, or where `jj op restore` put the conflict back, the value from before
//!   the restore, which the restoring machine's `.git` kept (`Refs.lean`'s expected value);
//! - a record that an undo, redo, `jj op restore` or `jj op revert` on this machine put back:
//!   they restore the remote refs, `x@git` among them, but keep `git_refs`
//!   (`view_with_desired_portions_restored` in jj-cli's `commands/operation/mod.rs`), so where
//!   the export can't write the restored bookmark, a conflict or the root commit, the import
//!   takes `.git`'s value back, as after undoing a move that resolved a conflicted bookmark;
//! - jj's three-way merge of two op heads that both changed the record since they forked,
//!   even if one changed it back: the result needn't be `.git`'s (`concurrent_records_revert`).
//!   Where only one changed it, the merge keeps that one's (`fork_merge_inv`), and the check
//!   follows it there. Each change either head made must be one jj makes, by an import, a
//!   restore, an export or a fetch, since the theorem assumes both heads reachable (`FReach`).
//!   Merges of more heads at once, or with closest common ancestors that disagree, aren't
//!   modeled, and fail as unexplained.
//!
//! Anything else is a finding: the operation that left the record differing from `.git`, if
//! any, is named in the failure.

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
    /// Each machine's git refs that git moved since jj last imported there, with what `.git`
    /// had before each of those moves.
    moved: Vec<BTreeMap<String, Vec<RefTarget>>>,
}

/// A ref an import compares with `.git`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    /// `x@git`, for bookmark `x`.
    Bookmark,
    /// `x@origin`.
    Remote,
    /// `x@git`, for tag `x`.
    Tag,
}

#[derive(Clone, PartialEq, Eq)]
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

fn own(op: &op_store::Operation) -> bool {
    !op.metadata.attributes.contains_key(CANONICAL_ATTRIBUTE)
}

/// One of this machine's own imports: a realization of another machine's is that machine's.
fn own_import(op: &op_store::Operation) -> bool {
    own(op) && op.metadata.description.starts_with("import git refs")
}

fn describe(id: &OperationId, op: &op_store::Operation) -> String {
    format!(
        "\"{}\" ({}{})",
        op.metadata.description.lines().next().unwrap_or_default(),
        &id.hex()[..12],
        if own(op) { "" } else { ", a realization" }
    )
}

/// What one check reads of a machine's operation log, cached.
struct Log {
    loader: RepoLoader,
    store: Arc<dyn op_store::OpStore>,
    ops: HashMap<OperationId, op_store::Operation>,
    views: HashMap<OperationId, View>,
    repos: HashMap<OperationId, Arc<ReadonlyRepo>>,
}

impl Log {
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

    /// Where `.git`'s value for the conflicted remote bookmark `r` at `id` comes from, as
    /// `Refs.lean`'s expected value has it: back through a parent with the same target, then
    /// through an operation with one parent, as `jj op restore` of the conflict is, to that
    /// parent's target, while it is a conflict too. The result is the value from before the
    /// restore, or else the conflict a merge or a join made, whose sides `.git` may have.
    /// Unlike musubi, this doesn't stop at a join point on the machine that joined, where
    /// history before it has no remote bookmarks in the search.
    fn restored(&mut self, id: &OperationId, r: &Ref) -> RefTarget {
        let mut at = id.clone();
        let mut target = self.record(&at, r).0;
        loop {
            let parents = self.op(&at).parents.clone();
            if let Some(same) = parents.iter().find(|p| self.record(p, r).0 == target) {
                at = same.clone();
                continue;
            }
            let [parent] = parents.as_slice() else {
                return target;
            };
            if self.op(parent).parents.is_empty() {
                return target;
            }
            let was = self.record(parent, r).0;
            if was.is_resolved() {
                return was;
            }
            at = parent.clone();
            target = was;
        }
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
            touched |= self.record(&id, r) != *base;
            if setup.contains(&id) {
                continue;
            }
            self.plausible(&id, r)?;
            pending.extend(self.op(&id).parents.iter().cloned());
        }
        Ok(touched)
    }

    /// An operation that changed the record of `r` did so as jj does: an import, a restore of
    /// what the export can't write, an export or fetch that wrote it, or for a merge, one
    /// parent's record or jj's merge of two. The remote's conflicts are exported by musubi
    /// instead.
    fn plausible(&mut self, id: &OperationId, r: &Ref) -> Result<(), String> {
        let op = self.op(id).clone();
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
                describe(id, &op)
            ));
        };
        // A restore whose export could write the bookmark leaves it as an export does.
        if self.record(parent, r) == now
            || own_import(&op)
            || own(&op) && restore(&op) && !exportable(&local)
            || r.kind == Kind::Remote && !now.0.is_resolved()
        {
            return Ok(());
        }
        if exported {
            return Ok(());
        }
        Err(format!(
            "{} left jj's record of {r} {now}, as no export or fetch does",
            describe(id, &op)
        ))
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

impl World {
    /// Starts the check: the operations so far are the setup's.
    pub fn start_imports(&mut self) {
        for m in 0..self.nodes() {
            self.imports.seen.push(HashSet::new());
            self.imports.moved.push(BTreeMap::new());
            self.check_imports(m);
            self.imports.setup.push(self.imports.seen[m].clone());
        }
        self.imports.started = true;
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
        self.imports.moved[m]
            .entry(git_ref.to_owned())
            .or_default()
            .push(value);
    }

    /// Checks machine `m`'s imports since the last check, oldest first.
    pub fn check_imports(&mut self, m: usize) {
        let loader = self.fx.hive.members[m].adapter.repo().loader().clone();
        let mut log = Log {
            store: loader.op_store().clone(),
            loader,
            ops: HashMap::new(),
            views: HashMap::new(),
            repos: HashMap::new(),
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
        for id in order {
            if !own_import(&log.ops[&id]) {
                continue;
            }
            // Reading the log fails only if musubi lost an operation file it refers to.
            let checked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                self.check_import(m, &mut log, &id)
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
            self.imports.moved[m].clear();
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
        let op = log.op(id).clone();
        let [parent] = op.parents.as_slice() else {
            return Err(format!("{} has several parents", describe(id, &op)));
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
                    describe(id, &op)
                ));
            }
            for r in refs {
                let taken = r.record(&after).0;
                if let Err(why) = self.justify(m, log, parent, &r, &taken) {
                    failures.push(format!("{} changed {what}: {why}", describe(id, &op)));
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
        taken: &RefTarget,
    ) -> Result<(), String> {
        let target = log.record(parent, r);
        // Unless git moved the ref, jj's record matches `.git` (`LInv`). After a move, an
        // export's compare-and-swap succeeds only where `.git` already has the bookmark's
        // value, so the record matches what `.git` had before one of git's moves since the
        // last import, and the import takes git's move.
        if let Some(values) = self.imports.moved[m].get(&r.git_ref())
            && values
                .iter()
                .any(|value| target == Record(value.clone(), value.clone()))
        {
            fired("import:git_move");
            return Ok(());
        }
        // `.git` has one side of a conflicted remote bookmark: the latest fetch, or the side
        // musubi writes (`export_conflicted_remote_bookmarks`). Where `jj op restore` put the
        // conflict back, the restoring machine's `.git` kept the value from before the restore,
        // and musubi writes that on every other machine.
        if r.kind == Kind::Remote && !target.0.is_resolved() {
            let from = log.restored(parent, r);
            let side = |id: &CommitId| from.adds().any(|side| side.as_ref() == Some(id));
            if from == *taken || taken.as_normal().is_some_and(side) {
                fired(if from == target.0 {
                    "import:conflicted_remote"
                } else {
                    "import:restored_conflict"
                });
                return Ok(());
            }
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
            let op = log.op(&at).clone();
            if own_import(&op) {
                return Err(format!(
                    "git didn't move {}, and jj's record of {r}, {target}, is the same as at the \
                     import {}",
                    r.git_ref(),
                    describe(&at, &op)
                ));
            }
            if let [before] = op.parents.as_slice() {
                let was = log.record(before, r);
                let now = log.record(&at, r);
                if was == now {
                    at = before.clone();
                    continue;
                }
                // jj's export after the restore wrote whatever it could, so only a value it
                // can't write leaves the record differing from `.git`.
                if own(&op) && restore(&op) && !exportable(&r.local(log.view(&at))) {
                    fired("import:undo");
                    return Ok(());
                }
                return Err(format!(
                    "git didn't move {}, and {} changed jj's record of {r} from {was} to {now}",
                    r.git_ref(),
                    describe(&at, &op)
                ));
            }
            let bases = log.bases(&op.parents);
            let base_records: Vec<Record> = bases.iter().map(|b| log.record(b, r)).collect();
            let Some(base) = base_records.first() else {
                return Err(format!("{} has no common ancestor", describe(&at, &op)));
            };
            let now = log.record(&at, r);
            if base_records.iter().any(|b| b != base) {
                return Err(format!(
                    "the merge {}, whose closest common ancestors record {r} differently, made \
                     jj's record of it {now}; criss-cross merges aren't modeled",
                    describe(&at, &op),
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
                        describe(&at, &op),
                        op.parents.len()
                    ));
                };
                let merged = log.merge(&at, r, left, base, right);
                if merged == now {
                    fired("import:concurrent_records");
                    return Ok(());
                }
                return Err(format!(
                    "git didn't move {}, and the merge {} made jj's record of {r} {now}, where \
                     jj's merge of its parents' makes {merged}",
                    r.git_ref(),
                    describe(&at, &op),
                ));
            }
            let next = touched.first().unwrap_or(&bases[0]).clone();
            if log.record(&next, r) != now {
                return Err(format!(
                    "the merge {} made jj's record of {r} {now}, which neither the one parent \
                     that changed it nor their common ancestor have",
                    describe(&at, &op),
                ));
            }
            at = next;
        }
    }
}
