//! Bookmarks in a colocated repository, against `formal/Musubi/Refs.lean`
//! (docs/internals/conformance.md, "Per-machine refs"). Hegel moves refs with git, runs
//! `jj` commands, `jj undo` and `jj op restore`, fetches, and has another machine move
//! bookmarks, move a tag or fetch, for musubi to realize here, its export succeeding or
//! failing. Beside the real machine it keeps the model's `Machine` for each ref it follows,
//! and steps each as the model's `LStep`s or `CStep`s that the real action performs, asking
//! the Lean oracle for each of the model's functions (`RefsModel`), with jj's own
//! `merge_ref_targets` as the model's merge (`ref_laws` checks that it obeys the laws the
//! model assumes). After every action each bookmark, its remote bookmark and whether
//! the bookmark tracks it, jj's record of the git ref, and the git ref itself must be the
//! model's, and the model's invariants `LInv` and `CInv` must hold, unless a restore of a
//! slot that isn't `Restorable` left the record behind, as only it may
//! (`restoreLocal_inv`, `restoreRemote_cinv`, `restore_reverts`). The slots carry tracking
//! states, as `TSlot`, and step as its functions, whose targets are `Slot`'s.
//!
//! Op heads are concurrent twice over: a `jj` command at an older operation (`--at-op`), which
//! the next command merges with the head, as jj's `TSlot.merge`; and the other machine moving
//! a bookmark or fetching before it has this machine's latest operations, so that it merges
//! them, and this machine realizes that merge, as `realizeMerge`, which is `TSlot.merge`
//! (`realizeMerge_eq`). Two fetches merge so to a conflicted `y@origin`, whose expected value,
//! one of its sides, musubi writes to `.git` (`exportConflicted`), the same on both machines;
//! a restore of the conflict keeps the expected value from before it (`restoreC`).
//!
//! The refs are a local bookmark `x`, which git moves; a local bookmark `y`, which git
//! doesn't; `y@origin`, which `y` tracks, which git moves and fetches move; and a tag `t`,
//! which git moves, and whose slot is a local bookmark's. The model has one ref per machine;
//! here `y` and `y@origin` share the bookmark `y`, so a step of one is a `set` of the other.

use std::cell::RefCell;
use std::cell::RefMut;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::path::PathBuf;
use std::sync::Arc;

use futures::executor::block_on;
use hegel::HealthCheck;
use hegel::TestCase;
use hegel::generators as gs;
use jj_lib::backend::CommitId;
use jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::RefTarget;
use jj_lib::op_store::RemoteRefState;
use jj_lib::op_store::View;
use jj_lib::ref_name::GitRefName;
use jj_lib::ref_name::RefName;
use jj_lib::ref_name::RemoteName;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use musubi_jj::node::NodeRepo;
use musubi_jj::op_id::CanonicalOp;
use musubi_jj::op_id::LocalOp;
use serde_json::json;

use crate::fixture::Fixture;
use crate::refs_model::RefsModel;
use crate::refs_model::Slot;

/// The machine whose refs are checked, and the other machine, which moves bookmarks.
const HERE: usize = 0;
const THERE: usize = 1;

/// A ref the test follows, as the model's `Slot` has it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Ref {
    /// `L` is `x`, `R` is `x@git`, and `K` is `git_refs["refs/heads/x"]`.
    X,
    /// `L` is `y`, `R` is `y@git`, and `K` is `git_refs["refs/heads/y"]`.
    Y,
    /// `L` is `y`, `R` is `y@origin`, and `K` is `git_refs["refs/remotes/origin/y"]`.
    Origin,
    /// `L` is the tag `t`, `R` is `t@git`, and `K` is `git_refs["refs/tags/t"]`: a local
    /// bookmark's slot, which jj imports and exports as it does `x`'s.
    T,
}

impl Ref {
    const ALL: [Self; 4] = [Self::X, Self::Y, Self::Origin, Self::T];

    /// The bookmark, or for `T` the tag.
    fn bookmark(self) -> &'static str {
        match self {
            Self::X => "x",
            Self::Y | Self::Origin => "y",
            Self::T => "t",
        }
    }

    fn remote(self) -> &'static RemoteName {
        match self {
            Self::X | Self::Y | Self::T => REMOTE_NAME_FOR_LOCAL_GIT_REPO,
            Self::Origin => RemoteName::new("origin"),
        }
    }

    fn git_ref(self) -> &'static str {
        match self {
            Self::X => "refs/heads/x",
            Self::Y => "refs/heads/y",
            Self::Origin => "refs/remotes/origin/y",
            Self::T => "refs/tags/t",
        }
    }

    /// One of `refs`, drawn.
    fn draw(tc: &TestCase, refs: &[Self]) -> Self {
        refs[tc.draw(gs::integers::<usize>().max_value(refs.len() - 1))]
    }
}

/// The model's `Machine`: the view's slot, `.git`'s ref, and the ghost `moved`; for
/// `y@origin`, `CMachine`, with the expected value of a conflicted remote bookmark.
#[derive(Clone, Debug)]
struct Machine {
    v: Slot,
    g: RefTarget,
    moved: bool,
    /// Ghost, shared: `CMachine.E` where `R` is a conflict (`Machine::expected`).
    e: RefTarget,
    /// Ghost: a `jj undo` or `jj op restore` since the last import left a record that
    /// doesn't match `.git`, which `restoreLocal_inv` and `restoreRemote_cinv` allow only
    /// where the restored slot isn't `Restorable`.
    restored: bool,
}

/// The model's `RefAlg` instance, jj's, and `Sides`: the model itself, the oracle's
/// (`RefsModel`), and what the test reads of jj's targets.
struct Alg {
    repo: Arc<ReadonlyRepo>,
    lean: RefCell<RefsModel>,
}

impl Alg {
    fn lean(&self) -> RefMut<'_, RefsModel> {
        self.lean.borrow_mut()
    }

    fn resolved(t: &RefTarget) -> bool {
        t.is_resolved()
    }

    fn writable(&self, t: &RefTarget) -> bool {
        Self::resolved(t) && t.as_normal() != Some(self.repo.store().root_commit_id())
    }

    /// `Sides.side`: the side of a conflict a merge makes that musubi writes to `.git`
    /// (`export_conflicted_remote_bookmarks`), the one committed last, then the greatest
    /// commit id; none if no side is present.
    fn side(&self, t: &RefTarget) -> Option<RefTarget> {
        t.iter()
            .step_by(2)
            .flatten()
            .map(|id| {
                let commit = self.repo.store().get_commit(id).unwrap();
                (commit.committer().timestamp.timestamp.0, id.clone())
            })
            .max()
            .map(|(_, id)| RefTarget::normal(id))
    }
}

impl Machine {
    /// `LStep.gitMove` and `RStep.gitMove`.
    fn git_move(&mut self, g: RefTarget) {
        self.g = g;
        self.moved = true;
    }

    /// `LStep.jjImport` and `RStep.jjImport`, as `TSlot.import`. Returns whether jj set the
    /// bookmark (`set_local_bookmark_target`), which drops the bookmark's other remote refs
    /// with no target if it is gone.
    fn jj_import(&mut self, alg: &Alg) -> bool {
        let set;
        (self.v, set) = alg.lean().import(&self.v, &self.g);
        self.moved = false;
        self.restored = false;
        self.e = self.g.clone();
        set
    }

    /// `LStep.jjExport`, `TSlot.exportLocal`, where the update of `.git` can succeed. Where
    /// `.git` is locked (not `git_writable`), an update that would write fails, which is no
    /// step, as the model has a failed update; one to the value `.git` already has, or none,
    /// writes nothing, so succeeds.
    fn export_local(&mut self, alg: &Alg, git_writable: bool) {
        if !git_writable && self.v.l != self.v.k && self.g != self.v.l {
            return;
        }
        (self.v, self.g) = alg.lean().export_local(&self.v, &self.g);
    }

    /// `RStep.jjExport`, `exportRemote`.
    fn export_remote(&mut self, alg: &Alg) {
        (self.v, self.g) = alg.lean().export_remote(&self.v, &self.g);
    }

    /// The expected value: the remote bookmark if it is resolved, otherwise `e`.
    fn expected(&self) -> RefTarget {
        if Alg::resolved(&self.v.r) {
            self.v.r.clone()
        } else {
            self.e.clone()
        }
    }

    /// musubi's export of a conflicted remote bookmark (`exportConflicted`,
    /// `export_conflicted_remote_bookmarks`): its expected value, written to `.git` if that
    /// holds it, or a value the hive knows of, a term of the conflict or the record, and it
    /// can be written; and to the record.
    fn export_conflicted(&mut self, alg: &Alg) {
        (self.v, self.g) = alg.lean().export_conflicted(&self.v, &self.g, &self.e);
    }

    /// musubi's export of a conflicted remote bookmark of a realization beside an op head
    /// whose record is `k` (`exportConflictedBeside`): none where `.git` holds `k`, which that
    /// head put there, and the realization records another value.
    fn export_conflicted_beside(&mut self, alg: &Alg, k: &RefTarget) {
        (self.v, self.g) = alg
            .lean()
            .export_conflicted_beside(&self.v, &self.g, &self.e, k);
    }

    /// The model's invariant for `r`: `LInv`, or for `y@origin` `CInv`, which is `RInv`
    /// but for a conflicted remote bookmark, with `.git` at the expected value.
    fn strict_inv(&self, alg: &Alg, r: Ref) -> bool {
        if r == Ref::Origin {
            alg.lean()
                .cinv(&self.v, &self.g, self.moved, &self.expected())
        } else {
            alg.lean().linv(&self.v, &self.g, self.moved)
        }
    }

    /// `strict_inv`, but where a restore left the record behind (`restored`).
    fn inv(&self, alg: &Alg, r: Ref) -> bool {
        self.restored || self.strict_inv(alg, r)
    }

    /// `Restorable`: whether restoring `o` here keeps the invariant, as the export puts
    /// `.git` back or there is nothing to put back. For a remote bookmark (`remote`) that is
    /// about its target, which may be a conflict too (`CStep.restore`), otherwise about the
    /// bookmark's.
    fn restorable(&self, alg: &Alg, o: &Slot, remote: bool) -> bool {
        alg.lean().restorable(o, &self.v, remote)
    }
}

/// The shared fields of the refs: `x`, `t`, and `y@origin`'s slot with no `K`.
type Shared = (RefTarget, RefTarget, Slot);

/// A `jj` command on this machine after the other machine's operation and before this machine
/// syncs, so that musubi realizes that operation beside it (`LStep.beside`, `CStep.beside`).
#[derive(Clone, Debug)]
enum Beside {
    /// The command moves `x`, `y` or `t` (`Refs::jj_sets`).
    Sets(Ref, RefTarget),
    /// `y` moves in `origin`, and `jj git fetch` fetches it (`Refs::jj_fetches_from`).
    Fetches(RefTarget),
}

/// The shared fields of the refs whose slots are `slot`'s.
fn shared(slot: impl Fn(Ref) -> Slot) -> Shared {
    (
        slot(Ref::X).l,
        slot(Ref::T).l,
        Slot {
            k: RefTarget::absent(),
            ..slot(Ref::Origin)
        },
    )
}

/// The model's machines, one for each ref, keeping the bookmark `y` the same in `Y`'s and
/// `Origin`'s.
#[derive(Clone, Debug)]
struct Model([Machine; 4]);

impl Model {
    fn get(&self, r: Ref) -> &Machine {
        &self.0[r as usize]
    }

    fn at(&mut self, r: Ref) -> &mut Machine {
        &mut self.0[r as usize]
    }

    /// `set` on the bookmark's refs, as jj's `set_local_bookmark_target`.
    fn set(&mut self, alg: &Alg, bookmark: Ref, l: RefTarget) {
        for r in Ref::ALL {
            if r.bookmark() == bookmark.bookmark() {
                let v = alg.lean().set(&self.get(r).v, &l);
                self.at(r).v = v;
            }
        }
    }

    /// `jj bookmark set` or `delete` moving `bookmark` to `l`: a `set`, and if it creates
    /// `y`, `TSlot.track` of `y@origin`, which `remotes.origin.auto-track-bookmarks` covers,
    /// and a `set` of `y@git` with the bookmark that merges into.
    fn bookmark_set(&mut self, alg: &Alg, bookmark: Ref, l: RefTarget) {
        let created = self.get(bookmark).v.l.is_absent() && l.is_present();
        self.set(alg, bookmark, l);
        if created && bookmark.bookmark() == Ref::Origin.bookmark() {
            let origin = alg.lean().track(&self.get(Ref::Origin).v);
            let y = alg.lean().set(&self.get(Ref::Y).v, &origin.l);
            self.at(Ref::Origin).v = origin;
            self.at(Ref::Y).v = y;
        }
    }

    /// `TSlot.realizeLocal` of `x`, `y` and `t`, and `realizeRemote` of `y@origin`, from
    /// the canonical view's slots: the shared fields, without dropping anything.
    fn realize(&mut self, canonical: &Shared) {
        let (x, t, origin) = canonical;
        self.at(Ref::X).v.l = x.clone();
        self.at(Ref::T).v.l = t.clone();
        self.at(Ref::Y).v.l = origin.l.clone();
        let v = &mut self.at(Ref::Origin).v;
        v.l = origin.l.clone();
        v.r = origin.r.clone();
        v.tr = origin.tr;
    }

    fn shared(&self) -> Shared {
        shared(|r| self.get(r).v.clone())
    }

    /// `jj undo` or `jj op restore` to an operation whose view is `view`: each ref's slot as
    /// there, but `K`, as `view_with_desired_portions_restored` in jj-cli restores it, then
    /// jj's export. Where that leaves a record that doesn't match `.git`, the ghost
    /// `restored`, which only an unrestorable slot may set.
    fn restore(&mut self, alg: &Alg, view: &View) {
        let mut restorable = [true; 4];
        for r in Ref::ALL {
            let o = slot(view, r);
            let m = self.at(r);
            restorable[r as usize] = m.restorable(alg, &o, r == Ref::Origin);
            // `restoreC`: the restore's parent is the head, so its expected value is the
            // head's, where the restored remote bookmark is a conflict.
            m.e = m.expected();
            m.v = Slot {
                k: m.v.k.clone(),
                ..o
            };
        }
        self.export(alg, false, false);
        for r in Ref::ALL {
            let m = self.at(r);
            if !m.inv(alg, r) {
                assert!(
                    !restorable[r as usize],
                    "{r:?}: a restorable slot left the record behind: {m:?}"
                );
                m.restored = true;
            }
        }
    }

    /// jj's merge of op heads, `first` merged with `second` against `base`.
    fn merge(alg: &Alg, base: &Self, first: &Self, second: &Self) -> [Slot; 4] {
        Ref::ALL.map(|r| {
            alg.lean()
                .merge_slots(&base.get(r).v, &first.get(r).v, &second.get(r).v)
        })
    }

    fn slots(&self) -> Vec<Slot> {
        self.0.iter().map(|m| m.v.clone()).collect()
    }

    /// jj's import of `refs`, in its order, each a `jjImport` and a `set` of the others with
    /// the bookmark. Returns whether it changed the view.
    fn import(&mut self, alg: &Alg, refs: &[Ref]) -> bool {
        let before = self.slots();
        for &r in refs {
            // Since jj's 095c1ca, unchanged physical refs do not update remote bookmarks.
            if self.get(r).g != self.get(r).v.k {
                self.import_ref(alg, r);
            }
        }
        self.slots() != before
    }

    /// A fetch imports its explicit result even if the physical ref did not change.
    fn import_ref(&mut self, alg: &Alg, r: Ref) {
        if self.at(r).jj_import(alg) {
            let l = self.at(r).v.l.clone();
            self.set(alg, r, l);
        }
    }

    /// jj's export of every ref, `x`'s update failing if `x_locked`, then, if `musubi`
    /// exports, its export of a conflicted `y@origin`.
    fn export(&mut self, alg: &Alg, x_locked: bool, musubi: bool) {
        self.at(Ref::X).export_local(alg, !x_locked);
        self.at(Ref::Y).export_local(alg, true);
        self.at(Ref::Origin).export_remote(alg);
        self.at(Ref::T).export_local(alg, true);
        if musubi {
            self.at(Ref::Origin).export_conflicted(alg);
        }
    }

    /// jj's export of a realization beside this machine's op head `head`, `x`'s update failing
    /// if `x_locked`, then musubi's of a conflicted `y@origin`, which leaves `.git` alone where
    /// it holds `head`'s record and the realization's differs (`realizeBesideLocal`,
    /// `realizeBesideRemote`).
    fn export_beside(&mut self, alg: &Alg, x_locked: bool, head: &Self) {
        self.export(alg, x_locked, false);
        let k = &head.get(Ref::Origin).v.k;
        self.at(Ref::Origin).export_conflicted_beside(alg, k);
    }

    /// Whether every local bookmark's record agrees with itself, as `LStep.beside` needs of the
    /// operation a realization beside the op head descends from (`LStep.agrees`).
    fn records_agree(&self) -> bool {
        [Ref::X, Ref::Y, Ref::T].iter().all(|&r| {
            let v = &self.get(r).v;
            v.r == v.k
        })
    }

    /// An integrated `jj` command imports, then exports even when importing changed
    /// nothing. Its own transaction, `change`, exports only if that changed the view.
    fn jj(&mut self, alg: &Alg, change: impl FnOnce(&mut Self)) {
        self.import(alg, &Ref::ALL);
        self.export(alg, false, false);
        let before = self.slots();
        change(self);
        if self.slots() != before {
            self.export(alg, false, false);
        }
    }
}

/// The repository the machines start from: `base`, `one` and `two` in a line, `three`
/// beside them, each kept visible by a bookmark of its own, and `x`, the tag `t`, `y` and
/// `y@origin`, which `y` tracks, at `one`. Both machines track `y@origin` automatically, as
/// the model assumes: without it, jj forgets that `y` tracks `y@origin` once both are gone,
/// and merges nothing into `y` when `y@origin` comes back (docs/internals/conformance.md,
/// "Per-machine refs").
pub(crate) fn hive() -> Fixture {
    Fixture::recorded(&["alpha", "beta"], "refs", |hive| {
        let origin = hive.env.root().join("origin.git");
        let repo = hive.repo(HERE);
        repo.jj(&["new", "-m", "base"]);
        repo.jj(&["new", "-m", "one"]);
        repo.jj(&["new", "-m", "two"]);
        repo.jj(&["bookmark", "create", "keep-two", "-r", "@"]);
        repo.jj(&["bookmark", "create", "x", "-r", "@-"]);
        repo.jj(&["tag", "set", "t", "-r", "@-"]);
        repo.jj(&["new", "@--", "-m", "three"]);
        repo.jj(&["bookmark", "create", "keep-three", "-r", "@"]);
        repo.jj(&["new"]);
        repo.git(&["init", "--quiet", "--bare", origin.to_str().unwrap()]);
        repo.git(&[
            "push",
            "--quiet",
            origin.to_str().unwrap(),
            "keep-two",
            "keep-three",
            "x:refs/heads/y",
        ]);
        for index in [HERE, THERE] {
            hive.repo(index).jj(&[
                "config",
                "set",
                "--repo",
                "remotes.origin.auto-track-bookmarks",
                "y",
            ]);
        }
        repo.jj(&["git", "remote", "add", "origin", origin.to_str().unwrap()]);
        repo.jj(&["git", "fetch"]);
        hive.sync();
    })
}

struct Refs {
    fixture: Fixture,
    alg: Alg,
    model: Model,
    /// The op head after the latest action, and the model then.
    latest: (OperationId, Model),
    /// The op head and the model before the latest action, for a `jj` command at that
    /// operation.
    older: (OperationId, Model),
    /// This machine's op head and model when both machines last synced, where the other
    /// machine's operations start.
    synced: (OperationId, Model),
    /// The root, then `base`, `one`, `two` and `three`.
    commits: Vec<CommitId>,
    /// `y` in `origin`.
    upstream: RefTarget,
}

impl Refs {
    fn new() -> Self {
        let mut fixture = hive();
        // Its copy of `origin`, where the recording's was: git keeps the path as given.
        let origin = fixture.env.root().join("origin.git");
        for index in [HERE, THERE] {
            fixture
                .repo(index)
                .git(&["remote", "set-url", "origin", origin.to_str().unwrap()]);
        }
        fixture.sync();
        let repo = fixture.load(HERE);
        let commit = |name: &str| {
            repo.view()
                .get_local_bookmark(RefName::new(name))
                .as_normal()
                .unwrap()
                .clone()
        };
        let parent = |id: &CommitId| repo.store().get_commit(id).unwrap().parent_ids()[0].clone();
        let two = commit("keep-two");
        let one = parent(&two);
        let base = parent(&one);
        let commits = vec![
            repo.store().root_commit_id().clone(),
            base,
            one.clone(),
            two,
            commit("keep-three"),
        ];
        let model = Model(Ref::ALL.map(|r| {
            let (v, g) = read(&repo, r);
            Machine {
                e: g.clone(),
                v,
                g,
                moved: false,
                restored: false,
            }
        }));
        let head = (repo.op_id().clone(), model.clone());
        let mut refs = Self {
            fixture,
            alg: Alg {
                lean: RefCell::new(RefsModel::new(repo.clone())),
                repo,
            },
            model,
            latest: head.clone(),
            older: head.clone(),
            synced: head,
            commits,
            upstream: RefTarget::normal(one),
        };
        refs.check();
        refs
    }

    /// A target other than `not`, the value it would replace, so that every action changes
    /// something: absent, or one of the commits, the root among them if `root`.
    fn target(&self, tc: &TestCase, root: bool, not: &RefTarget) -> RefTarget {
        let first = if root { 0 } else { 1 };
        let choices: Vec<RefTarget> = self.commits[first..]
            .iter()
            .map(|id| RefTarget::normal(id.clone()))
            .chain([RefTarget::absent()])
            .filter(|target| target != not)
            .collect();
        let n = tc.draw(gs::integers::<usize>().max_value(choices.len() - 1));
        choices[n].clone()
    }

    /// The real state is the model's, and the model's invariants hold.
    fn check(&mut self) {
        let repo = self.fixture.load(HERE);
        let heads = block_on(repo.loader().op_heads_store().get_op_heads()).unwrap();
        assert_eq!(heads.len(), 1, "op heads: {heads:?}");
        let latest = (repo.op_id().clone(), self.model.clone());
        self.older = std::mem::replace(&mut self.latest, latest);
        for r in Ref::ALL {
            let model = self.model.get(r);
            let (v, g) = read(&repo, r);
            assert_eq!(v, model.v, "{r:?}: bookmark, remote bookmark and git_refs");
            assert_eq!(g, model.g, "{r:?}: .git's {}", r.git_ref());
            assert!(
                model.inv(&self.alg, r),
                "{r:?}: the model's invariant fails: {model:?}"
            );
            // Once the record is back, as a realization's export can put it, the invariant
            // holds again in full.
            if model.strict_inv(&self.alg, r) {
                self.model.at(r).restored = false;
            }
        }
    }

    /// This machine's op head.
    fn head(&self) -> OperationId {
        self.fixture.load(HERE).op_id().clone()
    }

    /// The parents of `op`.
    fn parents(&self, op: &OperationId) -> Vec<OperationId> {
        let repo = self.fixture.load(HERE);
        block_on(repo.loader().load_operation(op))
            .unwrap()
            .parent_ids()
            .to_vec()
    }

    /// The parents of this machine's latest merge operation, the head or an ancestor.
    fn merge_parents(&self) -> Vec<OperationId> {
        let repo = self.fixture.load(HERE);
        let mut op = repo.operation().clone();
        while op.parent_ids().len() == 1 {
            op = block_on(op.parents()).unwrap().remove(0);
        }
        op.parent_ids().to_vec()
    }

    /// Has machine `index` move `bookmark` (or the tag) to `l` with a `jj` command, or if `l`
    /// is where it is, run a `jj` command that changes nothing; at the operation `at`, if
    /// given.
    fn jj_set(
        &self,
        index: usize,
        bookmark: Ref,
        l: &RefTarget,
        current: &RefTarget,
        at: Option<&OperationId>,
    ) {
        let repo = self.fixture.repo(index);
        let at = at.map(|op| ["--at-op".to_owned(), op.hex()]);
        let jj = |args: &[&str]| {
            let mut all: Vec<&str> = at.iter().flatten().map(String::as_str).collect();
            all.extend(args);
            repo.jj(&all)
        };
        if l == current {
            jj(&["status"]);
        } else if let Some(id) = l.as_normal() {
            let rev = if id == &self.commits[0] {
                "root()".to_owned()
            } else {
                id.hex()
            };
            if bookmark == Ref::T {
                jj(&["tag", "set", "t", "-r", &rev, "--allow-move"]);
            } else {
                jj(&[
                    "bookmark",
                    "set",
                    bookmark.bookmark(),
                    "-r",
                    &rev,
                    "--allow-backwards",
                ]);
            }
        } else if bookmark == Ref::T {
            jj(&["tag", "delete", "t"]);
        } else {
            jj(&["bookmark", "delete", bookmark.bookmark()]);
        }
    }

    /// `y` in `origin` moves to `upstream`.
    fn push_upstream(&mut self, upstream: RefTarget) {
        let origin = self.origin();
        let origin = origin.to_str().unwrap();
        let repo = self.fixture.repo(HERE);
        match upstream.as_normal() {
            Some(id) => repo.git(&["--git-dir", origin, "update-ref", "refs/heads/y", &id.hex()]),
            None => repo.git(&["--git-dir", origin, "update-ref", "-d", "refs/heads/y"]),
        };
        self.upstream = upstream;
    }

    fn origin(&self) -> PathBuf {
        self.fixture.env.root().join("origin.git")
    }
}

/// The expected value of `y@origin` in `model`, if it is conflicted.
fn conflicted_expected(model: &Model) -> Option<RefTarget> {
    let origin = model.get(Ref::Origin);
    (!Alg::resolved(&origin.v.r)).then(|| origin.e.clone())
}

/// The expected value of `y@origin` at `r`, a merge of `heads`, in that order if
/// `in_order`: the remote bookmark if it is resolved, as where a fetch and a conflict on it
/// merge to neither, or else the first parent's with the same conflict, or the side, where
/// the merge made it.
fn merged_expected(
    side: impl FnOnce(&RefTarget) -> Option<RefTarget>,
    r: &RefTarget,
    mut heads: [&Machine; 2],
    in_order: bool,
) -> RefTarget {
    if Alg::resolved(r) {
        return r.clone();
    }
    if !in_order {
        heads.reverse();
    }
    match heads.iter().find(|m| m.v.r == *r) {
        Some(parent) => parent.expected(),
        // Two fetches' conflict has a side, a commit: one of them fetched it.
        None => side(r).expect("a fetched side"),
    }
}

/// `r` as this machine's view at `repo` has it, and its `.git`.
fn read(repo: &ReadonlyRepo, r: Ref) -> (Slot, RefTarget) {
    let slot = slot(repo.view().store_view(), r);
    let git = jj_lib::git::get_git_repo(repo.store()).unwrap();
    let g = match git.try_find_reference(r.git_ref()).unwrap() {
        Some(reference) => {
            let id = reference.into_fully_peeled_id().unwrap();
            RefTarget::normal(CommitId::from_bytes(id.detach().as_bytes()))
        }
        None => RefTarget::absent(),
    };
    (slot, g)
}

fn slot(view: &View, r: Ref) -> Slot {
    let name = RefName::new(r.bookmark());
    let (local, remote) = if r == Ref::T {
        (
            view.local_tags.get(name),
            view.remote_views
                .get(r.remote())
                .and_then(|remote| remote.tags.get(name)),
        )
    } else {
        (
            view.local_bookmarks.get(name),
            view.remote_views
                .get(r.remote())
                .and_then(|remote| remote.bookmarks.get(name)),
        )
    };
    let local = local.cloned();
    Slot {
        l: local.unwrap_or_else(RefTarget::absent),
        r: remote.map_or_else(RefTarget::absent, |remote| remote.target.clone()),
        tr: remote.is_some_and(|remote| remote.state == RemoteRefState::Tracked),
        k: view
            .git_refs
            .get(GitRefName::new(r.git_ref()))
            .cloned()
            .unwrap_or_else(RefTarget::absent),
    }
}

impl Refs {
    /// `git update-ref` moves or deletes `r`'s git ref to `g`: `gitMove`.
    fn git_moves_to(&mut self, r: Ref, g: RefTarget) {
        let repo = self.fixture.repo(HERE);
        match g.as_normal() {
            Some(id) => repo.git(&["update-ref", r.git_ref(), &id.hex()]),
            None => repo.git(&["update-ref", "-d", r.git_ref()]),
        };
        self.model.at(r).git_move(g);
        self.check();
    }

    /// A `jj` command that moves `bookmark` to `l` (`Model::jj`), or changes nothing if
    /// that is where the command finds it.
    fn jj_sets(&mut self, bookmark: Ref, l: RefTarget) {
        let current = self.imported(bookmark);
        self.jj_set(HERE, bookmark, &l, &current, None);
        self.model.jj(&self.alg, |model| {
            model.bookmark_set(&self.alg, bookmark, l);
        });
        self.check();
    }

    /// `bookmark` as a `jj` command finds it, once it has imported.
    fn imported(&self, bookmark: Ref) -> RefTarget {
        let mut imported = self.model.clone();
        imported.import(&self.alg, &Ref::ALL);
        imported.get(bookmark).v.l.clone()
    }

    /// A `jj` command at the operation before the latest action (`--at-op`) moves `bookmark`
    /// to `l`, which must be somewhere else there. It imports nothing, but exports, against
    /// that operation's record. The next `jj` command merges its operation with the head,
    /// against the older operation, as `TSlot.merge`, then imports and exports. If the latest
    /// action made no operation, the command's operation is simply the next.
    fn jj_sets_at_older_op(&mut self, bookmark: Ref, l: RefTarget) {
        let (old, base) = self.older.clone();
        let head = self.head();
        let current = base.get(bookmark).v.l.clone();
        assert_ne!(l, current);
        self.jj_set(HERE, bookmark, &l, &current, Some(&old));
        let mut theirs = base.clone();
        for r in Ref::ALL {
            theirs.at(r).g = self.model.get(r).g.clone();
        }
        theirs.bookmark_set(&self.alg, bookmark, l);
        theirs.export(&self.alg, false, false);
        for r in Ref::ALL {
            let g = theirs.get(r).g.clone();
            self.model.at(r).g = g;
        }
        self.fixture.repo(HERE).jj(&["status"]);
        let merged = if old == head {
            theirs.slots().try_into().unwrap()
        } else {
            // jj merges op heads in the order of their end times, and the merge's parents
            // are in that order.
            let parents = self.merge_parents();
            assert!(
                parents.contains(&head),
                "merged {parents:?}, not the head {head:?}"
            );
            if parents[0] == head {
                Model::merge(&self.alg, &base, &self.model, &theirs)
            } else {
                Model::merge(&self.alg, &base, &theirs, &self.model)
            }
        };
        for (r, v) in Ref::ALL.into_iter().zip(merged) {
            self.model.at(r).v = v;
        }
        self.model.jj(&self.alg, |_| {});
        self.check();
    }

    /// `y` moves in `origin` to `upstream`, and `jj git fetch` fetches it: a `jj` command
    /// whose change is `RStep.fetch`.
    fn jj_fetches_from(&mut self, upstream: RefTarget) {
        self.push_upstream(upstream.clone());
        self.fixture.repo(HERE).jj(&["git", "fetch"]);
        self.model.jj(&self.alg, |model| {
            model.at(Ref::Origin).g = upstream;
            model.import_ref(&self.alg, Ref::Origin);
        });
        self.check();
    }

    /// The other machine moves `x` or `t` (`moved`), or if none, fetches `y` after it moved
    /// in `origin` to `upstream`, and both sync, the update of `x` failing if `locked`, while
    /// git's lock on `refs/heads/x` is held: an `advance` of each ref, and the export, with
    /// musubi's of a conflicted `y@origin`. If `concurrent`, the other machine acts before it
    /// has this machine's latest operations, so that when it syncs, it merges them with its
    /// own, and this machine realizes the merge: `realizeMerge`, which is jj's merge
    /// (`realizeMerge_eq`), against the operation both last synced at. Two fetches merge so
    /// to a conflicted `y@origin` if both moved it, and the side musubi writes for it must
    /// be the same on both machines. If `beside`, this machine runs that `jj` command before
    /// it syncs, and musubi realizes the other's operation beside it, merges the two, and
    /// exports the merge: `LStep.beside` and `CStep.beside`.
    fn musubi_realizes_with(
        &mut self,
        moved: Option<(Ref, RefTarget)>,
        upstream: RefTarget,
        locked: bool,
        concurrent: bool,
        beside: Option<Beside>,
    ) {
        self.fixture.hive.sync(HERE).unwrap();
        if !concurrent {
            // Both up to date, so that what this machine realizes follows its op head.
            self.fixture.hive.sync(THERE).unwrap();
            self.synced = (self.head(), self.model.clone());
        }
        let (synced_op, base) = self.synced.clone();
        let ours = self.head();
        match &moved {
            None => {
                self.push_upstream(upstream);
                self.fixture.repo(THERE).jj(&["git", "fetch"]);
            }
            Some((r, c)) => {
                // The other machine's ref is this one's when they last synced.
                let current = base.get(*r).v.l.clone();
                self.jj_set(THERE, *r, c, &current, None);
            }
        }
        // What the other machine's operations leave in the hive, the shared fields of its
        // view, are what this machine's model says the other's command made of them: the
        // other machine's own refs changed nothing.
        let there = self.fixture.load(THERE);
        let view = there.view().store_view();
        let canonical = shared(|r| slot(view, r));
        let mut expected = base.clone();
        // The other machine's command imports first, and resolves a conflicted `y@origin` to
        // the expected value its `.git` holds if that physical ref changed, as this
        // machine's import would
        // (`conflicted_import_agrees`, `restore_import_agrees`).
        if let Some(e) = conflicted_expected(&expected) {
            expected.at(Ref::Origin).g = e;
            expected.import(&self.alg, &[Ref::Origin]);
        }
        match moved {
            None => {
                let (theirs, _) = self
                    .alg
                    .lean()
                    .import(&expected.get(Ref::Origin).v, &self.upstream);
                expected.set(&self.alg, Ref::Y, theirs.l.clone());
                expected.at(Ref::Origin).v = Slot {
                    k: expected.get(Ref::Origin).v.k.clone(),
                    ..theirs
                };
            }
            Some((r, c)) => expected.set(&self.alg, r, c),
        }
        assert_eq!(
            canonical,
            expected.shared(),
            "the other machine's x, t, y and y@origin"
        );
        self.fixture.hive.sync(THERE).unwrap();
        // This machine as of `ours`, which the realization descends from.
        let at_ours = self.model.clone();
        match beside {
            Some(Beside::Sets(r, l)) => self.jj_sets(r, l),
            Some(Beside::Fetches(upstream)) => self.jj_fetches_from(upstream),
            None => {}
        }
        // The operation the command made, if any, which the realization is beside.
        let mine = self.head();
        let beside = mine != ours;
        let lock = self
            .fixture
            .repo(HERE)
            .path()
            .join(".git/refs/heads/x.lock");
        if locked {
            std::fs::create_dir_all(lock.parent().unwrap()).unwrap();
            std::fs::write(&lock, "").unwrap();
        }
        self.fixture.hive.sync(HERE).unwrap();
        if locked {
            std::fs::remove_file(&lock).unwrap();
        }
        // `LStep.advance` for `x`, `y` and `t`, and `CStep.advance` for `y@origin`, then the
        // export, if there was anything to realize: a fetch that brings nothing new makes no
        // operation. Beside the command, `LStep.beside` and `CStep.beside`.
        if expected.shared() != base.shared() {
            // The realization, from this machine's refs as of `ours`, against `.git` as it is.
            let mut realized = at_ours.clone();
            for r in Ref::ALL {
                realized.at(r).g = self.model.get(r).g.clone();
            }
            if ours == synced_op {
                // The other machine's operations follow on from this machine's head, so a
                // conflict they keep has the head's expected value.
                let e = at_ours.get(Ref::Origin).expected();
                realized.realize(&canonical);
                realized.at(Ref::Origin).e = e;
            } else {
                // Theirs is realized here from the base, its record the base's, and merged
                // with ours as the other machine merged them.
                let mut theirs = base.clone();
                theirs.realize(&canonical);
                let parents = if beside {
                    let merge = self.merge_parents();
                    let realization = merge.iter().find(|&op| *op != mine).unwrap();
                    self.parents(realization)
                } else {
                    self.merge_parents()
                };
                assert!(
                    parents.contains(&ours),
                    "merged {parents:?}, not ours {ours:?}"
                );
                let merged = if parents[0] == ours {
                    Model::merge(&self.alg, &base, &at_ours, &theirs)
                } else {
                    Model::merge(&self.alg, &base, &theirs, &at_ours)
                };
                let e = merged_expected(
                    |r| self.alg.side(r),
                    &merged[Ref::Origin as usize].r,
                    [&at_ours, &theirs].map(|m| m.get(Ref::Origin)),
                    parents[0] == ours,
                );
                for (r, v) in Ref::ALL.into_iter().zip(merged) {
                    realized.at(r).v = v;
                }
                realized.at(Ref::Origin).e = e;
            }
            if beside {
                // Exported against `.git` as the command left it, then merged with the
                // command's operation, against `ours`, as musubi merged them.
                realized.export_beside(&self.alg, locked, &self.model);
                let parents = self.merge_parents();
                assert!(
                    parents.contains(&mine),
                    "merged {parents:?}, not the command's {mine:?}"
                );
                let merged = if parents[0] == mine {
                    Model::merge(&self.alg, &at_ours, &self.model, &realized)
                } else {
                    Model::merge(&self.alg, &at_ours, &realized, &self.model)
                };
                let e = merged_expected(
                    |r| self.alg.side(r),
                    &merged[Ref::Origin as usize].r,
                    [&self.model, &realized].map(|m| m.get(Ref::Origin)),
                    parents[0] == mine,
                );
                for (r, v) in Ref::ALL.into_iter().zip(merged) {
                    realized.at(r).v = v;
                }
                realized.at(Ref::Origin).e = e;
            }
            // The ghosts are the command's, if any: musubi neither imports nor moves refs.
            for r in Ref::ALL {
                let Machine { v, g, .. } = realized.get(r).clone();
                let m = self.model.at(r);
                (m.v, m.g) = (v, g);
            }
            self.model.at(Ref::Origin).e = realized.get(Ref::Origin).e.clone();
            // `CStep.advance`'s and `CStep.beside`'s precondition, which offering no root
            // commit keeps.
            let origin = self.model.get(Ref::Origin);
            let e = origin.expected();
            assert!(e == origin.g || self.alg.writable(&e));
            self.model.export(&self.alg, locked, true);
        }
        if beside {
            // The other machine catches up, so that both last synced at this machine's head.
            self.fixture.hive.sync(THERE).unwrap();
        }
        self.check();
        // Every machine has the same expected value of a conflicted `y@origin` in its `.git`.
        if let Some(e) = conflicted_expected(&self.model) {
            let (there, g) = read(&self.fixture.load(THERE), Ref::Origin);
            assert_eq!(
                there.r,
                self.model.get(Ref::Origin).v.r,
                "the other machine's y@origin"
            );
            assert_eq!(g, e, "the other machine's refs/remotes/origin/y");
        }
        self.synced = (self.head(), self.model.clone());
    }

    /// `jj undo`, or if `target`, `jj op restore` to it: as a `jj` command, its import, then
    /// `Model::restore` of the operation it restores, read from its description, if it made
    /// one. jj refuses to undo a merge operation, or one made in another workspace.
    fn jj_restores_to(&mut self, target: Option<OperationId>) {
        let before = self.head();
        let repo = self.fixture.repo(HERE);
        let output = match &target {
            None => repo.jj_output(&["undo"]),
            Some(op) => repo.jj_output(&["op", "restore", &op.hex()]),
        };
        if self.model.import(&self.alg, &Ref::ALL) {
            self.model.export(&self.alg, false, false);
        }
        let repo = self.fixture.load(HERE);
        let description = &repo.operation().metadata().description;
        let restored = (repo.op_id() != &before)
            .then(|| {
                description
                    .strip_prefix("undo: restore to operation ")
                    .or_else(|| description.strip_prefix("restore to operation "))
            })
            .flatten();
        match restored {
            Some(hex) => {
                let op = OperationId::try_from_hex(hex).unwrap();
                if let Some(target) = &target {
                    assert_eq!(&op, target);
                }
                let op = block_on(repo.loader().load_operation(&op)).unwrap();
                let view = block_on(op.view()).unwrap();
                self.model.restore(&self.alg, view.store_view());
            }
            // jj makes no operation if the restored view is the current one, as when the
            // operation undone changed only `git_refs`, which a restore keeps.
            None => assert!(
                !output.status.success()
                    || String::from_utf8_lossy(&output.stderr).contains("Nothing changed."),
                "restored nothing"
            ),
        }
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                target.is_none()
                    && (stderr.contains("Cannot undo a merge operation")
                        || stderr.contains("Refusing to undo operation")),
                "{stderr}"
            );
        }
        self.check();
    }
}

#[hegel::state_machine]
impl Refs {
    /// `git update-ref` moves or deletes `refs/heads/x`, `refs/tags/t` or
    /// `refs/remotes/origin/y`: `LStep.gitMove` or `RStep.gitMove`.
    #[rule(weight = 2)]
    fn git_moves(&mut self, tc: TestCase) {
        let r = Ref::draw(&tc, &[Ref::X, Ref::T, Ref::Origin]);
        let g = self.target(&tc, false, &self.model.get(r).g);
        self.git_moves_to(r, g);
    }

    /// A `jj` command that moves `x`, `y` or `t`, or changes nothing (`Model::jj`).
    #[rule]
    fn jj_runs(&mut self, tc: TestCase) {
        let bookmark = Ref::draw(&tc, &[Ref::X, Ref::T, Ref::Y]);
        let current = self.imported(bookmark);
        let l = if tc.draw(gs::booleans()) {
            self.target(&tc, true, &current)
        } else {
            current
        };
        self.jj_sets(bookmark, l);
    }

    /// A `jj` command at the operation before the latest action moves `x`, `y` or `t`, and
    /// the next merges it with the head.
    #[rule]
    fn jj_runs_at_older_op(&mut self, tc: TestCase) {
        let bookmark = Ref::draw(&tc, &[Ref::X, Ref::T, Ref::Y]);
        let current = self.older.1.get(bookmark).v.l.clone();
        let l = self.target(&tc, true, &current);
        self.jj_sets_at_older_op(bookmark, l);
    }

    /// `jj undo`, or `jj op restore` to the operation before the latest action or to the one
    /// both machines last synced at.
    #[rule]
    fn jj_restores(&mut self, tc: TestCase) {
        let target = match tc.draw(gs::integers::<u8>().max_value(2)) {
            0 => None,
            1 => Some(self.older.0.clone()),
            _ => Some(self.synced.0.clone()),
        };
        self.jj_restores_to(target);
    }

    /// `y` moves in `origin`, and `jj git fetch` fetches it.
    #[rule]
    fn jj_fetches(&mut self, tc: TestCase) {
        let upstream = self.target(&tc, false, &self.upstream);
        self.jj_fetches_from(upstream);
    }

    /// The other machine moves `x` or `t`, or fetches `y` after it moved in `origin`, with
    /// or without this machine's latest operations, and both sync (`musubi_realizes_with`).
    #[rule(weight = 2)]
    fn musubi_realizes(&mut self, tc: TestCase) {
        let concurrent = tc.draw(gs::booleans());
        let fetch = tc.draw(gs::booleans());
        let locked = tc.draw(gs::booleans());
        let moved = (!fetch).then(|| {
            let r = Ref::draw(&tc, &[Ref::X, Ref::T]);
            // The other machine's: as when they last synced, if it is behind, or else as
            // here.
            let current = if concurrent {
                self.synced.1.get(r).v.l.clone()
            } else {
                self.model.get(r).v.l.clone()
            };
            (r, self.target(&tc, true, &current))
        });
        let upstream = self.target(&tc, false, &self.upstream);
        // A `jj` command here that the realization is beside, where the records agree.
        let beside = (self.model.records_agree() && tc.draw(gs::booleans())).then(|| {
            if tc.draw(gs::booleans()) {
                // Something other than this machine has, but perhaps what the other fetched.
                let origin = &self.model.get(Ref::Origin).g;
                Beside::Fetches(self.target(&tc, false, origin))
            } else {
                let r = Ref::draw(&tc, &[Ref::X, Ref::T, Ref::Y]);
                let current = self.imported(r);
                Beside::Sets(r, self.target(&tc, true, &current))
            }
        });
        self.musubi_realizes_with(moved, upstream, locked, concurrent, beside);
    }
}

#[hegel::test(test_cases = refs_cases(), suppress_health_check = [HealthCheck::TooSlow])]
fn bookmarks_conform_to_refs_model(tc: TestCase) {
    hegel::stateful::machine(Refs::new()).steps(10).run(tc);
}

/// Undoing a move from the root restores `x` there even though jj can't export it.
/// `git_refs` still matches `.git`, so the next ordinary command imports nothing.
#[test]
fn undo_of_an_unexportable_bookmark_keeps_it() {
    let mut refs = Refs::new();
    refs.jj_sets(Ref::X, RefTarget::normal(refs.commits[0].clone()));
    refs.jj_sets(Ref::X, RefTarget::normal(refs.commits[3].clone()));
    refs.jj_restores_to(None);
    assert!(refs.model.get(Ref::X).restored);
    let y = refs.imported(Ref::Y);
    refs.jj_sets(Ref::Y, y);
    assert_eq!(
        refs.model.get(Ref::X).v.l,
        RefTarget::normal(refs.commits[0].clone())
    );
}

/// Concurrent fetches conflict `y@origin`; a fetch here settles it, then a restore brings
/// back the conflict. Both machines keep the fetched value in `.git`. Ordinary commands
/// keep the conflict; an explicit fetch resolves it even though the physical ref is unchanged.
#[test]
fn restore_of_a_conflicted_remote_bookmark_waits_for_a_fetch() {
    let mut refs = Refs::new();
    let [base, _, two, three] = [1, 2, 3, 4].map(|i| RefTarget::normal(refs.commits[i].clone()));
    refs.jj_fetches_from(two);
    refs.musubi_realizes_with(None, three, false, true, None);
    assert!(!refs.model.get(Ref::Origin).v.r.is_resolved());
    let conflicted = refs.head();
    refs.jj_fetches_from(base.clone());
    refs.jj_restores_to(Some(conflicted));
    let origin = refs.model.get(Ref::Origin);
    assert!(!origin.v.r.is_resolved() && !origin.restored, "{origin:?}");
    assert_eq!(origin.g, base);
    let x = refs.model.get(Ref::X).v.l.clone();
    let moved = RefTarget::normal(refs.commits[if x == base { 2 } else { 1 }].clone());
    refs.musubi_realizes_with(Some((Ref::X, moved)), base.clone(), false, false, None);
    let y = refs.imported(Ref::Y);
    refs.jj_sets(Ref::Y, y);
    let origin = refs.model.get(Ref::Origin);
    assert!(!origin.v.l.is_resolved() && !origin.v.r.is_resolved());
    assert_eq!(origin.g, base);
    refs.jj_fetches_from(base.clone());
    let origin = refs.model.get(Ref::Origin);
    assert_eq!((&origin.v.l, &origin.v.r), (&base, &base));
}

/// A fetch beside a realization of a conflict, as Hegel found: after both machines have
/// `two`, this machine fetches `base` while the other, behind, fetches `one`, so that the
/// merge conflicts `y@origin`, with `one` as its expected value, and `jj undo` here brings the
/// conflict back once the undo's import has resolved it. Meanwhile the other machine, behind
/// again, fetches `base`, a term of the conflict, then realizes the undo beside its fetch,
/// and merges the two, keeping the fetch. musubi must leave `base` in that machine's `.git`:
/// had it written `one` for the realization, the other machine's next command, which moves
/// `x`, would import that as a move made with git, and move `y` back to `one`.
#[test]
fn realization_beside_a_fetch_keeps_the_fetch() {
    let mut refs = Refs::new();
    let [root, base, one, two] = [0, 1, 2, 3].map(|i| RefTarget::normal(refs.commits[i].clone()));
    refs.musubi_realizes_with(None, two, false, false, None);
    refs.jj_fetches_from(base.clone());
    refs.musubi_realizes_with(None, one, false, true, None);
    refs.jj_restores_to(None);
    assert!(!refs.model.get(Ref::Origin).v.r.is_resolved());
    refs.musubi_realizes_with(None, base.clone(), false, true, None);
    let (there, g) = read(&refs.fixture.load(THERE), Ref::Origin);
    assert_eq!((&there.r, &there.k, &g), (&base, &base, &base));
    refs.musubi_realizes_with(Some((Ref::X, root)), base, false, false, None);
}

/// A resolved merge has its own expected value even if neither parent had it: absence
/// included, where there is no conflict side to choose. jj's merge that produces this is
/// pinned by `ref_laws::a_fetch_can_resolve_a_conflict_to_neither_side`.
#[test]
fn a_resolved_merge_is_its_own_expected_value() {
    let present = RefTarget::normal(CommitId::from_bytes(&[1; 20]));
    let parent = Machine {
        v: Slot {
            l: present.clone(),
            r: present.clone(),
            k: present.clone(),
            tr: true,
        },
        g: present.clone(),
        e: present.clone(),
        moved: false,
        restored: false,
    };
    for target in [
        RefTarget::absent(),
        RefTarget::normal(CommitId::from_bytes(&[2; 20])),
    ] {
        assert_eq!(
            merged_expected(
                |_| panic!("a resolved merge needs no side"),
                &target,
                [&parent, &parent],
                true
            ),
            target,
        );
    }
}

/// A fetch here beside a realization of a conflict, `beside_keeps_fetch` as musubi does it:
/// `y@origin` conflicts as in `restore_of_a_conflicted_remote_bookmark_waits_for_a_fetch`, a
/// fetch of `base` here resolves it, and both machines sync. This machine then restores the
/// conflict, whose expected value is `base`, and while the other machine, behind, moves `t` and
/// merges that with the restore, keeping the conflict, this machine fetches `two`, a term of
/// it. musubi realizes the other machine's merge beside the fetch, and must leave `two` in
/// `.git`, as the merge of the two keeps it: written for the realization alone, `base` would
/// be in `.git` and `two` in the record.
#[test]
fn realization_beside_a_fetch_here_keeps_the_fetch() {
    let mut refs = Refs::new();
    let [base, one, two, three] = [1, 2, 3, 4].map(|i| RefTarget::normal(refs.commits[i].clone()));
    refs.jj_fetches_from(two.clone());
    refs.musubi_realizes_with(None, three, false, true, None);
    assert!(!refs.model.get(Ref::Origin).v.r.is_resolved());
    let conflicted = refs.head();
    refs.jj_fetches_from(base.clone());
    // The other machine moves `x` from where it is, `one`, so that both sync.
    assert_eq!(refs.model.get(Ref::X).v.l, one);
    refs.musubi_realizes_with(
        Some((Ref::X, base.clone())),
        base.clone(),
        false,
        false,
        None,
    );
    refs.jj_restores_to(Some(conflicted));
    assert!(!refs.model.get(Ref::Origin).v.r.is_resolved());
    let fetch = Some(Beside::Fetches(two.clone()));
    refs.musubi_realizes_with(Some((Ref::T, two.clone())), base, false, true, fetch);
    let parents = refs.parents(&refs.head());
    assert_eq!(parents.len(), 2, "merged beside the fetch");
    let repo = refs.fixture.load(HERE);
    let conflicted = parents.iter().any(|op| {
        let op = block_on(repo.loader().load_operation(op)).unwrap();
        let view = block_on(op.view()).unwrap();
        !slot(view.store_view(), Ref::Origin).r.is_resolved()
    });
    assert!(conflicted, "the realization keeps the conflict");
    let origin = refs.model.get(Ref::Origin);
    assert_eq!((&origin.v.r, &origin.v.k, &origin.g), (&two, &two, &two));
}

/// A fetch beside a realization made while taking another machine's `jj op abandon`: the
/// fetches of `two` and `three` conflict `y@origin`, and musubi writes its side, `three`, to
/// both `.git`s. The other machine abandons the operation this machine's op head stands
/// for, so this machine realizes the hub's head, which keeps the conflict, before taking the
/// abandon (protocol.md, "Supersedes"). A `jj git fetch` of `two`, a term of the conflict,
/// publishes after the sync's step has checked the op heads and before the realization is
/// published, as only a command running concurrently can: the test makes the step's calls
/// itself, mapping the op heads before the realization as a node opened since does. musubi
/// must leave `two` in `.git`, and publish the realization merged with the fetch, which keeps
/// it, the fetch renamed first: written for the realization alone, `three` would be in
/// `.git`, and the next command would import it as a move made with git.
#[test]
fn realization_beside_a_fetch_keeps_the_fetch_while_taking_an_abandon() {
    use musubi_core::node::LocalRepo as _;
    use musubi_core::node::Step;

    let mut f = hive();
    let origin = f.env.root().join("origin.git");
    let origin = origin.to_str().unwrap().to_owned();
    for index in [HERE, THERE] {
        f.repo(index).git(&["remote", "set-url", "origin", &origin]);
    }
    let [two, three] = ["two", "three"].map(|m| f.commit_id(HERE, m));
    let upstream = |f: &Fixture, id: &str| {
        f.repo(HERE)
            .git(&["--git-dir", &origin, "update-ref", "refs/heads/y", id]);
    };
    let git_y = |f: &Fixture| {
        let git = f.repo(THERE).git(&["rev-parse", "refs/remotes/origin/y"]);
        git.trim().to_owned()
    };
    upstream(&f, &two);
    f.repo(HERE).jj(&["git", "fetch"]);
    upstream(&f, &three);
    f.repo(THERE).jj(&["git", "fetch"]);
    f.hive.sync(HERE).unwrap();
    f.hive.sync(THERE).unwrap();
    f.hive.sync(HERE).unwrap();
    assert_eq!(git_y(&f), three, "musubi's side");

    // Importing nothing, so that the conflict stays.
    let jj = |f: &Fixture, args: &[&str]| {
        f.repo(HERE)
            .jj(&[&["--ignore-working-copy"], args].concat());
    };
    jj(&f, &["bookmark", "create", "dropped", "-r", "@"]);
    let dropped = f.load(HERE).op_id().hex();
    let dropped_canonical = f
        .node(HERE)
        .canonicalize(&LocalOp(OperationId::try_from_hex(&dropped).unwrap()))
        .unwrap();
    f.sync();
    jj(&f, &["new", "-m", "kept"]);
    jj(&f, &["op", "abandon", &dropped]);
    f.hive.sync(HERE).unwrap();
    let (head_slot, _) = read(&f.load(HERE), Ref::Origin);
    assert!(!head_slot.r.is_resolved(), "{head_slot:?}");
    // A fix-up keeps the pre-abandon expectation explicitly, rather than inferring it
    // from the shortened history. Its canonical shared view is its parent's.
    let mut fixups = 0;
    let node = f.node(HERE);
    let heads = node.canonical_heads().unwrap();
    let history = node
        .canonical_store()
        .ancestors_until(&heads, |_| false)
        .unwrap();
    for op in history {
        let raw = node.canonical_store().read_operation(&op).unwrap();
        if let Some(expected) = raw.metadata.attributes.get("musubi.expected") {
            assert!(
                expected
                    .lines()
                    .any(|line| line == format!("refs/remotes/origin/y {three}"))
            );
            let parent = node.canonical_store().parents(&op).unwrap();
            assert_eq!(parent.len(), 1);
            assert_eq!(
                raw.view_id,
                node.canonical_store()
                    .read_operation(&parent[0])
                    .unwrap()
                    .view_id
            );
            fixups += 1;
        }
    }
    assert!(
        fixups > 0,
        "the expected-value snapshot is carried across the drop"
    );

    // The sync's steps up to the realization, the first of which prepares to take the
    // abandon.
    f.hive.fetch(THERE).unwrap();
    let unpublished_heads = f.node(THERE).local_heads().unwrap();
    let canonical_before: BTreeSet<_> = f
        .node(THERE)
        .canonical_store()
        .operation_ids()
        .unwrap()
        .into_iter()
        .collect();
    let known = loop {
        let member = &mut f.hive.members[THERE];
        let known = member.core.known().1.clone();
        if member.adapter.is_local(&known).unwrap() {
            break known;
        }
        let step = member.core.step(&mut member.adapter).unwrap();
        assert!(matches!(step, Step::Realized(_)), "{step:?}");
    };
    assert_eq!(f.node(THERE).local_heads().unwrap(), unpublished_heads);
    assert_eq!(git_y(&f), three, "unpublished realization exports nothing");
    assert_eq!(
        f.node(THERE)
            .canonical_store()
            .operation_ids()
            .unwrap()
            .into_iter()
            .collect::<BTreeSet<_>>(),
        canonical_before
    );
    upstream(&f, &two);
    f.repo(THERE).jj(&["git", "fetch"]);
    // As `realize` does on a node opened since the records were prepared, which gives the
    // fetch a canonical form on the abandoned operation.
    let old_heads = f.node(THERE).canonical_heads().unwrap();
    let incoming = f
        .node(THERE)
        .to_node(&musubi_jj::records::HubOp(CanonicalOp(
            OperationId::try_from_hex(known.hex()).unwrap(),
        )))
        .unwrap()[0]
        .0
        .clone();
    // Independently contract the old heads, then take max(images(heads) ∪ {incoming}).
    // Using the old names as parents would revive the dropped operation.
    let node = f.node(THERE);
    let store = node.canonical_store();
    let mut contraction =
        musubi_jj::canonical::Contraction::new(store, [dropped_canonical.clone()]).unwrap();
    let mut candidates = vec![incoming.clone()];
    for head in &old_heads {
        candidates.extend(contraction.images(store, head).unwrap());
    }
    let expected_parents: BTreeSet<_> = candidates
        .iter()
        .filter(|a| {
            !candidates
                .iter()
                .any(|b| a != &b && store.is_ancestor_of(a, b).unwrap())
        })
        .cloned()
        .collect();
    assert_eq!(
        expected_parents.len(),
        2,
        "the renamed fetch and the incoming head"
    );

    let graph = OriginalGraph::observe(node, &old_heads, &incoming);
    let bases = store
        .closest_common_ancestors(
            std::slice::from_ref(&incoming),
            &expected_parents
                .iter()
                .filter(|op| **op != incoming)
                .cloned()
                .collect::<Vec<_>>(),
        )
        .unwrap();
    assert_eq!(bases.len(), 1);
    let at = |local: &LocalOp| {
        let op = block_on(node.loader().load_operation(&local.0)).unwrap();
        slot(block_on(op.view()).unwrap().store_view(), Ref::Origin)
    };
    let base_slot = at(&node.local_of(&bases[0]).unwrap());
    let local = node.local_heads().unwrap();
    assert_eq!(local.len(), 1);
    let local_slot = at(&local[0]);
    let incoming_local = node.local_of(&incoming).unwrap();
    assert_eq!(
        node.canonical_of(&incoming_local).unwrap(),
        incoming,
        "realize/canon inverse before publication"
    );
    let realized_slot = at(&incoming_local);
    let incoming_slot = slot(&store.read_operation_view(&incoming).unwrap(), Ref::Origin);
    assert_eq!(
        (&realized_slot.l, &realized_slot.r, realized_slot.tr),
        (&incoming_slot.l, &incoming_slot.r, incoming_slot.tr),
        "the realization preserves the canonical input's shared ref fields"
    );
    let time = |local: &LocalOp| {
        block_on(node.loader().op_store().read_operation(&local.0))
            .unwrap()
            .metadata
            .time
            .end
            .timestamp
    };
    let first = time(&incoming_local) <= time(&local[0]);
    let three_target = RefTarget::normal(CommitId::try_from_hex(&three).unwrap());
    let two_target = RefTarget::normal(CommitId::try_from_hex(&two).unwrap());
    let op = block_on(node.loader().load_operation(&local[0].0)).unwrap();
    let mut model = RefsModel::new(block_on(node.loader().load_at(&op)).unwrap());
    let (boundary, expected_slot, expected_git) = model.abandon_beside(
        &json!({"par": graph.parents, "drops": [graph.id(node, &dropped_canonical)],
            "heads": old_heads.iter().map(|h| graph.id(node, h)).collect::<Vec<_>>(),
            "incoming": graph.id(node, &incoming), "base": graph.id(node, &bases[0]), "first": first}),
        &[
            (graph.id(node, &bases[0]), base_slot, three_target.clone()),
            (graph.id(node, &old_heads[0]), local_slot, two_target.clone()),
            (graph.id(node, &incoming), incoming_slot, three_target.clone()),
        ],
        [&two_target, &two_target],
    );
    assert_eq!(expected_git, two_target);
    assert_eq!(boundary["bases"], json!([graph.id(node, &bases[0])]));
    let expected_model_parents: BTreeSet<usize> =
        serde_json::from_value(boundary["parents"].clone()).unwrap();
    assert_eq!(
        expected_parents
            .iter()
            .map(|p| graph.id(node, p))
            .collect::<BTreeSet<_>>(),
        expected_model_parents
    );
    // The Lean contraction is checked against every actual survivor, not just final heads.
    for (i, op) in graph.operations.iter().enumerate() {
        if op == &dropped_canonical {
            continue;
        }
        let image = contraction.images(store, op).unwrap();
        assert_eq!(image.len(), 1);
        let actual: Vec<_> = store
            .parents(&image[0])
            .unwrap()
            .iter()
            .map(|p| graph.id(node, p))
            .collect();
        assert_eq!(json!(actual), boundary["contracted"][i], "survivor {i}");
    }

    f.hive.members[THERE].adapter.advance(&known).unwrap();
    // Observe the returned raw heads before any subsequent jj command merges them.
    let node = f.node(THERE);
    let heads = node.local_heads().unwrap();
    assert_eq!(heads.len(), 1);
    let merged = block_on(node.loader().op_store().read_operation(&heads[0].0)).unwrap();
    let parents: BTreeSet<_> = merged
        .parents
        .iter()
        .map(|p| node.canonicalize(&LocalOp(p.clone())).unwrap())
        .collect();
    assert_eq!(parents, expected_parents);
    let canonical = node.canonicalize(&heads[0]).unwrap();
    assert!(
        !node
            .canonical_store()
            .is_ancestor_of(&dropped_canonical, &canonical)
            .unwrap()
    );
    let published = block_on(node.loader().load_operation(&heads[0].0)).unwrap();
    assert_eq!(
        slot(
            block_on(published.view()).unwrap().store_view(),
            Ref::Origin
        ),
        expected_slot
    );
    graph.check_translation(node, &heads[0], &canonical);
    assert_eq!(git_y(&f), two, "the fetch in .git");
    let ops = |f: &Fixture, index: usize| {
        let template = "description ++ \"\\n\"";
        f.repo(index).jj(&[
            "--ignore-working-copy",
            "op",
            "log",
            "--no-graph",
            "-T",
            template,
        ])
    };
    // The fetch was moved onto the renamed history before the merge, which otherwise would
    // have merged it on the dropped operation, against an older common ancestor.
    let log = ops(&f, THERE);
    assert!(!log.contains("create bookmark dropped"), "{log}");

    // A neutral publication tip inherits this current fetch/expectation, rather than
    // replaying the fix-up's earlier `three` snapshot. Exercise the primitive on this
    // observed parent before any jj command can import or reconcile the fetch.
    let before = read(&f.load(THERE), Ref::Origin);
    let before_url = f.repo(THERE).git(&["remote", "get-url", "origin"]);
    let node = f.node(THERE);
    let parent = node.canonical_heads().unwrap().swap_remove(0);
    let before_presence = node.presence(&parent).unwrap();
    let before_view = node
        .canonical_store()
        .read_operation(&parent)
        .unwrap()
        .view_id;
    let tip = node
        .write_drop_tip(&musubi_jj::records::HubOp(parent.clone()))
        .unwrap()
        .unwrap();
    let raw = node.canonical_store().read_operation(&tip.0).unwrap();
    assert_eq!(raw.parents, [parent.0]);
    assert_eq!(raw.view_id, before_view);
    assert_eq!(node.presence(&tip.0).unwrap(), before_presence);
    assert!(raw.metadata.workspace_name.is_none());
    for key in [
        "musubi.work",
        "musubi.forget",
        "musubi.forget-after",
        "musubi.settings",
        "musubi.expected",
    ] {
        assert!(!raw.metadata.attributes.contains_key(key), "replayed {key}");
    }
    assert_eq!(read(&f.load(THERE), Ref::Origin), before);
    assert_eq!(git_y(&f), two);

    f.repo(THERE).jj(&["status"]);
    f.sync();
    f.assert_converged();
    f.reopen(THERE);
    f.sync();
    assert_eq!(
        f.repo(THERE).git(&["remote", "get-url", "origin"]),
        before_url
    );
    let two = RefTarget::normal(CommitId::try_from_hex(&two).unwrap());
    for index in [HERE, THERE] {
        let (slot, git) = read(&f.load(index), Ref::Origin);
        assert_eq!((&slot.r, &git), (&two, &two), "y@origin on {index}");
        let log = ops(&f, index);
        assert!(!log.contains("create bookmark dropped"), "{log}");
    }
}

/// Project observed histories into original-operation names. Prefer the old local history
/// when an incoming contracted version has the same original: its old parents are precisely
/// the ghost ancestry the contraction model retains. Fresh fix-up operations are originals
/// too; realization must not allocate any. This does not infer identity from descriptions.
struct OriginalGraph {
    ids: BTreeMap<OperationId, usize>,
    operations: Vec<CanonicalOp>,
    parents: Vec<Vec<usize>>,
    stored: BTreeSet<CanonicalOp>,
}

impl OriginalGraph {
    fn observe(node: &NodeRepo, old: &[CanonicalOp], incoming: &CanonicalOp) -> Self {
        let mut graph = Self {
            ids: BTreeMap::new(),
            operations: vec![],
            parents: vec![],
            stored: node
                .canonical_store()
                .operation_ids()
                .unwrap()
                .into_iter()
                .collect(),
        };
        let root = node.canonical_store().root_operation_id();
        graph.add(node, root);
        for head in old.iter().chain([incoming]) {
            graph.add(node, head);
        }
        graph
    }

    fn add(&mut self, node: &NodeRepo, op: &CanonicalOp) -> usize {
        let store = node.canonical_store();
        let origin = store.original_id(op).unwrap();
        if let Some(&id) = self.ids.get(&origin) {
            return id;
        }
        let parents = store
            .parents(op)
            .unwrap()
            .iter()
            .map(|p| self.add(node, p))
            .collect();
        let id = self.operations.len();
        self.ids.insert(origin, id);
        self.operations.push(op.clone());
        self.parents.push(parents);
        id
    }

    fn id(&self, node: &NodeRepo, op: &CanonicalOp) -> usize {
        self.ids[&node.canonical_store().original_id(op).unwrap()]
    }

    /// Translation's inverse, parent preservation, reachable injectivity and no new IDs
    /// immediately after publication, before another command or full convergence.
    fn check_translation(&self, node: &mut NodeRepo, head: &LocalOp, merged: &CanonicalOp) {
        let mut stack = vec![head.clone()];
        let mut seen = BTreeSet::new();
        let mut forms = BTreeSet::new();
        while let Some(local) = stack.pop() {
            if !seen.insert(local.clone())
                || local.0 == *node.loader().op_store().root_operation_id()
            {
                continue;
            }
            let canonical = node.canonicalize(&local).unwrap();
            assert!(
                forms.insert(canonical.clone()),
                "two reachable realizations of {canonical:?}"
            );
            let raw = block_on(node.loader().op_store().read_operation(&local.0)).unwrap();
            let parents = node.canonical_store().parents(&canonical).unwrap();
            if parents == [node.canonical_store().root_operation_id().clone()] {
                continue; // The joining machine's earlier operations aren't hive history.
            }
            let locals: Vec<_> = raw.parents.into_iter().map(LocalOp).collect();
            let translated: Vec<_> = locals
                .iter()
                .map(|p| node.canonicalize(p).unwrap())
                .collect();
            assert_eq!(translated, parents);
            stack.extend(locals);
        }
        let after: BTreeSet<_> = node
            .canonical_store()
            .operation_ids()
            .unwrap()
            .into_iter()
            .collect();
        assert_eq!(after.difference(&self.stored).collect::<Vec<_>>(), [merged]);
    }
}

/// How many cases to make: `MUSUBI_CONFORMANCE_CASES`, as for the other conformance tests,
/// or 12, each a few tenths of a second of real `jj`, `git` and syncs.
fn refs_cases() -> u64 {
    std::env::var("MUSUBI_CONFORMANCE_CASES")
        .ok()
        .and_then(|cases| cases.parse().ok())
        .unwrap_or(12)
}

/// jj exports a bookmark selected by the native merge even when physical refs match the
/// merged import records. Its ordinary import phase has no changes to publish first.
#[test]
fn an_unchanged_import_exports_a_bookmark_selected_by_a_merge() {
    let mut refs = Refs::new();
    let three = RefTarget::normal(refs.commits[4].clone());
    let base = RefTarget::normal(refs.commits[1].clone());
    refs.musubi_realizes_with(
        None,
        three,
        false,
        false,
        Some(Beside::Fetches(base.clone())),
    );
    refs.jj_sets_at_older_op(Ref::Y, RefTarget::normal(refs.commits[2].clone()));
}
