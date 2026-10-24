//! Bookmarks in a colocated repository, against `formal/Musubi/Refs.lean`
//! (docs/internals/conformance.md, "Per-machine refs"). Hegel moves refs with git, runs
//! `jj` commands, `jj undo` and `jj op restore`, fetches, and has another machine move
//! bookmarks, move a tag or fetch, for musubi to realize here, its export succeeding or
//! failing. Beside the real machine it keeps the model's `Machine` for each ref it follows,
//! with jj's own `merge_ref_targets` as the model's merge (`ref_laws` checks that it obeys
//! the laws the model assumes), and steps each as the model's `LStep`s or `CStep`s that the
//! real action performs. After every action each bookmark, its remote bookmark and whether
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
//! (`realizeMerge_eq`). Two fetches merge so to a conflicted `y@origin`, one side of which
//! musubi writes to `.git` (`exportConflicted`), the same on both machines.
//!
//! The refs are a local bookmark `x`, which git moves; a local bookmark `y`, which git
//! doesn't; `y@origin`, which `y` tracks, which git moves and fetches move; and a tag `t`,
//! which git moves, and whose slot is a local bookmark's. The model has one ref per machine;
//! here `y` and `y@origin` share the bookmark `y`, so a step of one is a `set` of the other.

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
use jj_lib::refs::merge_ref_targets;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;

use crate::fixture::Fixture;

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

/// The model's `TSlot`: its `Slot`, and whether the bookmark tracks the remote ref `r`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Slot {
    l: RefTarget,
    r: RefTarget,
    k: RefTarget,
    tr: bool,
}

/// The model's `Machine`: the view's slot, `.git`'s ref, and the ghost `moved`.
#[derive(Clone, Debug)]
struct Machine {
    v: Slot,
    g: RefTarget,
    moved: bool,
    /// Ghost: a `jj undo` or `jj op restore` since the last import left a record that
    /// doesn't match `.git`, which `restoreLocal_inv` and `restoreRemote_cinv` allow only
    /// where the restored slot isn't `Restorable`.
    restored: bool,
}

/// The model's `RefAlg` instance: jj's merge, and its notions of resolved and writable.
struct Alg {
    repo: Arc<ReadonlyRepo>,
}

impl Alg {
    fn merge(&self, a: &RefTarget, b: &RefTarget, c: &RefTarget) -> RefTarget {
        block_on(merge_ref_targets(self.repo.index(), a, b, c)).unwrap()
    }

    fn resolved(t: &RefTarget) -> bool {
        t.is_resolved()
    }

    fn writable(&self, t: &RefTarget) -> bool {
        Self::resolved(t) && t.as_normal() != Some(self.repo.store().root_commit_id())
    }

    /// `Sides.side`: the side of a conflict that musubi writes to `.git`
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

/// `bmerge`, two-valued `trivial_merge`.
fn bmerge(a: bool, b: bool, c: bool) -> bool {
    if a == b { c } else { a }
}

impl Slot {
    /// `TSlot.norm`: no remote ref with no target unless tracked and the bookmark exists.
    fn norm(mut self) -> Self {
        if self.r.is_absent() && (!self.tr || self.l.is_absent()) {
            self.tr = false;
        }
        self
    }

    /// `TSlot.set`.
    fn set(&self, l: RefTarget) -> Self {
        Self { l, ..self.clone() }.norm()
    }

    /// `TSlot.track`.
    fn track(&self, alg: &Alg) -> Self {
        let base = if self.tr {
            self.r.clone()
        } else {
            RefTarget::absent()
        };
        Self {
            l: alg.merge(&self.l, &base, &self.r),
            tr: true,
            ..self.clone()
        }
        .norm()
    }

    /// `TSlot.import`, every ref here tracked by default (`auto`). Also returns whether jj
    /// set the bookmark (`set_local_bookmark_target`), which drops the bookmark's other remote
    /// refs with no target if it is gone.
    fn import(&self, alg: &Alg, g: &RefTarget) -> (Self, bool) {
        if *g == self.r {
            return (
                Self {
                    k: g.clone(),
                    ..self.clone()
                },
                false,
            );
        }
        let tr = if self.r.is_absent() && !self.tr {
            true
        } else {
            self.tr
        };
        let l = if tr {
            alg.merge(&self.l, &self.r, g)
        } else {
            self.l.clone()
        };
        let imported = Self {
            l,
            r: g.clone(),
            k: g.clone(),
            tr,
        };
        (imported.norm(), tr)
    }

    /// `TSlot.mergeL`.
    fn merge_l(alg: &Alg, b: &Self, v: &Self, w: &Self) -> Self {
        if b.l == w.l {
            v.clone()
        } else {
            v.set(alg.merge(&v.l, &b.l, &w.l))
        }
    }

    /// `TSlot.merge`: jj's merge of `v` with `w` against `b`.
    fn merge(alg: &Alg, b: &Self, v: &Self, w: &Self) -> Self {
        let r = Self::merge_l(alg, b, v, w);
        let k = alg.merge(&v.k, &b.k, &w.k);
        if b.r == w.r && b.tr == w.tr {
            Self { k, ..r }
        } else {
            Self {
                l: alg.merge(&v.l, &b.l, &w.l),
                r: alg.merge(&r.r, &b.r, &w.r),
                k,
                tr: bmerge(r.tr, b.tr, w.tr),
            }
            .norm()
        }
    }
}

impl Machine {
    /// `LStep.gitMove` and `RStep.gitMove`.
    fn git_move(&mut self, g: RefTarget) {
        self.g = g;
        self.moved = true;
    }

    /// `LStep.jjImport` and `RStep.jjImport`, as `TSlot.import`. Returns whether jj set the
    /// bookmark.
    fn jj_import(&mut self, alg: &Alg) -> bool {
        let (v, set) = self.v.import(alg, &self.g);
        self.v = v;
        self.moved = false;
        self.restored = false;
        set
    }

    /// `LStep.jjExport`, `TSlot.exportLocal`, where the update of `.git` can succeed; where
    /// it can't, because `.git` is locked, no step, as the model has a failed update. An
    /// update to the value `.git` already has writes nothing, so succeeds. Copying the
    /// bookmark to `R` tracks it.
    fn export_local(&mut self, alg: &Alg, git_writable: bool) {
        let before = self.v.r.clone();
        let v = &mut self.v;
        if v.l == v.k {
            if Alg::resolved(&v.l) {
                v.r = v.l.clone();
            }
        } else if alg.writable(&v.l)
            && Alg::resolved(&v.k)
            && (self.g == v.l || (git_writable && self.g == v.k))
        {
            v.r = v.l.clone();
            v.k = v.l.clone();
            self.g = v.l.clone();
        }
        if self.v.r != before {
            self.v.tr = true;
            self.v = self.v.clone().norm();
        }
    }

    /// `RStep.jjExport`, `exportRemote`.
    fn export_remote(&mut self, alg: &Alg) {
        let v = &mut self.v;
        if v.r != v.k
            && alg.writable(&v.r)
            && Alg::resolved(&v.k)
            && (self.g == v.k || self.g == v.r)
        {
            v.k = v.r.clone();
            self.g = v.r.clone();
        }
    }

    /// musubi's export of a conflicted remote bookmark (`exportConflicted`,
    /// `export_conflicted_remote_bookmarks`): its side, written to `.git` if that holds a
    /// value the hive knows of, a term of the conflict or the record, and to the record.
    fn export_conflicted(&mut self, alg: &Alg) {
        let v = &mut self.v;
        if Alg::resolved(&v.r) {
            return;
        }
        let Some(side) = alg.side(&v.r) else {
            return;
        };
        if self.g != side {
            let actual = self.g.as_normal();
            let known = v.r.iter().any(|term| term.as_ref() == actual)
                || (Alg::resolved(&v.k) && v.k.as_normal() == actual);
            if !known {
                return;
            }
            self.g = side.clone();
        }
        v.k = side;
    }

    /// The model's invariant for `r`: `LInv`, or for `y@origin` `CInv`, which is `RInv`
    /// but for a conflicted remote bookmark whose side musubi wrote.
    fn strict_inv(&self, alg: &Alg, r: Ref) -> bool {
        if r != Ref::Origin {
            return self.moved || (self.v.r == self.g && self.v.k == self.g);
        }
        Alg::resolved(&self.g)
            && (self.moved
                || (self.v.k == self.g
                    && (self.v.r == self.g
                        || (!Alg::resolved(&self.v.r)
                            && alg.side(&self.v.r).as_ref() == Some(&self.g)))))
    }

    /// `strict_inv`, but where a restore left the record behind (`restored`).
    fn inv(&self, alg: &Alg, r: Ref) -> bool {
        self.restored || self.strict_inv(alg, r)
    }

    /// `Restorable`: whether restoring `o` here keeps the invariant, as the export puts
    /// `.git` back or there is nothing to put back. For a remote bookmark (`remote`) that is
    /// about its target, otherwise about the bookmark's.
    fn restorable(&self, alg: &Alg, o: &Slot, remote: bool) -> bool {
        let target = if remote { &o.r } else { &o.l };
        alg.writable(target) || *target == self.v.k || o.r == self.v.r
    }
}

/// The shared fields of the refs: `x`, `t`, and `y@origin`'s slot with no `K`.
type Shared = (RefTarget, RefTarget, Slot);

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
    fn set(&mut self, bookmark: Ref, l: RefTarget) {
        for r in Ref::ALL {
            if r.bookmark() == bookmark.bookmark() {
                let v = self.at(r).v.set(l.clone());
                self.at(r).v = v;
            }
        }
    }

    /// `jj bookmark set` or `delete` moving `bookmark` to `l`: a `set`, and if it creates
    /// `y`, `TSlot.track` of `y@origin`, which `remotes.origin.auto-track-bookmarks` covers,
    /// and a `set` of `y@git` with the bookmark that merges into.
    fn bookmark_set(&mut self, alg: &Alg, bookmark: Ref, l: RefTarget) {
        let created = self.get(bookmark).v.l.is_absent() && l.is_present();
        self.set(bookmark, l);
        if created && bookmark.bookmark() == Ref::Origin.bookmark() {
            let origin = self.get(Ref::Origin).v.track(alg);
            let y = self.get(Ref::Y).v.set(origin.l.clone());
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
        Ref::ALL.map(|r| Slot::merge(alg, &base.get(r).v, &first.get(r).v, &second.get(r).v))
    }

    fn slots(&self) -> Vec<Slot> {
        self.0.iter().map(|m| m.v.clone()).collect()
    }

    /// jj's import of `refs`, in its order, each a `jjImport` and a `set` of the others with
    /// the bookmark. Returns whether it changed the view.
    fn import(&mut self, alg: &Alg, refs: &[Ref]) -> bool {
        let before = self.slots();
        for &r in refs {
            if self.at(r).jj_import(alg) {
                let l = self.at(r).v.l.clone();
                self.set(r, l);
            }
        }
        self.slots() != before
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

    /// A `jj` command: an import, exported if it changed the view, since jj exports only a
    /// transaction with changes, then the command's own transaction, `change`, exported if it
    /// changed the view.
    fn jj(&mut self, alg: &Alg, change: impl FnOnce(&mut Self)) {
        if self.import(alg, &Ref::ALL) {
            self.export(alg, false, false);
        }
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
fn hive() -> Fixture {
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
                v,
                g,
                moved: false,
                restored: false,
            }
        }));
        let head = (repo.op_id().clone(), model.clone());
        let mut refs = Self {
            fixture,
            alg: Alg { repo },
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
    /// against the older operation, as `TSlot.merge`, then imports, and exports if that
    /// changed anything. If the latest action made no operation, the command's operation is
    /// simply the next.
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
            model.import(&self.alg, &[Ref::Origin]);
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
    /// be the same on both machines.
    fn musubi_realizes_with(
        &mut self,
        moved: Option<(Ref, RefTarget)>,
        upstream: RefTarget,
        locked: bool,
        concurrent: bool,
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
        // the side musubi wrote there, as this machine's import would
        // (`conflicted_import_agrees`).
        if let Some(side) = self.conflicted_side(&expected) {
            expected.at(Ref::Origin).g = side;
            expected.import(&self.alg, &[Ref::Origin]);
        }
        match moved {
            None => {
                let (theirs, _) = expected
                    .get(Ref::Origin)
                    .v
                    .import(&self.alg, &self.upstream);
                expected.set(Ref::Y, theirs.l.clone());
                expected.at(Ref::Origin).v = Slot {
                    k: expected.get(Ref::Origin).v.k.clone(),
                    ..theirs
                };
            }
            Some((r, c)) => expected.set(r, c),
        }
        assert_eq!(
            canonical,
            expected.shared(),
            "the other machine's x, t, y and y@origin"
        );
        self.fixture.hive.sync(THERE).unwrap();
        let lock = self
            .fixture
            .repo(HERE)
            .path()
            .join(".git/refs/heads/x.lock");
        if locked {
            std::fs::write(&lock, "").unwrap();
        }
        self.fixture.hive.sync(HERE).unwrap();
        if locked {
            std::fs::remove_file(&lock).unwrap();
        }
        // `LStep.advance` for `x`, `y` and `t`, and `CStep.advance` for `y@origin`, then the
        // export, if there was anything to realize: a fetch that brings nothing new makes no
        // operation.
        if expected.shared() != base.shared() {
            // `CStep.advance`'s precondition, which offering no root commit keeps.
            let g = self.model.at(Ref::Origin).g.clone();
            let advances = |r: &RefTarget| {
                *r == g || self.alg.writable(r) || (!Alg::resolved(r) && self.alg.side(r).is_some())
            };
            assert!(advances(&canonical.2.r));
            if ours == synced_op {
                self.model.realize(&canonical);
            } else {
                // Theirs is realized here from the base, its record the base's, and merged
                // with ours as the other machine merged them.
                let mut theirs = base.clone();
                theirs.realize(&canonical);
                let parents = self.merge_parents();
                assert!(
                    parents.contains(&ours),
                    "merged {parents:?}, not ours {ours:?}"
                );
                let merged = if parents[0] == ours {
                    Model::merge(&self.alg, &base, &self.model, &theirs)
                } else {
                    Model::merge(&self.alg, &base, &theirs, &self.model)
                };
                for (r, v) in Ref::ALL.into_iter().zip(merged) {
                    self.model.at(r).v = v;
                }
                assert!(advances(&self.model.get(Ref::Origin).v.r));
            }
            self.model.export(&self.alg, locked, true);
        }
        self.check();
        // Every machine writes the same side of a conflicted `y@origin` to its `.git`.
        if let Some(side) = self.conflicted_side(&self.model) {
            let (there, g) = read(&self.fixture.load(THERE), Ref::Origin);
            assert_eq!(
                there.r,
                self.model.get(Ref::Origin).v.r,
                "the other machine's y@origin"
            );
            assert_eq!(g, side, "the other machine's refs/remotes/origin/y");
        }
        self.synced = (self.head(), self.model.clone());
    }

    /// The side musubi writes for `y@origin` in `model`, if it is conflicted.
    fn conflicted_side(&self, model: &Model) -> Option<RefTarget> {
        let r = &model.get(Ref::Origin).v.r;
        if Alg::resolved(r) {
            None
        } else {
            self.alg.side(r)
        }
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
        self.musubi_realizes_with(moved, upstream, locked, concurrent);
    }
}

#[hegel::test(test_cases = refs_cases(), suppress_health_check = [HealthCheck::TooSlow])]
fn bookmarks_conform_to_refs_model(tc: TestCase) {
    hegel::stateful::machine(Refs::new()).steps(10).run(tc);
}

/// `restore_reverts`, as jj does it, with no sync: `x` at the root commit, which jj can't
/// export, then moved to `two` and exported, then `jj undo`, which restores `x` to the root
/// and `x@git` to `one`, but keeps `git_refs` at `two`. The next `jj` command takes `.git`'s
/// `two` for a move made with git, and makes `x` a conflict.
#[test]
fn undo_of_an_unexportable_bookmark_conflicts_it() {
    let mut refs = Refs::new();
    refs.jj_sets(Ref::X, RefTarget::normal(refs.commits[0].clone()));
    refs.jj_sets(Ref::X, RefTarget::normal(refs.commits[3].clone()));
    refs.jj_restores_to(None);
    assert!(refs.model.get(Ref::X).restored);
    let y = refs.imported(Ref::Y);
    refs.jj_sets(Ref::Y, y);
    assert!(!refs.model.get(Ref::X).v.l.is_resolved());
}

/// How many cases to make: `MUSUBI_CONFORMANCE_CASES`, as for the other conformance tests,
/// or 12, each a few tenths of a second of real `jj`, `git` and syncs.
fn refs_cases() -> u64 {
    std::env::var("MUSUBI_CONFORMANCE_CASES")
        .ok()
        .and_then(|cases| cases.parse().ok())
        .unwrap_or(12)
}
