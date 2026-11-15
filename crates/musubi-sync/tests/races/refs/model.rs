//! The model's side of the refs conformance test: the refs it follows, its `Machine` and
//! `Model` stepping as the Lean oracle's functions, and the judgment of the real repository
//! against it. Nothing here runs a command or decides what to do next.

use std::cell::RefCell;
use std::cell::RefMut;
use std::sync::Arc;

use futures::executor::block_on;
use hegel::TestCase;
use hegel::generators as gs;
use jj_lib::backend::CommitId;
use jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
use jj_lib::op_store::RefTarget;
use jj_lib::op_store::RemoteRefState;
use jj_lib::op_store::View;
use jj_lib::ref_name::GitRefName;
use jj_lib::ref_name::RefName;
use jj_lib::ref_name::RemoteName;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;

use crate::refs_model::RefsModel;
use crate::refs_model::Slot;

/// A ref the test follows, as the model's `Slot` has it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Ref {
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
    pub(super) const ALL: [Self; 4] = [Self::X, Self::Y, Self::Origin, Self::T];

    /// The bookmark, or for `T` the tag.
    pub(super) fn bookmark(self) -> &'static str {
        match self {
            Self::X => "x",
            Self::Y | Self::Origin => "y",
            Self::T => "t",
        }
    }

    pub(super) fn remote(self) -> &'static RemoteName {
        match self {
            Self::X | Self::Y | Self::T => REMOTE_NAME_FOR_LOCAL_GIT_REPO,
            Self::Origin => RemoteName::new("origin"),
        }
    }

    pub(super) fn git_ref(self) -> &'static str {
        match self {
            Self::X => "refs/heads/x",
            Self::Y => "refs/heads/y",
            Self::Origin => "refs/remotes/origin/y",
            Self::T => "refs/tags/t",
        }
    }

    /// One of `refs`, drawn.
    pub(super) fn draw(tc: &TestCase, refs: &[Self]) -> Self {
        tc.draw_named("ref", gs::sampled_from(refs))
    }
}

/// The model's `Machine`: the view's slot, `.git`'s ref, and the ghost `moved`; for
/// `y@origin`, `CMachine`, with the expected value of a conflicted remote bookmark.
#[derive(Clone, Debug)]
pub(super) struct Machine {
    pub(super) v: Slot,
    pub(super) g: RefTarget,
    pub(super) moved: bool,
    /// Ghost, shared: `CMachine.E` where `R` is a conflict (`Machine::expected`).
    pub(super) e: RefTarget,
    /// Ghost: a `jj undo` or `jj op restore` since the last import left a record that
    /// doesn't match `.git`, which `restoreLocal_inv` and `restoreRemote_cinv` allow only
    /// where the restored slot isn't `Restorable`.
    pub(super) restored: bool,
}

/// The model's `RefAlg` instance, jj's, and `Sides`: the model itself, the oracle's
/// (`RefsModel`), and what the test reads of jj's targets.
pub(super) struct Alg {
    pub(super) repo: Arc<ReadonlyRepo>,
    pub(super) lean: RefCell<RefsModel>,
}

impl Alg {
    pub(super) fn lean(&self) -> RefMut<'_, RefsModel> {
        self.lean.borrow_mut()
    }

    pub(super) fn resolved(t: &RefTarget) -> bool {
        t.is_resolved()
    }

    pub(super) fn writable(&self, t: &RefTarget) -> bool {
        Self::resolved(t) && t.as_normal() != Some(self.repo.store().root_commit_id())
    }

    /// `Sides.side`: the side of a conflict a merge makes that musubi writes to `.git`
    /// (`export_conflicted_remote_bookmarks`), the one committed last, then the greatest
    /// commit id; none if no side is present.
    pub(super) fn side(&self, t: &RefTarget) -> Option<RefTarget> {
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
    pub(super) fn git_move(&mut self, g: RefTarget) {
        self.g = g;
        self.moved = true;
    }

    /// `LStep.jjImport` and `RStep.jjImport`, as `TSlot.import`. Returns whether jj set the
    /// bookmark (`set_local_bookmark_target`), which drops the bookmark's other remote refs
    /// with no target if it is gone.
    pub(super) fn jj_import(&mut self, alg: &Alg) -> bool {
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
    pub(super) fn export_local(&mut self, alg: &Alg, git_writable: bool) {
        if !git_writable && self.v.l != self.v.k && self.g != self.v.l {
            return;
        }
        (self.v, self.g) = alg.lean().export_local(&self.v, &self.g);
    }

    /// `RStep.jjExport`, `exportRemote`.
    pub(super) fn export_remote(&mut self, alg: &Alg) {
        (self.v, self.g) = alg.lean().export_remote(&self.v, &self.g);
    }

    /// The expected value: the remote bookmark if it is resolved, otherwise `e`.
    pub(super) fn expected(&self) -> RefTarget {
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
    pub(super) fn export_conflicted(&mut self, alg: &Alg) {
        (self.v, self.g) = alg.lean().export_conflicted(&self.v, &self.g, &self.e);
    }

    /// musubi's export of a conflicted remote bookmark of a realization beside an op head
    /// whose record is `k` (`exportConflictedBeside`): none where `.git` holds `k`, which that
    /// head put there, and the realization records another value.
    pub(super) fn export_conflicted_beside(&mut self, alg: &Alg, k: &RefTarget) {
        (self.v, self.g) = alg
            .lean()
            .export_conflicted_beside(&self.v, &self.g, &self.e, k);
    }

    /// The model's invariant for `r`: `LInv`, or for `y@origin` `CInv`, which is `RInv`
    /// but for a conflicted remote bookmark, with `.git` at the expected value.
    pub(super) fn strict_inv(&self, alg: &Alg, r: Ref) -> bool {
        if r == Ref::Origin {
            alg.lean()
                .cinv(&self.v, &self.g, self.moved, &self.expected())
        } else {
            alg.lean().linv(&self.v, &self.g, self.moved)
        }
    }

    /// `strict_inv`, but where a restore left the record behind (`restored`).
    pub(super) fn inv(&self, alg: &Alg, r: Ref) -> bool {
        self.restored || self.strict_inv(alg, r)
    }

    /// `Restorable`: whether restoring `o` here keeps the invariant, as the export puts
    /// `.git` back or there is nothing to put back. For a remote bookmark (`remote`) that is
    /// about its target, which may be a conflict too (`CStep.restore`), otherwise about the
    /// bookmark's.
    pub(super) fn restorable(&self, alg: &Alg, o: &Slot, remote: bool) -> bool {
        alg.lean().restorable(o, &self.v, remote)
    }
}

/// The shared fields of the refs: `x`, `t`, and `y@origin`'s slot with no `K`.
#[derive(Debug, PartialEq, Eq)]
pub(super) struct SharedRefs {
    pub(super) x: RefTarget,
    pub(super) tag: RefTarget,
    pub(super) origin: Slot,
}

/// The shared fields of the refs whose slots are `slot`'s.
pub(super) fn shared(slot: impl Fn(Ref) -> Slot) -> SharedRefs {
    SharedRefs {
        x: slot(Ref::X).l,
        tag: slot(Ref::T).l,
        origin: Slot {
            k: RefTarget::absent(),
            ..slot(Ref::Origin)
        },
    }
}

/// The model's machines, one for each ref, keeping the bookmark `y` the same in `Y`'s and
/// `Origin`'s.
#[derive(Clone, Debug)]
pub(super) struct Model([Machine; 4]);

impl Model {
    pub(super) fn new(machines: [Machine; 4]) -> Self {
        Self(machines)
    }

    pub(super) fn get(&self, r: Ref) -> &Machine {
        &self.0[r as usize]
    }

    pub(super) fn at(&mut self, r: Ref) -> &mut Machine {
        &mut self.0[r as usize]
    }

    /// `set` on the bookmark's refs, as jj's `set_local_bookmark_target`.
    pub(super) fn set(&mut self, alg: &Alg, bookmark: Ref, l: RefTarget) {
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
    pub(super) fn bookmark_set(&mut self, alg: &Alg, bookmark: Ref, l: RefTarget) {
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
    pub(super) fn realize(&mut self, canonical: &SharedRefs) {
        let SharedRefs { x, tag, origin } = canonical;
        self.at(Ref::X).v.l = x.clone();
        self.at(Ref::T).v.l = tag.clone();
        self.at(Ref::Y).v.l = origin.l.clone();
        let v = &mut self.at(Ref::Origin).v;
        v.l = origin.l.clone();
        v.r = origin.r.clone();
        v.tr = origin.tr;
    }

    pub(super) fn shared(&self) -> SharedRefs {
        shared(|r| self.get(r).v.clone())
    }

    /// `jj undo` or `jj op restore` to an operation whose view is `view`: each ref's slot as
    /// there, but `K`, as `view_with_desired_portions_restored` in jj-cli restores it, then
    /// jj's export. Where that leaves a record that doesn't match `.git`, the ghost
    /// `restored`, which only an unrestorable slot may set.
    pub(super) fn restore(&mut self, alg: &Alg, view: &View) {
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
    pub(super) fn merge(alg: &Alg, base: &Self, first: &Self, second: &Self) -> [Slot; 4] {
        Ref::ALL.map(|r| {
            alg.lean()
                .merge_slots(&base.get(r).v, &first.get(r).v, &second.get(r).v)
        })
    }

    pub(super) fn slots(&self) -> Vec<Slot> {
        self.0.iter().map(|m| m.v.clone()).collect()
    }

    /// jj's import of `refs`, in its order, each a `jjImport` and a `set` of the others with
    /// the bookmark.
    pub(super) fn import(&mut self, alg: &Alg, refs: &[Ref]) {
        for &r in refs {
            // Since jj's 095c1ca, unchanged physical refs do not update remote bookmarks.
            if self.get(r).g != self.get(r).v.k {
                self.import_ref(alg, r);
            }
        }
    }

    /// A fetch imports its explicit result even if the physical ref did not change.
    pub(super) fn import_ref(&mut self, alg: &Alg, r: Ref) {
        if self.at(r).jj_import(alg) {
            let l = self.at(r).v.l.clone();
            self.set(alg, r, l);
        }
    }

    /// Once the record is back, as a realization's export can put it, the invariant holds
    /// again in full, and a restore's allowance (`restored`) ends.
    pub(super) fn forget_restored_where_the_record_is_back(&mut self, alg: &Alg) {
        for r in Ref::ALL {
            if self.get(r).strict_inv(alg, r) {
                self.at(r).restored = false;
            }
        }
    }

    /// jj's export of every ref, `x`'s update failing if `x_locked`, then, if `musubi`
    /// exports, its export of a conflicted `y@origin`.
    pub(super) fn export(&mut self, alg: &Alg, x_locked: bool, musubi: bool) {
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
    pub(super) fn export_beside(&mut self, alg: &Alg, x_locked: bool, head: &Self) {
        self.export(alg, x_locked, false);
        let k = &head.get(Ref::Origin).v.k;
        self.at(Ref::Origin).export_conflicted_beside(alg, k);
    }

    /// Whether every local bookmark's record agrees with itself, as `LStep.beside` needs of the
    /// operation a realization beside the op head descends from (`LStep.agrees`).
    pub(super) fn records_agree(&self) -> bool {
        [Ref::X, Ref::Y, Ref::T].iter().all(|&r| {
            let v = &self.get(r).v;
            v.r == v.k
        })
    }

    /// A head `jj` command imports, then exports even when importing changed
    /// nothing. Its own transaction, `change`, exports only if that changed the view.
    pub(super) fn jj(&mut self, alg: &Alg, change: impl FnOnce(&mut Self)) {
        self.import(alg, &Ref::ALL);
        self.export(alg, false, false);
        let before = self.slots();
        change(self);
        if self.slots() != before {
            self.export(alg, false, false);
        }
    }
}

/// The expected value of `y@origin` in `model`, if it is conflicted.
pub(super) fn conflicted_expected(model: &Model) -> Option<RefTarget> {
    let origin = model.get(Ref::Origin);
    (!Alg::resolved(&origin.v.r)).then(|| origin.e.clone())
}

/// The expected value of `y@origin` at `r`, a merge of `heads`, in that order if
/// `in_order`: the remote bookmark if it is resolved, as where a fetch and a conflict on it
/// merge to neither, or else the first parent's with the same conflict, or the side, where
/// the merge made it.
pub(super) fn merged_expected(
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
pub(super) fn read(repo: &ReadonlyRepo, r: Ref) -> (Slot, RefTarget) {
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

pub(super) fn slot(view: &View, r: Ref) -> Slot {
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

/// The real repository is the model's: one op head, and each ref's slot and `.git` as the
/// model has them, with the model's invariant holding for each. Changes nothing.
pub(super) fn judge(repo: &ReadonlyRepo, model: &Model, alg: &Alg) {
    let heads = block_on(repo.loader().op_heads_store().get_op_heads()).unwrap();
    assert_eq!(heads.len(), 1, "op heads: {heads:?}");
    for r in Ref::ALL {
        let machine = model.get(r);
        let (v, g) = read(repo, r);
        assert_eq!(
            v, machine.v,
            "{r:?}: bookmark, remote bookmark and git_refs"
        );
        assert_eq!(g, machine.g, "{r:?}: .git's {}", r.git_ref());
        assert!(
            machine.inv(alg, r),
            "{r:?}: the model's invariant fails: {machine:?}"
        );
    }
}
