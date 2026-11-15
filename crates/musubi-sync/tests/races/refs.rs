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
use std::path::PathBuf;

use futures::executor::block_on;
use hegel::TestCase;
use hegel::generators as gs;
use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::RefTarget;
use jj_lib::ref_name::RefName;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;

use crate::fixture::Fixture;
use crate::refs_model::RefsModel;

mod abandon;
mod examples;
mod model;
mod scenario;

use model::*;
use scenario::*;

/// The machine whose refs are checked, and the other machine, which moves bookmarks.
const HERE: usize = 0;
const THERE: usize = 1;

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
            // Each machine configures its own Git access; syncing only carries bookmarks.
            hive.repo(index)
                .jj(&["git", "remote", "add", "origin", origin.to_str().unwrap()]);
        }
        repo.jj(&["git", "fetch"]);
        hive.sync();
    })
}

/// A model snapshot paired with the native operation whose refs it predicts.
#[derive(Clone)]
struct ModelAtOperation {
    op: OperationId,
    model: Model,
}

/// The commits the fixture's bookmarks name, as targets: the root; `base`, `one` and `two`, each
/// the one before's child; and `three`, another child of `base`, which a bookmark of its own
/// keeps visible.
#[derive(Clone)]
struct Commits {
    root: RefTarget,
    base: RefTarget,
    one: RefTarget,
    two: RefTarget,
    three: RefTarget,
}

/// A target for a ref to move to, which a failure prints by name, not as a commit id.
#[derive(Clone, Copy, Debug)]
enum Target {
    Absent,
    Root,
    Base,
    One,
    Two,
    Three,
}

impl Commits {
    fn get(&self, target: Target) -> RefTarget {
        match target {
            Target::Absent => RefTarget::absent(),
            Target::Root => self.root.clone(),
            Target::Base => self.base.clone(),
            Target::One => self.one.clone(),
            Target::Two => self.two.clone(),
            Target::Three => self.three.clone(),
        }
    }
}

struct Refs {
    fixture: Fixture,
    alg: Alg,
    model: Model,
    /// The op head after the latest action, and the model then.
    latest: ModelAtOperation,
    /// The op head and the model before the latest action, for a `jj` command at that
    /// operation.
    older: ModelAtOperation,
    /// This machine's op head and model when both machines last synced, where the other
    /// machine's operations start.
    synced: ModelAtOperation,
    commits: Commits,
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
        let normal = |id: &CommitId| RefTarget::normal(id.clone());
        let commits = Commits {
            root: normal(repo.store().root_commit_id()),
            base: normal(&base),
            one: normal(&one),
            two: normal(&two),
            three: normal(&commit("keep-three")),
        };
        let model = Model::new(Ref::ALL.map(|r| {
            let (v, g) = read(&repo, r);
            Machine {
                e: g.clone(),
                v,
                g,
                moved: false,
                restored: false,
            }
        }));
        let head = ModelAtOperation {
            op: repo.op_id().clone(),
            model: model.clone(),
        };
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
            upstream: commits.one.clone(),
            commits,
        };
        refs.check();
        refs
    }

    /// A target other than `not`, the value it would replace, so that every action changes
    /// something: absent, or one of the commits, the root among them if `root`.
    #[hegel::test_helper]
    fn target(&self, tc: &TestCase, root: bool, not: &RefTarget) -> RefTarget {
        let places = [
            Target::Root,
            Target::Base,
            Target::One,
            Target::Two,
            Target::Three,
            Target::Absent,
        ];
        let choices: Vec<Target> = places[usize::from(!root)..]
            .iter()
            .copied()
            .filter(|&place| &self.commits.get(place) != not)
            .collect();
        let target = tc.draw(gs::sampled_from(choices));
        self.commits.get(target)
    }

    /// The real state is the model's, and the model's invariants hold. Then the snapshots
    /// the next actions refer to move on.
    fn check(&mut self) {
        let repo = self.fixture.load(HERE);
        judge(&repo, &self.model, &self.alg);
        self.rotate_snapshots(&repo);
        self.model
            .forget_restored_where_the_record_is_back(&self.alg);
    }

    /// `latest` becomes the model at the head, and what it was becomes `older`, the
    /// operation a `jj` command at an older operation runs at.
    fn rotate_snapshots(&mut self, repo: &ReadonlyRepo) {
        let latest = ModelAtOperation {
            op: repo.op_id().clone(),
            model: self.model.clone(),
        };
        self.older = std::mem::replace(&mut self.latest, latest);
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
            let rev = if l == &self.commits.root {
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

    /// A `jj` command at an explicit operation id (`--at-op`) moves `bookmark` to `l`,
    /// which must be somewhere else there. It neither imports nor exports Git refs. The
    /// next head command merges its operation with the head against the older operation,
    /// as `TSlot.merge`, then imports and exports. If the latest action made no operation,
    /// the command's operation is simply the next.
    fn jj_sets_at_older_op(&mut self, bookmark: Ref, l: RefTarget) {
        let ModelAtOperation {
            op: old,
            model: base,
        } = self.older.clone();
        let head = self.head();
        let current = base.get(bookmark).v.l.clone();
        assert_ne!(l, current);
        self.jj_set(HERE, bookmark, &l, &current, Some(&old));
        let mut theirs = base.clone();
        for r in Ref::ALL {
            theirs.at(r).g = self.model.get(r).g.clone();
        }
        theirs.bookmark_set(&self.alg, bookmark, l);
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

    /// Publish the other machine's command, realize it here, and compare both machines with
    /// the model. Concurrent work is merged as jj merges it (`realizeMerge_eq`); a local
    /// command before realization adds `LStep.beside` and `CStep.beside`. Git may hold `x`'s
    /// lock during realization, and conflicted `y@origin` must have the same expected value
    /// on both machines, whatever the command and ordering.
    fn musubi_realizes_with(&mut self, scenario: Realization) {
        let history = self.realization_base(scenario.order);
        let peer = self.peer_command(&history.model, scenario.command);

        // This machine as of `ours`, which the realization descends from.
        let at_ours = self.model.clone();
        match scenario.beside {
            Some(RefCommand::Sets(r, l)) => self.jj_sets(r, l),
            Some(RefCommand::Fetches(upstream)) => self.jj_fetches_from(upstream),
            None => {}
        }
        let mine = self.head();
        let beside = mine != history.ours;
        self.sync_realization(scenario.export);

        // A fetch that brings nothing new makes no operation to realize.
        if peer.expected.shared() != history.model.shared() {
            let realized = self.predict_realization(
                &history,
                &peer.canonical,
                &at_ours,
                &mine,
                scenario.export,
            );
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
            self.model
                .export(&self.alg, scenario.export.x_locked(), true);
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
        self.synced = ModelAtOperation {
            op: self.head(),
            model: self.model.clone(),
        };
    }

    /// Publish this machine's work first. A following peer takes it before acting; a
    /// concurrent peer keeps the common history from the preceding sync.
    fn realization_base(&mut self, order: PeerOrder) -> RealizationBase {
        self.fixture.hive.sync(HERE).unwrap();
        if order == PeerOrder::Following {
            self.fixture.hive.sync(THERE).unwrap();
            self.synced = ModelAtOperation {
                op: self.head(),
                model: self.model.clone(),
            };
        }
        let ModelAtOperation {
            op: synced_op,
            model,
        } = self.synced.clone();
        RealizationBase {
            synced_op,
            model,
            ours: self.head(),
        }
    }

    /// Predict a command from the other machine's own import/export records and physical
    /// refs, then check its native result before publishing it. A pending git move here can
    /// leave our record behind even when both machines have the same shared fields.
    fn peer_command(&mut self, base: &Model, command: RefCommand) -> PeerResult {
        let there = self.fixture.load(THERE);
        assert_eq!(
            shared(|r| slot(there.view().store_view(), r)),
            base.shared()
        );
        let mut expected = base.clone();
        for r in Ref::ALL {
            let (v, g) = read(&there, r);
            let m = expected.at(r);
            (m.v, m.g) = (v, g);
        }
        expected.jj(&self.alg, |model| match &command {
            RefCommand::Fetches(upstream) => {
                model.at(Ref::Origin).g = upstream.clone();
                model.import_ref(&self.alg, Ref::Origin);
            }
            RefCommand::Sets(r, c) if *c != base.get(*r).v.l => {
                model.bookmark_set(&self.alg, *r, c.clone());
            }
            RefCommand::Sets(_, _) => {}
        });
        match command {
            RefCommand::Fetches(upstream) => {
                self.push_upstream(upstream);
                self.fixture.repo(THERE).jj(&["git", "fetch"]);
            }
            RefCommand::Sets(r, c) => {
                let current = base.get(r).v.l.clone();
                self.jj_set(THERE, r, &c, &current, None);
            }
        }
        let there = self.fixture.load(THERE);
        let view = there.view().store_view();
        let canonical = shared(|r| slot(view, r));
        for r in Ref::ALL {
            let m = expected.get(r);
            assert_eq!(
                read(&there, r),
                (m.v.clone(), m.g.clone()),
                "the other machine's {r:?} after its command"
            );
        }
        assert_eq!(
            canonical,
            expected.shared(),
            "the other machine's x, t, y and y@origin"
        );
        self.fixture.hive.sync(THERE).unwrap();
        PeerResult {
            expected,
            canonical,
        }
    }

    /// Take the published work with the selected physical export condition.
    fn sync_realization(&mut self, export: GitExport) {
        let lock = self
            .fixture
            .repo(HERE)
            .path()
            .join(".git/refs/heads/x.lock");
        if export.x_locked() {
            std::fs::create_dir_all(lock.parent().unwrap()).unwrap();
            std::fs::write(&lock, "").unwrap();
        }
        self.fixture.hive.sync(HERE).unwrap();
        if export.x_locked() {
            std::fs::remove_file(&lock).unwrap();
        }
    }

    /// `LStep.advance` and `CStep.advance`, followed by export; with a command here,
    /// `LStep.beside` and `CStep.beside`. Actual native merge parents determine both orders.
    fn predict_realization(
        &self,
        history: &RealizationBase,
        canonical: &SharedRefs,
        at_ours: &Model,
        mine: &OperationId,
        export: GitExport,
    ) -> Model {
        let ours = &history.ours;
        let beside = mine != ours;
        let locked = export.x_locked();
        // The realization, from this machine's refs as of `ours`, against `.git` as it is.
        let mut realized = at_ours.clone();
        for r in Ref::ALL {
            realized.at(r).g = self.model.get(r).g.clone();
        }
        if history.ours == history.synced_op {
            // The other machine's operations follow on from this machine's head, so a
            // conflict they keep has the head's expected value.
            let e = at_ours.get(Ref::Origin).expected();
            realized.realize(canonical);
            realized.at(Ref::Origin).e = e;
        } else {
            // Theirs is realized here from the base, its record the base's, and merged
            // with ours as the other machine merged them.
            let mut theirs = history.model.clone();
            theirs.realize(canonical);
            let parents = if beside {
                let merge = self.merge_parents();
                let realization = merge.iter().find(|&op| op != mine).unwrap();
                self.parents(realization)
            } else {
                self.merge_parents()
            };
            assert!(
                parents.contains(&history.ours),
                "merged {parents:?}, not ours {ours:?}"
            );
            let merged = if parents[0] == history.ours {
                Model::merge(&self.alg, &history.model, at_ours, &theirs)
            } else {
                Model::merge(&self.alg, &history.model, &theirs, at_ours)
            };
            let e = merged_expected(
                |r| self.alg.side(r),
                &merged[Ref::Origin as usize].r,
                [at_ours, &theirs].map(|m| m.get(Ref::Origin)),
                parents[0] == history.ours,
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
                parents.contains(mine),
                "merged {parents:?}, not the command's {mine:?}"
            );
            let merged = if &parents[0] == mine {
                Model::merge(&self.alg, at_ours, &self.model, &realized)
            } else {
                Model::merge(&self.alg, at_ours, &realized, &self.model)
            };
            let e = merged_expected(
                |r| self.alg.side(r),
                &merged[Ref::Origin as usize].r,
                [&self.model, &realized].map(|m| m.get(Ref::Origin)),
                &parents[0] == mine,
            );
            for (r, v) in Ref::ALL.into_iter().zip(merged) {
                realized.at(r).v = v;
            }
            realized.at(Ref::Origin).e = e;
        }
        realized
    }

    /// `jj undo`, or if `target`, `jj op restore` to it: as a `jj` command that changes
    /// nothing: its import, then its export, which writes what an earlier export left undone,
    /// before anything is restored; then `Model::restore` of the operation it restores, read
    /// from its description, if it made one. Where the import or export made an operation,
    /// `jj undo` undoes that one; otherwise jj refuses to undo a merge operation, or one made
    /// in another workspace.
    fn jj_restores_to(&mut self, target: Option<OperationId>) {
        let before = self.head();
        let repo = self.fixture.repo(HERE);
        let output = match &target {
            None => repo.jj_output(&["undo"]),
            Some(op) => repo.jj_output(&["op", "restore", &op.hex()]),
        };
        self.model.jj(&self.alg, |_| {});
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
            // jj makes no restore if the restored view is the current one, as when the
            // operation undone changed only `git_refs`, which a restore keeps, though the
            // import or export before it may have made an operation.
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
        // False, a command that changes nothing, is the ordinary case Hegel shrinks to.
        let moves = tc.draw(gs::booleans());
        let l = if moves {
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
        let current = self.older.model.get(bookmark).v.l.clone();
        let l = self.target(&tc, true, &current);
        self.jj_sets_at_older_op(bookmark, l);
    }

    /// `jj undo`, or `jj op restore` to the operation before the latest action or to the one
    /// both machines last synced at.
    #[rule]
    fn jj_restores(&mut self, tc: TestCase) {
        let restore = tc.draw(gs::sampled_from(vec![
            Restore::Undo,
            Restore::ToOlder,
            Restore::ToSynced,
        ]));
        let target = match restore {
            Restore::Undo => None,
            Restore::ToOlder => Some(self.older.op.clone()),
            Restore::ToSynced => Some(self.synced.op.clone()),
        };
        self.jj_restores_to(target);
    }

    /// `y` moves in `origin`, and `jj git fetch` fetches it.
    #[rule]
    fn jj_fetches(&mut self, tc: TestCase) {
        let upstream = self.target(&tc, false, &self.upstream);
        self.jj_fetches_from(upstream);
    }

    /// The other machine moves `x` or `t`, with or without this machine's latest operations,
    /// and both sync (`musubi_realizes_with`).
    #[rule]
    fn musubi_realizes_a_move(&mut self, tc: TestCase) {
        let order = tc.draw(gs::sampled_from(vec![
            PeerOrder::Following,
            PeerOrder::Concurrent,
        ]));
        let export = tc.draw(gs::sampled_from(vec![
            GitExport::Writable,
            GitExport::XLocked,
        ]));
        let r = Ref::draw(&tc, &[Ref::X, Ref::T]);
        // The other machine's: as when they last synced, if it is behind, or else as here.
        let current = if order == PeerOrder::Concurrent {
            self.synced.model.get(r).v.l.clone()
        } else {
            self.model.get(r).v.l.clone()
        };
        let target = self.target(&tc, true, &current);
        let beside = self.beside(&tc);
        self.musubi_realizes_with(Realization {
            command: RefCommand::Sets(r, target),
            order,
            export,
            beside,
        });
    }

    /// The other machine fetches `y` after it moved in `origin`, with or without this
    /// machine's latest operations, and both sync (`musubi_realizes_with`).
    #[rule]
    fn musubi_realizes_a_fetch(&mut self, tc: TestCase) {
        let order = tc.draw(gs::sampled_from(vec![
            PeerOrder::Following,
            PeerOrder::Concurrent,
        ]));
        let export = tc.draw(gs::sampled_from(vec![
            GitExport::Writable,
            GitExport::XLocked,
        ]));
        let upstream = self.target(&tc, false, &self.upstream);
        let beside = self.beside(&tc);
        self.musubi_realizes_with(Realization {
            command: RefCommand::Fetches(upstream),
            order,
            export,
            beside,
        });
    }
}

/// What a `jj` command here, beside a realization, does.
#[derive(Clone, Copy, Debug)]
enum Beside {
    Nothing,
    /// Fetches something other than this machine has, but perhaps what the other fetched.
    Fetch,
    Set,
}

/// How `jj_restores` restores.
#[derive(Clone, Copy, Debug)]
enum Restore {
    Undo,
    /// `jj op restore` to the operation before the latest action.
    ToOlder,
    /// `jj op restore` to the operation both machines last synced at.
    ToSynced,
}

impl Refs {
    /// A `jj` command here that the realization is beside, where the records agree; half the
    /// time none.
    #[hegel::test_helper]
    fn beside(&self, tc: &TestCase) -> Option<RefCommand> {
        if !self.model.records_agree() {
            return None;
        }
        let beside = tc.draw(gs::sampled_from(vec![
            Beside::Nothing,
            Beside::Nothing,
            Beside::Fetch,
            Beside::Set,
        ]));
        match beside {
            Beside::Nothing => None,
            Beside::Fetch => {
                let origin = &self.model.get(Ref::Origin).g;
                Some(RefCommand::Fetches(self.target(tc, false, origin)))
            }
            Beside::Set => {
                let r = Ref::draw(tc, &[Ref::X, Ref::T, Ref::Y]);
                let current = self.imported(r);
                Some(RefCommand::Sets(r, self.target(tc, true, &current)))
            }
        }
    }
}

#[hegel::test(profile = "refs")]
fn bookmarks_conform_to_refs_model(tc: TestCase) {
    hegel::stateful::machine(Refs::new()).steps(10).run(tc);
}
