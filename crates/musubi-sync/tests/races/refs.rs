//! Bookmarks in a colocated repository, against `formal/Musubi/Refs.lean`
//! (docs/internals/conformance.md, "Per-machine refs"). Hegel moves refs with git, runs
//! `jj` commands, fetches, and has another machine move bookmarks for musubi to realize here,
//! its export succeeding or failing. Beside the real machine it keeps the model's `Machine`
//! for each ref it follows, with jj's own `merge_ref_targets` as the model's merge
//! (`ref_laws` checks that it obeys the laws the model assumes), and steps each as the
//! model's `LStep`s or `RStep`s that the real action performs. After every action each
//! bookmark, its remote bookmark, jj's record of the git ref, and the git ref itself must be
//! the model's, and the model's invariants `LInv` and `RInv` must hold.
//!
//! The refs are a local bookmark `x`, which git moves; a local bookmark `y`, which git
//! doesn't; and `y@origin`, which `y` tracks, which git moves and fetches move. The model has
//! one ref per machine; here `y` and `y@origin` share the bookmark `y`, so a step of one is a
//! `set` of the other.

use std::path::PathBuf;
use std::sync::Arc;

use futures::executor::block_on;
use hegel::HealthCheck;
use hegel::TestCase;
use hegel::generators as gs;
use jj_lib::backend::CommitId;
use jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::RefTarget;
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
}

impl Ref {
    const ALL: [Self; 3] = [Self::X, Self::Y, Self::Origin];

    fn bookmark(self) -> &'static str {
        match self {
            Self::X => "x",
            Self::Y | Self::Origin => "y",
        }
    }

    fn remote(self) -> &'static RemoteName {
        match self {
            Self::X | Self::Y => REMOTE_NAME_FOR_LOCAL_GIT_REPO,
            Self::Origin => RemoteName::new("origin"),
        }
    }

    fn git_ref(self) -> &'static str {
        match self {
            Self::X => "refs/heads/x",
            Self::Y => "refs/heads/y",
            Self::Origin => "refs/remotes/origin/y",
        }
    }
}

/// The model's `Slot`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Slot {
    l: RefTarget,
    r: RefTarget,
    k: RefTarget,
}

/// The model's `Machine`: the view's slot, `.git`'s ref, and the ghost `moved`.
#[derive(Clone, Debug)]
struct Machine {
    v: Slot,
    g: RefTarget,
    moved: bool,
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
}

impl Slot {
    /// `Slot.import`.
    fn import(&self, alg: &Alg, g: &RefTarget) -> Self {
        Self {
            l: if *g == self.r {
                self.l.clone()
            } else {
                alg.merge(&self.l, &self.r, g)
            },
            r: g.clone(),
            k: g.clone(),
        }
    }
}

impl Machine {
    /// `LStep.gitMove` and `RStep.gitMove`.
    fn git_move(&mut self, g: RefTarget) {
        self.g = g;
        self.moved = true;
    }

    /// `LStep.jjImport` and `RStep.jjImport`.
    fn jj_import(&mut self, alg: &Alg) {
        self.v = self.v.import(alg, &self.g);
        self.moved = false;
    }

    /// `LStep.jjExport`, `exportLocal`, where the update of `.git` can succeed; where it
    /// can't, because `.git` is locked, no step, as the model has a failed update. An update
    /// to the value `.git` already has writes nothing, so succeeds.
    fn export_local(&mut self, alg: &Alg, git_writable: bool) {
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

    /// `LInv`.
    fn local_inv(&self) -> bool {
        self.moved || (self.v.r == self.g && self.v.k == self.g)
    }

    /// `RInv`.
    fn remote_inv(&self) -> bool {
        Alg::resolved(&self.g) && self.local_inv()
    }
}

/// The model's machines, one for each ref, keeping the bookmark `y` the same in `Y`'s and
/// `Origin`'s.
#[derive(Clone, Debug)]
struct Model([Machine; 3]);

impl Model {
    fn get(&self, r: Ref) -> &Machine {
        &self.0[r as usize]
    }

    fn at(&mut self, r: Ref) -> &mut Machine {
        &mut self.0[r as usize]
    }

    /// `set` on the bookmark's refs.
    fn set(&mut self, bookmark: Ref, l: RefTarget) {
        for r in Ref::ALL {
            if r.bookmark() == bookmark.bookmark() {
                self.at(r).v.l = l.clone();
            }
        }
    }

    fn slots(&self) -> Vec<Slot> {
        self.0.iter().map(|m| m.v.clone()).collect()
    }

    /// jj's import of `refs`, in its order, each a `jjImport` and a `set` of the others with
    /// the bookmark. Returns whether it changed the view.
    fn import(&mut self, alg: &Alg, refs: &[Ref]) -> bool {
        let before = self.slots();
        for &r in refs {
            self.at(r).jj_import(alg);
            let l = self.at(r).v.l.clone();
            self.set(r, l);
        }
        self.slots() != before
    }

    /// jj's export of every ref, `x`'s update failing if `x_locked`.
    fn export(&mut self, alg: &Alg, x_locked: bool) {
        self.at(Ref::X).export_local(alg, !x_locked);
        self.at(Ref::Y).export_local(alg, true);
        self.at(Ref::Origin).export_remote(alg);
    }

    /// A `jj` command: an import, exported if it changed the view, since jj exports only a
    /// transaction with changes, then the command's own transaction, `change`, exported if it
    /// changed the view.
    fn jj(&mut self, alg: &Alg, change: impl FnOnce(&mut Self)) {
        if self.import(alg, &Ref::ALL) {
            self.export(alg, false);
        }
        let before = self.slots();
        change(self);
        if self.slots() != before {
            self.export(alg, false);
        }
    }
}

/// The repository the machines start from: `base`, `one` and `two` in a line, `three`
/// beside them, each kept visible by a bookmark of its own, and `x`, `y` and `y@origin`, which
/// `y` tracks, at `one`. Both machines track `y@origin` automatically, as the model assumes:
/// without it, jj forgets that `y` tracks `y@origin` once both are gone, and merges nothing
/// into `y` when `y@origin` comes back (docs/internals/conformance.md, "Per-machine refs").
fn hive() -> Fixture {
    Fixture::recorded(&["alpha", "beta"], "refs", |hive| {
        let origin = hive.env.root().join("origin.git");
        let repo = hive.repo(HERE);
        repo.jj(&["new", "-m", "base"]);
        repo.jj(&["new", "-m", "one"]);
        repo.jj(&["new", "-m", "two"]);
        repo.jj(&["bookmark", "create", "keep-two", "-r", "@"]);
        repo.jj(&["bookmark", "create", "x", "-r", "@-"]);
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
            Machine { v, g, moved: false }
        }));
        let refs = Self {
            fixture,
            alg: Alg { repo },
            model,
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
    fn check(&self) {
        let repo = self.fixture.load(HERE);
        let heads = block_on(repo.loader().op_heads_store().get_op_heads()).unwrap();
        assert_eq!(heads.len(), 1, "op heads: {heads:?}");
        for r in Ref::ALL {
            let model = self.model.get(r);
            let (v, g) = read(&repo, r);
            assert_eq!(v, model.v, "{r:?}: bookmark, remote bookmark and git_refs");
            assert_eq!(g, model.g, "{r:?}: .git's {}", r.git_ref());
            let inv = match r {
                Ref::X | Ref::Y => model.local_inv(),
                Ref::Origin => model.remote_inv(),
            };
            assert!(inv, "{r:?}: the model's invariant fails: {model:?}");
        }
    }

    /// Has machine `index` move `bookmark` to `l` with a `jj` command, or if `l` is where
    /// it is, run a `jj` command that changes nothing.
    fn jj_set(&self, index: usize, bookmark: Ref, l: &RefTarget, current: &RefTarget) {
        let repo = self.fixture.repo(index);
        if l == current {
            repo.jj(&["status"]);
        } else if let Some(id) = l.as_normal() {
            let rev = if id == &self.commits[0] {
                "root()".to_owned()
            } else {
                id.hex()
            };
            repo.jj(&[
                "bookmark",
                "set",
                bookmark.bookmark(),
                "-r",
                &rev,
                "--allow-backwards",
            ]);
        } else {
            repo.jj(&["bookmark", "delete", bookmark.bookmark()]);
        }
    }

    /// `y` in `origin` moves to a new value, which it returns.
    fn push_upstream(&mut self, tc: &TestCase) -> RefTarget {
        let upstream = self.target(tc, false, &self.upstream);
        let origin = self.origin();
        let origin = origin.to_str().unwrap();
        let repo = self.fixture.repo(HERE);
        match upstream.as_normal() {
            Some(id) => repo.git(&["--git-dir", origin, "update-ref", "refs/heads/y", &id.hex()]),
            None => repo.git(&["--git-dir", origin, "update-ref", "-d", "refs/heads/y"]),
        };
        self.upstream = upstream.clone();
        upstream
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
    let local = view.local_bookmarks.get(name).cloned();
    let remote = view
        .remote_views
        .get(r.remote())
        .and_then(|remote| remote.bookmarks.get(name))
        .map(|remote| remote.target.clone());
    Slot {
        l: local.unwrap_or_else(RefTarget::absent),
        r: remote.unwrap_or_else(RefTarget::absent),
        k: view
            .git_refs
            .get(GitRefName::new(r.git_ref()))
            .cloned()
            .unwrap_or_else(RefTarget::absent),
    }
}

#[hegel::state_machine]
impl Refs {
    /// `git update-ref` moves or deletes `refs/heads/x` or `refs/remotes/origin/y`:
    /// `LStep.gitMove` or `RStep.gitMove`.
    #[rule(weight = 2)]
    fn git_moves(&mut self, tc: TestCase) {
        let r = if tc.draw(gs::booleans()) {
            Ref::X
        } else {
            Ref::Origin
        };
        let g = self.target(&tc, false, &self.model.get(r).g);
        let repo = self.fixture.repo(HERE);
        match g.as_normal() {
            Some(id) => repo.git(&["update-ref", r.git_ref(), &id.hex()]),
            None => repo.git(&["update-ref", "-d", r.git_ref()]),
        };
        self.model.at(r).git_move(g);
        self.check();
    }

    /// A `jj` command that moves `x` or `y`, or changes nothing (`Model::jj`).
    #[rule]
    fn jj_runs(&mut self, tc: TestCase) {
        let bookmark = if tc.draw(gs::booleans()) {
            Ref::X
        } else {
            Ref::Y
        };
        let moves = tc.draw(gs::booleans());
        // The bookmark as the command sees it, once it has imported.
        let mut imported = self.model.clone();
        imported.import(&self.alg, &Ref::ALL);
        let current = imported.at(bookmark).v.l.clone();
        let l = if moves {
            self.target(&tc, true, &current)
        } else {
            current.clone()
        };
        self.jj_set(HERE, bookmark, &l, &current);
        self.model.jj(&self.alg, |model| model.set(bookmark, l));
        self.check();
    }

    /// `y` moves in `origin`, and `jj git fetch` fetches it: a `jj` command whose change is
    /// `RStep.fetch`.
    #[rule]
    fn jj_fetches(&mut self, tc: TestCase) {
        let upstream = self.push_upstream(&tc);
        self.fixture.repo(HERE).jj(&["git", "fetch"]);
        self.model.jj(&self.alg, |model| {
            model.at(Ref::Origin).g = upstream;
            model.import(&self.alg, &[Ref::Origin]);
        });
        self.check();
    }

    /// The other machine moves `x`, or fetches `y` after it moved in `origin`, and both
    /// sync, the update of `x` failing while git's lock on `refs/heads/x` is held: an
    /// `advance` of each ref, and the export.
    #[rule(weight = 2)]
    fn musubi_realizes(&mut self, tc: TestCase) {
        let fetch = tc.draw(gs::booleans());
        let locked = tc.draw(gs::booleans());
        // Both up to date, so that what this machine realizes follows its op head.
        self.fixture.hive.sync(HERE).unwrap();
        self.fixture.hive.sync(THERE).unwrap();
        let moved_to = if fetch {
            self.push_upstream(&tc);
            self.fixture.repo(THERE).jj(&["git", "fetch"]);
            None
        } else {
            // The other machine's `x` is this one's, which it had from the hive.
            let current = self.model.at(Ref::X).v.l.clone();
            let c = self.target(&tc, true, &current);
            self.jj_set(THERE, Ref::X, &c, &current);
            Some(c)
        };
        // What the other machine's operations leave in the hive, the shared fields of its
        // view, are what this machine's model says the other's command made of them: the
        // other machine's own refs changed nothing.
        let there = self.fixture.load(THERE);
        let x = slot(there.view().store_view(), Ref::X);
        let origin = slot(there.view().store_view(), Ref::Origin);
        let mut expected = self.model.clone();
        match moved_to {
            None => {
                let theirs = expected.at(Ref::Origin).v.import(&self.alg, &self.upstream);
                expected.set(Ref::Y, theirs.l);
                expected.at(Ref::Origin).v.r = theirs.r;
            }
            Some(c) => expected.at(Ref::X).v.l = c,
        }
        assert_eq!(
            (&x.l, &origin.l, &origin.r),
            (
                &expected.get(Ref::X).v.l,
                &expected.get(Ref::Origin).v.l,
                &expected.get(Ref::Origin).v.r
            ),
            "the other machine's x, y and y@origin"
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
        // `LStep.advance` for `x` and `y`, and `RStep.advance` for `y@origin`, then the
        // export, if there was anything to realize: a fetch that brings nothing new makes no
        // operation.
        if expected.slots() != self.model.slots() {
            // `RStep.advance`'s precondition, which offering no root commit keeps.
            let g = self.model.at(Ref::Origin).g.clone();
            assert!(origin.r == g || self.alg.writable(&origin.r));
            self.model.at(Ref::X).v.l = x.l;
            self.model.set(Ref::Y, origin.l);
            self.model.at(Ref::Origin).v.r = origin.r;
            self.model.export(&self.alg, locked);
        }
        self.check();
    }
}

#[hegel::test(test_cases = refs_cases(), suppress_health_check = [HealthCheck::TooSlow])]
fn bookmarks_conform_to_refs_model(tc: TestCase) {
    hegel::stateful::machine(Refs::new()).steps(10).run(tc);
}

/// How many cases to make: `MUSUBI_CONFORMANCE_CASES`, as for the other conformance tests,
/// or 12, each a few tenths of a second of real `jj`, `git` and syncs.
fn refs_cases() -> u64 {
    std::env::var("MUSUBI_CONFORMANCE_CASES")
        .ok()
        .and_then(|cases| cases.parse().ok())
        .unwrap_or(12)
}
