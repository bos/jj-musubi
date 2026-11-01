//! `jj op restore` back to an operation whose `y@origin` is conflicted, when it isn't now
//! (formal/Musubi/Refs.lean, `restore_import_agrees`; docs/internals/conformance.md,
//! "Per-machine refs"), with the refs and remote of `refs::hive`.

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::RefTarget;
use jj_lib::ref_name::RefName;
use jj_lib::ref_name::RemoteName;
use jj_lib::ref_name::RemoteRefSymbol;

use crate::fixture::Fixture;
use crate::refs::hive;

const HERE: usize = 0;
const THERE: usize = 1;

/// Machine `index`'s `y` and `y@origin`, read in process, so importing nothing, and its
/// `.git`'s `refs/heads/y` and `refs/remotes/origin/y`.
fn y(fixture: &Fixture, index: usize) -> (RefTarget, RefTarget, String, String) {
    let repo = fixture.load(index);
    let view = repo.view();
    let local = view.get_local_bookmark(RefName::new("y")).clone();
    let remote = view
        .get_remote_bookmark(RemoteRefSymbol {
            name: RefName::new("y"),
            remote: RemoteName::new("origin"),
        })
        .target
        .clone();
    let git = |r: &str| fixture.repo(index).git(&["rev-parse", r]).trim().to_owned();
    (
        local,
        remote,
        git("refs/heads/y"),
        git("refs/remotes/origin/y"),
    )
}

/// After concurrent fetches of `two` and `three` conflict `y@origin` (and `y`, which tracks
/// it), and musubi wrote their side `three` to both `.git`s, this machine fetches `settled`,
/// then restores the conflicted operation. jj's export skips the conflicted `y@origin`, so
/// this machine's `.git` keeps `settled`, and its next command imports it. The restore's
/// expected value is its parent's `y@origin`, `settled`, so the other machine, realizing the
/// restore, keeps `settled` in its `.git` too, rather than writing the side, and imports the
/// same (Refs.lean, `restore_import_agrees`). Then nothing is conflicted and nothing moved
/// back: `y` and `y@origin` are where the fetch put them, everywhere, `.git` included
/// (`restore_conflict_resolves_back`). Had the other machine written `three`, the hive would
/// have merged the two imports, from the conflict of `two` and `three` over `one`, to `one`.
///
/// With an [`Abandon`], this machine then abandons the fetch and what followed it up to the
/// restore, so the restore's parent is conflicted too and the rewritten history would expect
/// musubi's side, `three`. The fix-up records the expected value as it was, so both `.git`s
/// still keep `settled` (docs/internals/design.md, "The fix-up").
fn restore_a_conflicted_remote_bookmark(settled: &str, abandon: Abandon) {
    let mut f = hive();
    let origin = f.env.root().join("origin.git");
    let origin = origin.to_str().unwrap().to_owned();
    for index in [HERE, THERE] {
        f.repo(index).git(&["remote", "set-url", "origin", &origin]);
    }
    // An operation from before the conflict, for a later abandon to drop, on each machine.
    let earlier = matches!(
        abandon,
        Abandon::FetchThenAnEarlierOne | Abandon::FetchWhileTheOtherAbandons
    )
    .then(|| {
        f.repo(HERE).jj(&["new", "-m", "earlier"]);
        f.load(HERE).op_id().hex()
    });
    f.sync();
    // The other machine's realization of it, its latest operation so described.
    let earlier = earlier.map(|here| {
        let template = r#"id ++ " " ++ description ++ "\n""#;
        let log = f
            .repo(THERE)
            .jj(&["op", "log", "--no-graph", "-T", template]);
        let there = log
            .lines()
            .find_map(|line| line.strip_suffix(" new empty commit"))
            .expect("the other machine has it")
            .to_owned();
        (here, there)
    });
    let [settled, two, three] = [settled, "two", "three"].map(|m| f.commit_id(HERE, m));
    let normal = |id: &String| RefTarget::normal(CommitId::try_from_hex(id.as_str()).unwrap());
    let upstream = |f: &Fixture, id: &str| {
        f.repo(HERE)
            .git(&["--git-dir", &origin, "update-ref", "refs/heads/y", id]);
    };

    // Both fetch before either has the other's fetch.
    upstream(&f, &two);
    f.repo(HERE).jj(&["git", "fetch"]);
    upstream(&f, &three);
    f.repo(THERE).jj(&["git", "fetch"]);
    f.hive.sync(HERE).unwrap();
    f.hive.sync(THERE).unwrap();
    f.hive.sync(HERE).unwrap();
    for index in [HERE, THERE] {
        let (local, remote, _, git_remote) = y(&f, index);
        assert!(!remote.is_resolved(), "y@origin on {index}: {remote:?}");
        assert!(!local.is_resolved(), "y on {index}: {local:?}");
        assert_eq!(git_remote, three, "musubi's side in {index}'s .git");
    }
    let conflicted = f.load(HERE).op_id().hex();

    // This machine fetches `settled`, resolving both.
    upstream(&f, &settled);
    f.repo(HERE).jj(&["git", "fetch"]);
    let fetch = f.load(HERE).op_id().hex();
    f.sync();
    let synced = (
        normal(&settled),
        normal(&settled),
        settled.clone(),
        settled.clone(),
    );
    for index in [HERE, THERE] {
        assert_eq!(y(&f, index), synced, "after the fetch on {index}");
    }

    // The restore, which the other machine realizes before either runs `jj` again.
    f.repo(HERE).jj(&["op", "restore", &conflicted]);
    let restore = f.load(HERE).op_id().hex();
    // Importing nothing, so that `.git` decides what the next command imports.
    let abandon_op = |f: &Fixture, index: usize, ops: &str| {
        f.repo(index)
            .jj(&["--ignore-working-copy", "op", "abandon", ops])
    };
    if matches!(
        abandon,
        Abandon::FetchUnderTheOthersWork | Abandon::FetchWhileTheOtherAbandons
    ) {
        // Both have the restore, and this machine keeps it, abandoning the operations from
        // the fetch up to it.
        f.hive.sync(HERE).unwrap();
        f.hive.sync(THERE).unwrap();
        abandon_op(&f, HERE, &format!("{fetch}-..{restore}-"));
    }
    if abandon == Abandon::FetchWhileTheOtherAbandons {
        // The other machine's fix-up records the same expected value, since it has the
        // restore. So this machine makes a new operation, older than that fix-up, so that
        // the merge of the two goes first to this machine's side, where only its own
        // fix-up's values say what the history before the abandon expected.
        f.repo(HERE)
            .jj(&["--ignore-working-copy", "new", "-m", "later"]);
    } else if abandon == Abandon::FetchUnderTheOthersWork {
        // On the restore, which this machine then realizes on its rewrite, exporting before
        // its fix-up is written.
        f.repo(THERE)
            .jj(&["--ignore-working-copy", "new", "-m", "there"]);
        f.hive.sync(THERE).unwrap();
    } else if abandon > Abandon::Nothing {
        abandon_op(&f, HERE, &format!("{fetch}-..@-"));
    }
    match (abandon, &earlier) {
        (Abandon::FetchThenAnEarlierOne, Some((here, _))) => {
            // musubi notices the first abandon, as a sync does first, then jj rewrites again
            // what it rewrote, before the fix-up is written.
            assert!(f.node(HERE).check_abandon().unwrap());
            abandon_op(&f, HERE, here);
        }
        (Abandon::FetchWhileTheOtherAbandons, Some((_, there))) => {
            // The hub takes the other machine's record first, so this machine takes it, which
            // rewrites what it rewrote, before it writes its fix-up.
            abandon_op(&f, THERE, there);
            f.hive.sync(THERE).unwrap();
        }
        _ => {}
    }
    f.hive.sync(HERE).unwrap();
    f.hive.sync(THERE).unwrap();
    for index in [HERE, THERE] {
        let (local, remote, git_local, git_remote) = y(&f, index);
        assert!(
            !remote.is_resolved(),
            "restored y@origin on {index}: {remote:?}"
        );
        assert!(!local.is_resolved(), "restored y on {index}: {local:?}");
        assert_eq!(
            (git_local, git_remote),
            (settled.clone(), settled.clone()),
            "{index}'s .git keeps the fetched y"
        );
    }

    // Each machine's next command imports the same, and nothing moves back.
    for index in [HERE, THERE] {
        f.repo(index).jj(&["status"]);
        assert_eq!(y(&f, index), synced, "imported on {index}");
    }
    f.assert_converged();
    for index in [HERE, THERE] {
        assert_eq!(y(&f, index), synced, "merged on {index}");
    }
    // `y` is `y@origin`, so `jj git push` sends nothing, and `origin` keeps `settled`.
    f.repo(HERE).jj(&["git", "push", "--bookmark", "y"]);
    let remote = f.repo(HERE).git(&["--git-dir", &origin, "rev-parse", "y"]);
    assert_eq!(remote.trim(), settled, "origin's y after jj git push");
}

/// What a test abandons after the restore, each case including the one before it.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Abandon {
    Nothing,
    /// This machine's fetch and what followed it, up to the restore.
    Fetch,
    /// The fetch and what followed it up to the restore, which both machines have, while the
    /// other machine builds on the restore and syncs first.
    FetchUnderTheOthersWork,
    /// Then, before this machine syncs, an operation from before the conflict.
    FetchThenAnEarlierOne,
    /// The fetch and what followed it up to the restore, which both machines have, while the
    /// other machine abandons an operation from before the conflict, and the hub takes that
    /// first.
    FetchWhileTheOtherAbandons,
}

/// The fetch settles on a commit that is no term of the conflict.
#[test]
fn restoring_a_conflicted_remote_bookmark_keeps_the_fetched_value() {
    restore_a_conflicted_remote_bookmark("base", Abandon::Nothing);
}

/// The fetch settles on a term of the conflict, its base or the side musubi didn't write:
/// a value the hive knows of, which musubi would replace, were the expected value not that
/// value itself.
#[test]
fn restoring_a_conflicted_remote_bookmark_keeps_a_fetched_term() {
    restore_a_conflicted_remote_bookmark("one", Abandon::Nothing);
    restore_a_conflicted_remote_bookmark("two", Abandon::Nothing);
}

/// The fetch settles on the side musubi didn't write, and the abandon would have every
/// machine write the other side, which the next command would import.
#[test]
fn abandoning_the_fetch_under_a_restore_keeps_the_fetched_term() {
    restore_a_conflicted_remote_bookmark("two", Abandon::Fetch);
}

/// So too where the other machine builds on the restore before this machine syncs, which
/// then realizes that on its rewrite of the restore, before it writes its fix-up.
#[test]
fn realizing_work_on_the_restore_before_the_fix_up_keeps_the_fetched_term() {
    restore_a_conflicted_remote_bookmark("two", Abandon::FetchUnderTheOthersWork);
}

/// So too where this machine abandons again before its fix-up is written: jj rewrites the
/// operation the fix-up's expected values were worked out at.
#[test]
fn abandoning_again_before_the_fix_up_keeps_the_fetched_term() {
    restore_a_conflicted_remote_bookmark("two", Abandon::FetchThenAnEarlierOne);
}

/// So too where this machine takes the other machine's abandon before it writes its fix-up,
/// rewriting the operation its fix-up's expected values were worked out at as the other
/// machine's record says.
#[test]
fn taking_another_abandon_before_the_fix_up_keeps_the_fetched_term() {
    restore_a_conflicted_remote_bookmark("two", Abandon::FetchWhileTheOtherAbandons);
}
