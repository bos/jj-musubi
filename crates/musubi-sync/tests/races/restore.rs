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

/// Concurrent fetches of `two` and `three` conflict `y@origin` and its tracking bookmark
/// `y`. After a fetch of `settled` resolves them, a restore brings back the conflict. Both
/// machines keep `settled` in the remote Git ref and its per-machine record, so ordinary
/// commands leave the remote-bookmark conflict unchanged. A further explicit fetch resolves
/// both bookmarks to `settled`.
/// The expected value kept through the restore prevents musubi from writing a different
/// physical ref on the other machine.
fn restore_a_conflicted_remote_bookmark(settled: &str) {
    let mut f = hive();
    let origin = f.env.root().join("origin.git");
    let origin = origin.to_str().unwrap().to_owned();
    for index in [HERE, THERE] {
        f.repo(index).git(&["remote", "set-url", "origin", &origin]);
    }
    f.sync();
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

    // The refs still match git_refs, so ordinary commands leave the conflicts alone.
    for index in [HERE, THERE] {
        let before = y(&f, index);
        f.repo(index).jj(&["status"]);
        let (local, remote, git_local, git_remote) = y(&f, index);
        assert_eq!(remote, before.1, "remote conflict unchanged on {index}");
        assert_eq!((git_local, git_remote), (before.2, before.3));
        assert_eq!(local, before.0, "local bookmark on {index}");
    }
    f.assert_converged();
    // A fetch imports its result even though the physical ref is unchanged.
    f.repo(HERE).jj(&["git", "fetch"]);
    f.sync();
    f.assert_converged();
    for index in [HERE, THERE] {
        assert_eq!(y(&f, index), synced, "merged on {index}");
    }
    // `y` is `y@origin`, so `jj git push` sends nothing, and `origin` keeps `settled`.
    f.repo(HERE).jj(&["git", "push", "--bookmark", "y"]);
    let remote = f.repo(HERE).git(&["--git-dir", &origin, "rev-parse", "y"]);
    assert_eq!(remote.trim(), settled, "origin's y after jj git push");
}

/// The fetch settles on a commit that is no term of the conflict.
#[test]
fn restoring_a_conflicted_remote_bookmark_keeps_the_fetched_value() {
    restore_a_conflicted_remote_bookmark("base");
}

/// The fetch settles on a term of the conflict, its base or the side musubi didn't write:
/// a value the hive knows of, which musubi would replace, were the expected value not that
/// value itself.
#[test]
fn restoring_a_conflicted_remote_bookmark_keeps_a_fetched_term() {
    restore_a_conflicted_remote_bookmark("one");
    restore_a_conflicted_remote_bookmark("two");
}
