//! Git remotes: fetches and pushes on different machines.

use std::path::PathBuf;

use musubi_testutil::TestEnv;

use crate::fixture::Fixture;

/// A bare `origin` with one commit on `main`, and each machine configured to use it.
fn with_origin(hive: &Fixture) -> PathBuf {
    let seed = create_origin(hive);
    let origin = hive.env.root().join("origin.git");
    for repo in &hive.repos {
        repo.jj(&["git", "remote", "add", "origin", origin.to_str().unwrap()]);
    }
    seed
}

/// A bare `origin` with one commit on `main`; returns the clone that seeded it.
fn create_origin(hive: &Fixture) -> PathBuf {
    let origin = hive.env.root().join("origin.git");
    let seed = hive.env.root().join("seed");
    let git = |dir: &std::path::Path, args: &[&str]| {
        let status = std::process::Command::new("git")
            .current_dir(dir)
            .args(args)
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env("HOME", hive.env.root().join("home"))
            .env("GIT_AUTHOR_NAME", "o")
            .env("GIT_AUTHOR_EMAIL", "o@example.com")
            .env("GIT_COMMITTER_NAME", "o")
            .env("GIT_COMMITTER_EMAIL", "o@example.com")
            .output()
            .unwrap();
        assert!(
            status.status.success(),
            "git {args:?}: {}",
            String::from_utf8_lossy(&status.stderr)
        );
    };
    std::fs::create_dir_all(&seed).unwrap();
    git(
        hive.env.root(),
        &[
            "init",
            "--quiet",
            "--bare",
            "--initial-branch=main",
            origin.to_str().unwrap(),
        ],
    );
    git(&seed, &["init", "--quiet", "--initial-branch=main"]);
    std::fs::write(seed.join("upstream"), "upstream 1").unwrap();
    git(&seed, &["add", "."]);
    git(&seed, &["commit", "--quiet", "-m", "upstream 1"]);
    git(
        &seed,
        &["push", "--quiet", origin.to_str().unwrap(), "main"],
    );
    seed
}

fn remotes(hive: &Fixture, index: usize) -> String {
    hive.repo(index).jj(&["git", "remote", "list"])
}

/// A remote added on one machine is added on every machine, so any machine can fetch it.
#[test]
fn remote_added_on_one_machine_reaches_the_others() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    create_origin(&hive);
    let origin = hive.env.root().join("origin.git");
    hive.repo(0)
        .jj(&["git", "remote", "add", "origin", origin.to_str().unwrap()]);
    hive.sync();
    assert_eq!(remotes(&hive, 1), remotes(&hive, 0));
    hive.repo(1).jj(&["git", "fetch"]);
    hive.sync();
    hive.assert_converged();
    assert!(hive.bookmarks(0).contains_key("main@origin"));
}

/// Renaming or removing a remote on one machine does it on every machine, as jj renames
/// or forgets its remote bookmarks everywhere.
#[test]
fn remote_renamed_and_removed_everywhere() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    with_origin(&hive);
    hive.repo(0).jj(&["git", "fetch"]);
    hive.sync();
    hive.repo(0)
        .jj(&["git", "remote", "rename", "origin", "upstream"]);
    hive.sync();
    hive.assert_converged();
    assert_eq!(remotes(&hive, 1), remotes(&hive, 0));
    assert!(
        remotes(&hive, 1).starts_with("upstream "),
        "{}",
        remotes(&hive, 1)
    );
    hive.repo(1).jj(&["git", "fetch", "--remote", "upstream"]);
    hive.sync();
    hive.assert_converged();
    assert!(hive.bookmarks(0).contains_key("main@upstream"));
    hive.repo(1).jj(&["git", "remote", "remove", "upstream"]);
    hive.sync();
    hive.assert_converged();
    assert_eq!(remotes(&hive, 0), "");
}

/// Two machines point a remote at different URLs at once: they end up agreeing.
#[test]
fn remote_changed_on_two_machines_at_once() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.repo(0).jj(&[
        "git",
        "remote",
        "add",
        "origin",
        "https://example.com/one.git",
    ]);
    hive.sync();
    hive.repo(0).jj(&[
        "git",
        "remote",
        "set-url",
        "origin",
        "https://example.com/two.git",
    ]);
    hive.repo(1).jj(&[
        "git",
        "remote",
        "set-url",
        "origin",
        "https://example.com/three.git",
    ]);
    hive.sync();
    hive.assert_converged();
    assert_eq!(remotes(&hive, 0), remotes(&hive, 1));
}

/// A machine that joins adds its own remotes to the hive's, but takes the hive's where
/// both have a remote of the same name pointing to different repositories.
#[test]
fn joining_machine_merges_its_remotes_with_the_hives() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    alpha.jj(&[
        "git",
        "remote",
        "add",
        "origin",
        "https://example.com/hive.git",
    ]);
    beta.jj(&[
        "git",
        "remote",
        "add",
        "origin",
        "https://example.com/beta.git",
    ]);
    beta.jj(&[
        "git",
        "remote",
        "add",
        "extra",
        "https://example.com/extra.git",
    ]);
    let mut hive = Fixture::join(env, vec![alpha, beta]);
    hive.sync();
    hive.assert_converged();
    let expected = "extra https://example.com/extra.git\norigin https://example.com/hive.git\n";
    assert_eq!(remotes(&hive, 0), expected);
    assert_eq!(remotes(&hive, 1), expected);
}

/// Machines that reach one repository by different URLs, over https and ssh, say, each
/// keep their own, joining or later: only a change to where a remote points replicates.
#[test]
fn machines_keep_their_own_spelling_of_a_shared_remote() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    let https = "https://example.com/team/project.git";
    let ssh = "git@example.com:team/project";
    alpha.jj(&["git", "remote", "add", "origin", https]);
    beta.jj(&["git", "remote", "add", "origin", ssh]);
    let mut hive = Fixture::join(env, vec![alpha, beta]);
    hive.sync();
    hive.assert_converged();
    assert_eq!(remotes(&hive, 0), format!("origin {https}\n"));
    assert_eq!(remotes(&hive, 1), format!("origin {ssh}\n"));
    // Respelling it is still nobody else's business.
    let respelled = "ssh://git@example.com/team/project.git";
    hive.repo(1)
        .jj(&["git", "remote", "set-url", "origin", respelled]);
    hive.sync();
    hive.sync();
    assert_eq!(remotes(&hive, 0), format!("origin {https}\n"));
    assert_eq!(remotes(&hive, 1), format!("origin {respelled}\n"));
    // Pointing it elsewhere is everybody's.
    let moved = "https://example.com/team/moved.git";
    hive.repo(1)
        .jj(&["git", "remote", "set-url", "origin", moved]);
    hive.sync();
    hive.sync();
    hive.assert_converged();
    assert_eq!(remotes(&hive, 0), format!("origin {moved}\n"));
    assert_eq!(remotes(&hive, 1), format!("origin {moved}\n"));
}

/// The same, when the machine whose spelling the hive has changes the remote: the other
/// machine takes each change, keeping its own spelling of whatever still names the same
/// repository.
#[test]
fn changes_to_a_remote_reach_machines_with_their_own_spelling() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    let https = "https://example.com/team/project.git";
    let ssh = "git@example.com:team/project";
    alpha.jj(&["git", "remote", "add", "origin", https]);
    beta.jj(&["git", "remote", "add", "origin", ssh]);
    let mut hive = Fixture::join(env, vec![alpha, beta]);
    hive.sync();
    // A push URL for another repository replicates; beta keeps its fetch URL.
    let mirror = "git@example.com:team/mirror";
    hive.repo(0)
        .git(&["config", "remote.origin.pushurl", mirror]);
    hive.sync();
    hive.sync();
    assert_eq!(
        remotes(&hive, 1),
        format!("origin {ssh} (push: {mirror})\n")
    );
    // A rename moves beta's remote, with its own spelling and remote-tracking refs.
    // jj won't rename a remote with a push URL; git will.
    hive.repo(0)
        .git(&["remote", "rename", "origin", "upstream"]);
    hive.sync();
    hive.sync();
    assert_eq!(
        remotes(&hive, 0),
        format!("upstream {https} (push: {mirror})\n")
    );
    assert_eq!(
        remotes(&hive, 1),
        format!("upstream {ssh} (push: {mirror})\n")
    );
    // Pointing it elsewhere moves beta too.
    let moved = "https://example.com/team/moved.git";
    hive.repo(0)
        .jj(&["git", "remote", "set-url", "upstream", moved]);
    hive.sync();
    hive.sync();
    hive.assert_converged();
    let expected = format!("upstream {moved} (push: {mirror})\n");
    assert_eq!(remotes(&hive, 0), expected);
    assert_eq!(remotes(&hive, 1), expected);
}

fn advance_origin(hive: &Fixture, seed: &std::path::Path, n: usize) {
    let origin = hive.env.root().join("origin.git");
    let run = |args: &[&str]| {
        let out = std::process::Command::new("git")
            .current_dir(seed)
            .args(args)
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env("HOME", hive.env.root().join("home"))
            .env("GIT_AUTHOR_NAME", "o")
            .env("GIT_AUTHOR_EMAIL", "o@example.com")
            .env("GIT_COMMITTER_NAME", "o")
            .env("GIT_COMMITTER_EMAIL", "o@example.com")
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
    };
    std::fs::write(seed.join("upstream"), format!("upstream {n}")).unwrap();
    run(&["commit", "--quiet", "-am", &format!("upstream {n}")]);
    run(&["push", "--quiet", origin.to_str().unwrap(), "main"]);
}

/// One machine fetches; the other sees the remote bookmark, and its own git gets the
/// matching remote-tracking ref.
#[test]
fn fetch_on_one_machine_reaches_the_other() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let _seed = with_origin(&hive);
    hive.repo(0).jj(&["git", "fetch"]);
    hive.sync();
    hive.assert_converged();
    let fetched = hive.bookmarks(0)["main@origin"].clone();
    assert_eq!(hive.bookmarks(1)["main@origin"], fetched);
    assert_eq!(
        hive.repo(1)
            .git(&["rev-parse", "refs/remotes/origin/main"])
            .trim(),
        fetched
    );
}

/// Both machines fetch, at different moments, while origin moves between the fetches.
/// The later fetch descends from the earlier one, so jj resolves the remote bookmark to the
/// newer commit rather than a conflict.
#[test]
fn concurrent_fetches_of_a_moving_remote() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let seed = with_origin(&hive);
    hive.repo(0).jj(&["git", "fetch"]);
    advance_origin(&hive, &seed, 2);
    hive.repo(1).jj(&["git", "fetch"]);
    hive.sync();
    hive.assert_converged();
    let main = &hive.bookmarks(0)["main@origin"];
    assert!(!main.starts_with("conflict:"), "{main}");
    let newest = hive.repo(1).git(&["rev-parse", "refs/remotes/origin/main"]);
    assert_eq!(main, newest.trim());
}

/// One machine pushes a bookmark; the other sees it tracked and pushed.
#[test]
fn push_from_one_machine() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let _seed = with_origin(&hive);
    hive.repo(0).jj(&["git", "fetch"]);
    hive.repo(0).jj(&["new", "main@origin"]);
    hive.commit(0, "feature", "feature");
    hive.repo(0)
        .jj(&["bookmark", "create", "feature", "-r", "@-"]);
    hive.repo(0).jj(&["git", "push", "--bookmark", "feature"]);
    hive.sync();
    hive.assert_converged();
    let feature = hive.commit_id(1, "feature");
    assert_eq!(hive.bookmarks(1)["feature@origin"], feature);
}

/// Two repositories created independently, each with a `main` at a different commit,
/// joining one hive: jj merges the histories at the root, and `main` is conflicted until
/// someone resolves it.
#[test]
fn joining_repositories_with_conflicting_bookmarks() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    for (repo, name) in [(&alpha, "alpha"), (&beta, "beta")] {
        repo.write_file(name, name);
        repo.jj(&["commit", "-m", name]);
        repo.jj(&["bookmark", "create", "main", "-r", "@-"]);
    }
    let mut hive = Fixture::join(env, vec![alpha, beta]);
    hive.assert_converged();
    assert!(hive.bookmarks(0)["main@"].starts_with("conflict:"));
}
