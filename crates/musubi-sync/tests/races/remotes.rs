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
pub fn create_origin(hive: &Fixture) -> PathBuf {
    let origin = hive.env.root().join("origin.git");
    let seed = hive.env.root().join("seed");
    std::fs::create_dir_all(&seed).unwrap();
    seed_git(
        hive,
        hive.env.root(),
        &[
            "init",
            "--quiet",
            "--bare",
            "--initial-branch=main",
            origin.to_str().unwrap(),
        ],
    );
    seed_git(hive, &seed, &["init", "--quiet", "--initial-branch=main"]);
    std::fs::write(seed.join("upstream"), "upstream 1").unwrap();
    seed_git(hive, &seed, &["add", "."]);
    seed_git(hive, &seed, &["commit", "--quiet", "-m", "upstream 1"]);
    seed_git(
        hive,
        &seed,
        &["push", "--quiet", origin.to_str().unwrap(), "main"],
    );
    seed
}

fn remotes(hive: &Fixture, index: usize) -> String {
    hive.repo(index).jj(&["git", "remote", "list"])
}

/// Joining, syncing, and reopening never copy or rewrite local remote definitions,
/// including when another machine changes both URLs while this config is locked.
#[test]
fn remote_configuration_stays_local() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    const ONE: &str = "https://example.com/one.git";
    const MOVED: &str = "https://example.com/moved.git";
    const MIRROR: &str = "https://example.com/mirror.git";
    for repo in [&alpha, &beta] {
        repo.jj(&["git", "remote", "add", "origin", ONE]);
        repo.git(&["config", "remote.origin.pushurl", MIRROR]);
    }
    beta.jj(&["git", "remote", "add", "extra", MIRROR]);
    let config = beta.path().join(".git/config");
    let before = std::fs::read(&config).unwrap();
    let mut hive = Fixture::join(env, vec![alpha, beta]);
    hive.repo(0)
        .jj(&["git", "remote", "set-url", "origin", MOVED]);
    hive.repo(0)
        .git(&["config", "--unset-all", "remote.origin.pushurl"]);
    let lock = config.with_extension("lock");
    std::fs::write(&lock, "").unwrap();
    hive.sync();
    hive.reopen(1);
    hive.sync();
    std::fs::remove_file(lock).unwrap();
    assert_eq!(std::fs::read(config).unwrap(), before);
    assert_eq!(remotes(&hive, 0), format!("origin {MOVED}\n"));
    assert_eq!(
        remotes(&hive, 1),
        format!("extra {MIRROR}\norigin {ONE} (push: {MIRROR})\n")
    );
    // An explicit local reversion is simply local configuration, not an unfinished sync.
    hive.repo(1)
        .jj(&["git", "remote", "set-url", "origin", MOVED]);
    hive.repo(1)
        .jj(&["git", "remote", "set-url", "origin", ONE]);
    hive.repo(0).jj(&["git", "remote", "remove", "origin"]);
    hive.sync();
    hive.assert_converged();
    assert_eq!(remotes(&hive, 0), "");
    assert!(remotes(&hive, 1).contains(ONE));
}

/// Renaming or removing a remote changes the shared remote bookmarks, while each
/// machine's configured remote names stay local.
#[test]
fn remote_renames_change_bookmarks_but_not_other_machines_config() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    with_origin(&hive);
    hive.repo(0).jj(&["git", "fetch"]);
    hive.sync();
    let beta_remotes = remotes(&hive, 1);
    hive.repo(0)
        .jj(&["git", "remote", "rename", "origin", "upstream"]);
    hive.sync();
    hive.assert_converged();
    assert_eq!(remotes(&hive, 1), beta_remotes);
    assert!(hive.bookmarks(1).contains_key("main@upstream"));
    assert!(!hive.bookmarks(1).contains_key("main@origin"));
    hive.repo(0).jj(&["git", "remote", "remove", "upstream"]);
    hive.sync();
    hive.assert_converged();
    assert_eq!(remotes(&hive, 1), beta_remotes);
    assert!(!hive.bookmarks(1).contains_key("main@upstream"));
}

/// Runs `git` in `dir`, such as the clone that seeds origin, as origin's author, in the
/// tests' hermetic environment.
pub fn seed_git(hive: &Fixture, dir: &std::path::Path, args: &[&str]) {
    let out = hive
        .repo(0)
        .program(std::path::Path::new("git"))
        .current_dir(dir)
        .args(args)
        .env("GIT_AUTHOR_NAME", "o")
        .env("GIT_AUTHOR_EMAIL", "o@example.com")
        .env("GIT_COMMITTER_NAME", "o")
        .env("GIT_COMMITTER_EMAIL", "o@example.com")
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "git {args:?}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

fn advance_origin(hive: &Fixture, seed: &std::path::Path, n: usize) {
    let origin = hive.env.root().join("origin.git");
    let run = |args: &[&str]| seed_git(hive, seed, args);
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
    hive.repo(1).jj(&["git", "remote", "remove", "origin"]);
    hive.repo(0).jj(&["git", "fetch"]);
    hive.sync();
    // Beta works with no remote configured; alpha is the only machine using upstream Git.
    assert_eq!(remotes(&hive, 1), "");
    hive.repo(1).jj(&["new", "main@origin"]);
    hive.commit(1, "feature", "feature");
    hive.repo(1)
        .jj(&["bookmark", "create", "feature", "-r", "@-"]);
    hive.sync();
    hive.repo(0).jj(&["git", "push", "--bookmark", "feature"]);
    hive.sync();
    hive.assert_converged();
    let feature = hive.commit_id(1, "feature");
    assert_eq!(hive.bookmarks(1)["feature@origin"], feature);
    assert_eq!(remotes(&hive, 1), "");
}

/// Whether remote bookmark `symbol` (`main@origin`) is tracked on machine `index`.
fn tracked(hive: &Fixture, index: usize, symbol: &str) -> bool {
    let template = r#"if(remote, name ++ "@" ++ remote ++ " " ++ if(tracked, "tracked", "untracked") ++ "\n")"#;
    let list = hive
        .repo(index)
        .jj(&["bookmark", "list", "--all-remotes", "-T", template]);
    list.lines()
        .find_map(|line| line.strip_prefix(symbol)?.strip_prefix(' '))
        == Some("tracked")
}

/// One machine stops tracking a remote bookmark; every machine stops, so a later fetch on
/// any of them moves the remote bookmark but leaves the local one where it was.
#[test]
fn untracking_a_remote_bookmark_reaches_every_machine() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let seed = with_origin(&hive);
    hive.repo(0).jj(&["git", "fetch"]);
    hive.repo(0).jj(&["bookmark", "track", "main@origin"]);
    hive.sync();
    hive.assert_converged();
    assert!(tracked(&hive, 1, "main@origin"));
    let upstream = hive.bookmarks(1)["main@"].clone();

    hive.repo(0).jj(&["bookmark", "untrack", "main@origin"]);
    hive.sync();
    assert!(!tracked(&hive, 1, "main@origin"));
    advance_origin(&hive, &seed, 2);
    hive.repo(1).jj(&["git", "fetch"]);
    hive.sync();
    hive.assert_converged();
    for index in [0, 1] {
        let bookmarks = hive.bookmarks(index);
        assert_eq!(bookmarks["main@"], upstream, "local main on {index}");
        assert_ne!(bookmarks["main@origin"], upstream, "main@origin on {index}");
        assert!(!tracked(&hive, index, "main@origin"), "{index}");
    }
}

/// A `file://` URL for `path`, as git takes one on any platform.
fn file_url(path: &std::path::Path) -> String {
    let path = path.to_string_lossy().replace('\\', "/");
    format!(
        "file://{}{path}",
        if path.starts_with('/') { "" } else { "/" }
    )
}

/// Whether any file under `dir` holds `needle`.
fn holds(dir: &std::path::Path, needle: &[u8]) -> bool {
    std::fs::read_dir(dir).unwrap().flatten().any(|entry| {
        let path = entry.path();
        if path.is_dir() {
            holds(&path, needle)
        } else {
            let bytes = std::fs::read(&path).unwrap_or_default();
            bytes.windows(needle.len()).any(|window| window == needle)
        }
    })
}

/// Explicit joins record credential-free URL hints, including Git alias expansions.
/// Neither those hints nor later operations configure another machine's remotes.
#[test]
fn remote_urls_are_join_hints_without_credentials() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    let root = file_url(env.root());
    alpha.git(&["config", &format!("url.{root}/.insteadOf"), "musubi-test:"]);
    alpha.jj(&["git", "remote", "add", "origin", "musubi-test:origin.git"]);
    let token = "https://alpha:secret@example.com/team/backup.git";
    alpha.jj(&["git", "remote", "add", "backup", token]);
    let mut hive = Fixture::join(env, vec![alpha, beta]);
    let summary = hive.node(0).join_summary().unwrap();
    assert_eq!(
        summary.remotes["origin"].expanded_url,
        Some(format!("{root}/origin.git"))
    );
    assert_eq!(
        summary.remotes["backup"].url.as_deref(),
        Some("https://example.com/team/backup.git")
    );
    let store = hive.node(0).canonical_store();
    let hints: std::collections::BTreeSet<String> = store
        .operation_ids()
        .unwrap()
        .into_iter()
        .flat_map(|id| {
            store
                .read_operation(&id)
                .unwrap()
                .metadata
                .attributes
                .into_iter()
                .filter(|(key, _)| key.starts_with(musubi_jj::remote_url::JOIN_URL_PREFIX))
                .map(|(_, url)| url)
                .collect::<Vec<_>>()
        })
        .collect();
    assert!(hints.contains("musubi-test:origin.git"));
    assert!(hints.contains(&format!("{root}/origin.git")));
    assert!(hints.contains("https://example.com/team/backup.git"));
    assert_eq!(remotes(&hive, 1), "");
    // Credentials are redacted from jj's recorded arguments too, including later edits.
    hive.repo(0).jj(&[
        "git",
        "remote",
        "set-url",
        "backup",
        "https://alpha:secret@example.com/team/later.git",
    ]);
    hive.sync();
    assert!(!holds(&hive.env.root().join("hub"), b"secret"));
    assert!(!holds(&hive.repo(1).path().join(".jj"), b"secret"));
    assert!(
        hive.repo(0)
            .git(&["config", "remote.backup.url"])
            .contains("secret")
    );
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

/// Force-pushes `main` on origin to a sibling of its current commit: a new commit on the
/// current commit's parent.
fn force_origin(hive: &Fixture, seed: &std::path::Path, n: usize) {
    let origin = hive.env.root().join("origin.git");
    let run = |args: &[&str]| seed_git(hive, seed, args);
    run(&["reset", "--quiet", "--hard", "HEAD~"]);
    std::fs::write(seed.join("upstream"), format!("upstream {n}")).unwrap();
    run(&["commit", "--quiet", "-am", &format!("upstream {n}")]);
    run(&[
        "push",
        "--quiet",
        "--force",
        origin.to_str().unwrap(),
        "main",
    ]);
}

/// `main@origin` as the machine's latest operation records it. `--ignore-working-copy`
/// keeps jj from importing git refs first, as any other `jj` command would.
fn recorded_main_at_origin(hive: &Fixture, index: usize) -> String {
    let template = r#"if(remote == "origin", if(conflict, "conflict", normal_target.commit_id()))"#;
    hive.repo(index).jj(&[
        "--ignore-working-copy",
        "bookmark",
        "list",
        "--all-remotes",
        "main",
        "-T",
        template,
    ])
}

/// Two machines fetch while origin is force-pushed between their fetches, so the hive's
/// `main@origin` is conflicted. A third machine's `.git` still has the
/// `refs/remotes/origin/main` of its own earlier fetch. musubi writes one of the conflict's
/// sides there, the same on every machine. Ordinary commands keep the conflict; an explicit
/// fetch resolves it, including when the physical ref is unchanged. With `stale_record`,
/// the third machine's `.git` has the fetch
/// of that machine instead, disagreeing with jj's record of it, as after `jj op restore`.
fn conflicted_fetches(stale_record: Option<usize>) {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    let seed = with_origin(&hive);
    hive.repo(2).jj(&["git", "fetch"]);
    hive.sync();
    let first = recorded_main_at_origin(&hive, 2);
    advance_origin(&hive, &seed, 2);
    hive.repo(0).jj(&["git", "fetch"]);
    let alphas = recorded_main_at_origin(&hive, 0);
    force_origin(&hive, &seed, 3);
    hive.repo(1).jj(&["git", "fetch"]);
    let betas = recorded_main_at_origin(&hive, 1);
    if let Some(fetcher) = stale_record {
        // Behind jj's back: fetch that machine's commit into a scratch ref, then point
        // gamma's remote-tracking ref at it.
        let gamma = hive.repo(2);
        let fetched = recorded_main_at_origin(&hive, fetcher);
        gamma.git(&[
            "fetch",
            "--quiet",
            hive.repo(fetcher).path().to_str().unwrap(),
            "+refs/remotes/origin/main:refs/scratch/main",
        ]);
        gamma.git(&["update-ref", "refs/remotes/origin/main", &fetched]);
        gamma.git(&["update-ref", "-d", "refs/scratch/main"]);
    }
    hive.sync();
    for index in 0..3 {
        assert_eq!(
            recorded_main_at_origin(&hive, index),
            "conflict",
            "on {index}"
        );
    }
    let git_main = |index: usize| {
        hive.repo(index)
            .git(&["rev-parse", "refs/remotes/origin/main"])
            .trim()
            .to_owned()
    };
    let side = git_main(2);
    assert!(
        side == alphas || side == betas,
        "{side} is not a fetched side"
    );
    assert_ne!(side, first);
    for index in 0..3 {
        assert_eq!(git_main(index), side, "git on {index}");
        hive.repo(index).jj(&["status"]);
        assert_eq!(
            recorded_main_at_origin(&hive, index),
            "conflict",
            "on {index}"
        );
    }
    let origin = hive.env.root().join("origin.git");
    hive.repo(0).git(&[
        "--git-dir",
        origin.to_str().unwrap(),
        "update-ref",
        "refs/heads/main",
        &side,
    ]);
    hive.repo(0).jj(&["git", "fetch"]);
    hive.sync();
    hive.assert_converged();
    for index in 0..3 {
        assert_eq!(recorded_main_at_origin(&hive, index), side, "on {index}");
    }
}

#[test]
fn conflicted_remote_bookmark_resolves_to_a_fetched_side() {
    conflicted_fetches(None);
}

/// One of these two has gamma's `.git` on the side musubi doesn't choose.
#[test]
fn conflicted_remote_bookmark_resolves_despite_a_stale_record() {
    conflicted_fetches(Some(0));
    conflicted_fetches(Some(1));
}
