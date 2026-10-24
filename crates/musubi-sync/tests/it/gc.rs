//! What jj's gc would clean up in a machine's repository (`musubi_jj::gc`), with nothing
//! kept for being new: keep refs beyond the heads of jj's index, never an object. Pruned
//! afterwards, as a `git gc` the user runs, or `jj util gc`, would, nothing the hive needs
//! goes; and what does go, that a sync was about to use, is fetched again.

#![allow(clippy::unwrap_used)]

use std::process::Command;
use std::time::Duration;
use std::time::SystemTime;

use jj_lib::object_id::ObjectId as _;
use musubi_jj::gc;
use musubi_jj::node::NodeRepo;
use musubi_jj::objects::Backend;
use musubi_sync::hive::Hive;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;

fn join(hive: &mut Hive, repo: &TestRepo) -> usize {
    let mut node = NodeRepo::open(&repo.repo_path(), &repo.settings())
        .unwrap()
        .with_repo_config(Some(repo.repo_config_path()));
    node.create_join_operation(&format!("musubi: {} joins", repo.machine()))
        .unwrap();
    hive.add(node).unwrap()
}

/// Runs musubi's gc in `repo` as if everything unreachable were old.
fn collect_everything(repo: &TestRepo) {
    let later = SystemTime::now() + Duration::from_secs(3600);
    assert!(gc::collect(&repo.repo_path(), &repo.settings(), later).unwrap());
}

/// Prunes `repo`'s git objects that no ref reaches, as `jj util gc` would.
fn prune(repo: &TestRepo) {
    repo.git(&["gc", "--quiet", "--prune=now"]);
}

fn keep_refs(repo: &TestRepo) -> usize {
    repo.git(&["for-each-ref", "--format=%(refname)", "refs/jj/keep/"])
        .lines()
        .count()
}

/// Whether `repo`'s git object store has the object `hex`.
fn has_object(repo: &TestRepo, hex: &str) -> bool {
    Command::new("git")
        .arg("--git-dir")
        .arg(repo.path().join(".git"))
        .args(["cat-file", "-e", hex])
        .status()
        .unwrap()
        .success()
}

fn descriptions(repo: &TestRepo) -> String {
    repo.jj(&["log", "--no-graph", "-r", "all()", "-T", "description"])
}

/// Every commit the machine's canonical operations require, those it made and those it
/// received alike, survives gc and a prune: the heads of jj's index, whose keep refs gc
/// leaves, reach every commit a reachable operation refers to, the predecessors it records
/// included. gc deletes no object; the prune deletes one nothing refers to. The hive syncs
/// on afterwards.
#[test]
fn gc_keeps_every_commit_the_hive_requires() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    let mut hive = Hive::new(&env.root().join("hub"), Backend::Git).unwrap();
    let a = join(&mut hive, &alpha);
    let b = join(&mut hive, &beta);
    // Rewrites, so that operations record predecessors, and an abandoned commit, which
    // only old operations refer to.
    alpha.write_file("f", "1");
    alpha.jj(&["commit", "-m", "one"]);
    alpha.write_file("f", "2");
    alpha.jj(&["describe", "-m", "two"]);
    alpha.write_file("f", "3");
    alpha.jj(&["squash", "--into", "@-", "--use-destination-message"]);
    alpha.jj(&["new", "-m", "dropped"]);
    alpha.write_file("g", "1");
    alpha.jj(&["abandon", "@"]);
    hive.sync_all().unwrap();
    beta.write_file("h", "1");
    beta.jj(&["commit", "-m", "beta work"]);
    hive.sync_all().unwrap();

    let stray_file = env.root().join("stray");
    std::fs::write(&stray_file, "nothing refers to this").unwrap();
    let stray = alpha.git(&["hash-object", "-w", stray_file.to_str().unwrap()]);
    let stray = stray.trim();

    for repo in [&alpha, &beta] {
        let before = keep_refs(repo);
        collect_everything(repo);
        assert!(
            keep_refs(repo) < before,
            "{} kept every keep ref",
            repo.machine()
        );
    }
    assert!(has_object(&alpha, stray), "musubi's gc deleted an object");
    for repo in [&alpha, &beta] {
        prune(repo);
    }
    assert!(!has_object(&alpha, stray), "git pruned nothing");
    for (node, repo) in [(a, &alpha), (b, &beta)] {
        let canonical = hive.members[node].adapter.repo().canonical_store();
        let required = canonical
            .required_commits(&canonical.operation_ids().unwrap())
            .unwrap();
        assert!(!required.is_empty());
        for commit in required {
            assert!(
                has_object(repo, &commit.hex()),
                "{} lost {}",
                repo.machine(),
                commit.hex()
            );
        }
    }

    alpha.jj(&["new", "-m", "after"]);
    hive.sync_all().unwrap();
    assert!(descriptions(&beta).contains("after"));
}

/// Objects fetched for operations not yet realized are garbage to git once gc has left no
/// keep ref to them, since nothing refers to them yet. A prune removes them, and the node
/// fetches them again before it realizes the operations.
#[test]
fn objects_removed_before_realizing_are_fetched_again() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    let mut hive = Hive::new(&env.root().join("hub"), Backend::Git).unwrap();
    let a = join(&mut hive, &alpha);
    let b = join(&mut hive, &beta);
    hive.sync_all().unwrap();
    alpha.write_file("f", "alpha's work");
    alpha.jj(&["commit", "-m", "alpha work"]);
    hive.sync(a).unwrap();
    let commit = alpha.jj(&[
        "log",
        "--no-graph",
        "-r",
        "description(substring:\"alpha work\")",
        "-T",
        "commit_id",
    ]);

    hive.fetch(b).unwrap();
    assert!(has_object(&beta, &commit));
    collect_everything(&beta);
    assert!(has_object(&beta, &commit), "musubi's gc deleted an object");
    prune(&beta);
    assert!(
        !has_object(&beta, &commit),
        "the prune kept what nothing refers to"
    );
    hive.sync(b).unwrap();
    assert!(has_object(&beta, &commit));
    assert!(descriptions(&beta).contains("alpha work"));
    let content = beta.jj(&[
        "file",
        "show",
        "-r",
        "description(substring:\"alpha work\")",
        "f",
    ]);
    assert_eq!(content, "alpha's work");
}

/// A copy that has just joined has too little to clean up for gc to be due, however long
/// since it last ran: it would only spend time on a machine that may not live long.
#[test]
fn a_new_copy_is_not_worth_collecting() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    let mut hive = Hive::new(&env.root().join("hub"), Backend::Git).unwrap();
    join(&mut hive, &alpha);
    join(&mut hive, &beta);
    alpha.write_file("f", "1");
    alpha.jj(&["commit", "-m", "one"]);
    hive.sync_all().unwrap();
    for repo in [&alpha, &beta] {
        let cruft = gc::Cruft::of(&repo.repo_path());
        assert!(cruft.extras_files > 0 && cruft.keep_refs > 0, "{cruft:?}");
        assert!(!cruft.worth_collecting(), "{cruft:?}");
        assert!(!gc::due(&repo.repo_path(), SystemTime::now()));
    }
}
