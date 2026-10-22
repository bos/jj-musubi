//! Repositories and histories of different kinds in one hive.

use musubi_testutil::TestEnv;

use crate::fixture::Fixture;
use crate::remotes::create_origin;
use crate::remotes::seed_git;

/// A repository that isn't colocated keeps its git store inside `.jj`, where musubi reads
/// and writes objects, with no `.git` to keep in step. It shares a hive with colocated ones
/// all the same: work and bookmarks from each reach the other, the colocated one's `.git`
/// gets the branches, and it merges concurrent work like any other machine.
#[test]
fn colocated_and_non_colocated_repositories_share_a_hive() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    // Syncing second, beta is the machine that merges.
    let beta = env.init_non_colocated_repo("beta");
    let mut hive = Fixture::join(env, vec![alpha, beta]);
    hive.commit(0, "a", "from alpha, colocated");
    hive.repo(0)
        .jj(&["bookmark", "create", "from-alpha", "-r", "@-"]);
    hive.commit(1, "b", "from beta, not colocated");
    hive.repo(1)
        .jj(&["bookmark", "create", "from-beta", "-r", "@-"]);
    hive.sync();
    hive.assert_converged();
    assert!(!hive.repo(1).path().join(".git").exists());
    let from_beta = hive.commit_id(0, "from beta, not colocated");
    assert_eq!(
        hive.repo(0).git(&["rev-parse", "from-beta"]).trim(),
        from_beta
    );
    let from_alpha = hive.commit_id(1, "from alpha, colocated");
    assert_eq!(hive.bookmarks(1)["from-alpha@"], from_alpha);
}

/// History with a submodule replicates. Its trees name the submodule's commit, which no
/// machine has, and nothing transfers it or asks for it.
#[test]
fn history_with_a_submodule_replicates() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let seed = create_origin(&hive);
    let sub = hive.env.root().join("sub");
    std::fs::create_dir_all(&sub).unwrap();
    seed_git(&hive, &sub, &["init", "--quiet", "--initial-branch=main"]);
    std::fs::write(sub.join("s"), "s").unwrap();
    seed_git(&hive, &sub, &["add", "."]);
    seed_git(&hive, &sub, &["commit", "--quiet", "-m", "sub"]);
    // git refuses local submodules by default (CVE-2022-39253).
    let add = [
        "-c",
        "protocol.file.allow=always",
        "submodule",
        "--quiet",
        "add",
        sub.to_str().unwrap(),
        "sub",
    ];
    seed_git(&hive, &seed, &add);
    seed_git(
        &hive,
        &seed,
        &["commit", "--quiet", "-m", "add a submodule"],
    );
    let origin = hive.env.root().join("origin.git");
    seed_git(
        &hive,
        &seed,
        &["push", "--quiet", origin.to_str().unwrap(), "main"],
    );

    let alpha = hive.repo(0);
    alpha.jj(&["git", "remote", "add", "origin", origin.to_str().unwrap()]);
    alpha.jj(&["git", "fetch"]);
    alpha.jj(&["new", "main@origin"]);
    hive.commit(0, "after", "after the submodule");
    hive.sync();
    hive.assert_converged();
    let added = hive.commit_id(1, "add a submodule");
    let entry = hive.repo(1).git(&["ls-tree", &added, "sub"]);
    assert!(entry.starts_with("160000 commit "), "{entry}");
}
