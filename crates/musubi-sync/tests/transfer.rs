//! What syncing transfers: nothing a node already has (docs/design.md, "Joining").

#![allow(clippy::unwrap_used)]

use musubi_hub::store::Backend;
use musubi_jj::node::NodeRepo;
use musubi_sync::hive::Hive;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;

/// Incompressible content, so that a transfer that includes it shows.
const BIG: usize = 256 * 1024;

/// Much less than [`BIG`], but enough for operations, views and small commits.
const SMALL: u64 = 64 * 1024;

fn big_file(repo: &TestRepo, name: &str) {
    let mut bytes = vec![0; BIG];
    blake3::Hasher::new()
        .update(name.as_bytes())
        .finalize_xof()
        .fill(&mut bytes);
    std::fs::write(repo.path().join(name), bytes).unwrap();
}

fn join(hive: &mut Hive, repo: &TestRepo) -> usize {
    let mut node = NodeRepo::open(&repo.repo_path(), &repo.settings())
        .unwrap()
        .with_repo_config(Some(repo.repo_config_path()));
    node.create_join_operation(&format!("musubi: {} joins", repo.machine()))
        .unwrap();
    hive.add(node).unwrap()
}

/// Syncs `node` and returns how many bytes it downloaded.
fn downloaded_by_sync(hive: &mut Hive, node: usize) -> u64 {
    let before = hive.members[node].downloaded;
    hive.sync(node).unwrap();
    hive.members[node].downloaded - before
}

/// A machine that joins with a copy of the repository the hive started from downloads only
/// what it lacks, not the whole history again.
#[test]
fn joining_with_a_copy_downloads_only_what_is_new() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    big_file(&alpha, "big");
    alpha.jj(&["commit", "-m", "big"]);
    alpha.jj(&["bookmark", "create", "main", "-r", "@-"]);
    let beta = env.init_repo("beta");
    let alpha_git = alpha.path().join(".git");
    beta.jj(&[
        "git",
        "remote",
        "add",
        "origin",
        alpha_git.to_str().unwrap(),
    ]);
    beta.jj(&["git", "fetch", "--remote", "origin"]);

    let mut hive = Hive::new(&env.root().join("hub"), Backend::Git).unwrap();
    let a = join(&mut hive, &alpha);
    let b = join(&mut hive, &beta);
    hive.sync(a).unwrap();
    let downloaded = downloaded_by_sync(&mut hive, b);
    assert!(
        downloaded < SMALL,
        "beta downloaded {downloaded} bytes it mostly had"
    );
}

/// The machine that seeded the hive downloads only what joined since, not its own history.
#[test]
fn seeding_machine_does_not_download_its_own_history() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    big_file(&alpha, "big");
    alpha.jj(&["commit", "-m", "big"]);
    let beta = env.init_repo("beta");

    let mut hive = Hive::new(&env.root().join("hub"), Backend::Git).unwrap();
    let a = join(&mut hive, &alpha);
    let b = join(&mut hive, &beta);
    hive.sync(a).unwrap();
    hive.sync(b).unwrap();
    let downloaded = downloaded_by_sync(&mut hive, a);
    assert!(
        downloaded < SMALL,
        "alpha downloaded {downloaded} bytes it had uploaded"
    );
}

/// A machine never downloads what it uploaded itself.
#[test]
fn own_uploads_are_not_downloaded_again() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    let mut hive = Hive::new(&env.root().join("hub"), Backend::Git).unwrap();
    let a = join(&mut hive, &alpha);
    let b = join(&mut hive, &beta);
    hive.sync_all().unwrap();

    for name in ["one", "two"] {
        big_file(&alpha, name);
        alpha.jj(&["commit", "-m", name]);
        hive.sync(a).unwrap();
    }
    hive.sync(b).unwrap();
    beta.write_file("small", "small");
    beta.jj(&["commit", "-m", "small"]);
    hive.sync(b).unwrap();
    let downloaded = downloaded_by_sync(&mut hive, a);
    assert!(
        downloaded < SMALL,
        "alpha downloaded {downloaded} bytes, most of which it had uploaded"
    );
}
