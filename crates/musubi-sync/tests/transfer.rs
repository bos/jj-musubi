//! What syncing transfers, nothing a node already has (docs/design.md, "Joining"), and
//! what it leaves behind in git's object stores.

#![allow(clippy::unwrap_used)]

use std::path::Path;
use std::process::Command;

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

fn git(git_dir: &Path, args: &[&str]) -> String {
    let output = Command::new("git")
        .args(args)
        .env("GIT_DIR", git_dir)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "git {args:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

fn packs(git_dir: &Path) -> usize {
    std::fs::read_dir(git_dir.join("objects/pack"))
        .unwrap()
        .filter(|entry| {
            entry
                .as_ref()
                .unwrap()
                .path()
                .extension()
                .is_some_and(|ext| ext == "pack")
        })
        .count()
}

/// Adds `count` packs to `git_dir`, each holding one blob that nothing refers to. Returns
/// the blobs.
fn add_unreachable_packs(git_dir: &Path, count: usize) -> Vec<String> {
    (0..count)
        .map(|i| {
            let file = git_dir.join(format!("junk-{i}"));
            std::fs::write(&file, format!("unreachable {i}")).unwrap();
            let blob = git(git_dir, &["hash-object", "-w", file.to_str().unwrap()]);
            let blob = blob.trim().to_owned();
            let pack = git_dir.join("objects/pack/pack");
            let mut child = Command::new("git")
                .args(["pack-objects", "-q", pack.to_str().unwrap()])
                .env("GIT_DIR", git_dir)
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::null())
                .spawn()
                .unwrap();
            std::io::Write::write_all(child.stdin.as_mut().unwrap(), blob.as_bytes()).unwrap();
            assert!(child.wait().unwrap().success());
            std::fs::remove_file(git_dir.join("objects").join(&blob[..2]).join(&blob[2..]))
                .unwrap();
            std::fs::remove_file(file).unwrap();
            blob
        })
        .collect()
}

/// A small transfer leaves loose objects behind, not a pack: a pack per sync would pile up.
#[test]
fn small_transfers_leave_no_pack() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    let mut hive = Hive::new(&env.root().join("hub"), Backend::Git).unwrap();
    let a = join(&mut hive, &alpha);
    let b = join(&mut hive, &beta);
    hive.sync_all().unwrap();

    let (alpha_git, hub_git) = (alpha.path().join(".git"), env.root().join("hub/git"));
    let before = (packs(&alpha_git), packs(&hub_git));
    beta.write_file("small", "small");
    beta.jj(&["commit", "-m", "small"]);
    hive.sync(b).unwrap();
    hive.sync(a).unwrap();
    assert_eq!((packs(&alpha_git), packs(&hub_git)), before);
}

/// Packs are consolidated once there are too many, on nodes and on the hub, but nothing is
/// deleted, not even objects nothing refers to.
#[test]
fn packs_are_consolidated_and_nothing_is_lost() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    let mut hive = Hive::new(&env.root().join("hub"), Backend::Git).unwrap();
    let a = join(&mut hive, &alpha);
    let b = join(&mut hive, &beta);
    hive.sync_all().unwrap();

    let (alpha_git, hub_git) = (alpha.path().join(".git"), env.root().join("hub/git"));
    let mut blobs = vec![];
    for git_dir in [&alpha_git, &hub_git] {
        git(git_dir, &["config", "gc.autoPackLimit", "3"]);
        git(git_dir, &["config", "gc.autoDetach", "false"]);
        blobs.push((git_dir, add_unreachable_packs(git_dir, 5)));
    }
    beta.write_file("small", "small");
    beta.jj(&["commit", "-m", "small"]);
    hive.sync(b).unwrap();
    hive.sync(a).unwrap();
    for (git_dir, blobs) in blobs {
        assert!(
            packs(git_dir) <= 2,
            "{} packs in {git_dir:?}",
            packs(git_dir)
        );
        for blob in blobs {
            git(git_dir, &["cat-file", "-e", &blob]);
        }
    }
    hive.sync_all().unwrap();
}

/// jj-lib's git backend sizes its table of pack indexes when it opens the repository. A
/// node that has been running while packs were added still reads the objects it receives.
#[test]
fn node_keeps_up_as_packs_pile_up() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    let mut hive = Hive::new(&env.root().join("hub"), Backend::Git).unwrap();
    let a = join(&mut hive, &alpha);
    let b = join(&mut hive, &beta);
    hive.sync_all().unwrap();

    let alpha_git = alpha.path().join(".git");
    // Not consolidated, as with `jj git fetch` run often and gc disabled.
    git(&alpha_git, &["config", "gc.auto", "0"]);
    add_unreachable_packs(&alpha_git, 40);
    // Enough objects to arrive as a pack.
    for i in 0..120 {
        beta.write_file(&format!("file-{i}"), &format!("file {i}"));
    }
    beta.jj(&["commit", "-m", "many files"]);
    hive.sync(b).unwrap();
    hive.sync(a).unwrap();
    hive.sync_all().unwrap();
}
