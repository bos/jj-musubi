//! A publication hold stops objects before the hub sees them, while receiving continues.

#![allow(clippy::unwrap_used)]

use jj_lib::backend::CommitId;
use jj_lib::config::ConfigLayer;
use jj_lib::config::ConfigSource;
use musubi_jj::node::NodeRepo;
use musubi_jj::node::PublicationCache;
use musubi_jj::node::PublicationHeld;
use musubi_jj::node::approve_publication;
use musubi_jj::objects::Backend;
use musubi_sync::hive::Hive;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;

fn add(hive: &mut Hive, repo: &TestRepo) -> usize {
    let mut settings = repo.settings();
    let mut config = settings.config().clone();
    config.add_layer(
        ConfigLayer::parse(
            ConfigSource::CommandArg,
            "musubi.publication.max-files = 10\nmusubi.publication.max-bytes = 32\n",
        )
        .unwrap(),
    );
    settings = settings.with_new_config(config).unwrap();
    let mut node = NodeRepo::open(&repo.repo_path(), &settings).unwrap();
    node.create_join_operation(&format!("musubi: {} joins", repo.machine()))
        .unwrap();
    hive.add(node).unwrap()
}

fn current(repo: &TestRepo) -> CommitId {
    let id = repo.jj(&[
        "--ignore-working-copy",
        "log",
        "--no-graph",
        "-r",
        "@",
        "-T",
        "commit_id",
    ]);
    CommitId::try_from_hex(id.trim()).unwrap()
}

fn held(error: &anyhow::Error) -> bool {
    error.chain().any(|cause| cause.is::<PublicationHeld>())
}

#[test]
fn held_snapshots_receive_other_work_and_cleanup_never_uploads_the_accident() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    let mut hive = Hive::new(&env.root().join("hub"), Backend::GIT).unwrap();
    let a = add(&mut hive, &alpha);
    let b = add(&mut hive, &beta);
    hive.sync_all().unwrap();
    alpha.write_file("README.txt", "README");
    alpha.write_file("AGENTS.md", "keep");
    alpha.write_file("accident", &"x".repeat(64));
    alpha.jj(&["status"]);
    let accidental = current(&alpha);
    alpha.jj(&["commit", "README.txt", "-m", "Keep README"]);
    let readme = alpha.jj(&[
        "--ignore-working-copy",
        "log",
        "--no-graph",
        "-r",
        "@-",
        "-T",
        "commit_id",
    ]);
    std::fs::remove_file(alpha.path().join("accident")).unwrap();
    alpha.jj(&["status"]);
    let before = hive.members[a].uploaded;
    assert!(held(&hive.sync(a).unwrap_err()));
    assert_eq!(hive.members[a].uploaded, before);
    assert_eq!(
        hive.hub
            .store()
            .object_store()
            .missing(std::slice::from_ref(&accidental))
            .unwrap(),
        std::slice::from_ref(&accidental)
    );

    beta.write_file("incoming", "from beta");
    beta.jj(&["commit", "-m", "Incoming from beta"]);
    hive.sync(b).unwrap();
    assert!(held(&hive.sync(a).unwrap_err()));
    assert!(
        alpha
            .jj(&[
                "--ignore-working-copy",
                "log",
                "--no-graph",
                "-r",
                "all()",
                "-T",
                "description"
            ])
            .contains("Incoming from beta")
    );
    assert_eq!(hive.members[a].uploaded, before);
    let node = hive.members[a].adapter.repo_mut();
    let mut cache = PublicationCache::default();
    let outgoing = node.outgoing_publication(&mut cache).unwrap();
    let selected: Vec<_> = outgoing
        .operations
        .iter()
        .map(|operation| operation.id.clone())
        .collect();
    let cleanup = node
        .preview_publication_cleanup(&selected, &mut cache)
        .unwrap();
    assert!(!cleanup.after.held());
    node.apply_publication_cleanup(&selected, &cleanup.token, &mut cache)
        .unwrap();
    hive.sync(a).unwrap();
    hive.sync(b).unwrap();
    assert_eq!(
        hive.hub
            .store()
            .object_store()
            .missing(std::slice::from_ref(&accidental))
            .unwrap(),
        [accidental]
    );
    assert_eq!(
        alpha.jj(&[
            "--ignore-working-copy",
            "log",
            "--no-graph",
            "-r",
            "@-",
            "-T",
            "commit_id"
        ]),
        readme
    );
    assert_eq!(
        std::fs::read_to_string(alpha.path().join("AGENTS.md")).unwrap(),
        "keep"
    );
    assert!(
        beta.jj(&[
            "--ignore-working-copy",
            "log",
            "--no-graph",
            "-r",
            "all()",
            "-T",
            "description"
        ])
        .contains("Keep README")
    );
}

#[test]
fn an_exact_override_sends_held_content_but_does_not_approve_later_snapshots() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut hive = Hive::new(&env.root().join("hub"), Backend::GIT).unwrap();
    let a = add(&mut hive, &repo);
    hive.sync(a).unwrap();
    repo.write_file("large", &"x".repeat(64));
    repo.jj(&["status"]);
    let first = current(&repo);
    assert!(held(&hive.sync(a).unwrap_err()));
    let outgoing = hive.members[a]
        .adapter
        .repo_mut()
        .outgoing_publication(&mut PublicationCache::default())
        .unwrap();
    assert!(approve_publication(&repo.repo_path(), &outgoing, &outgoing.token).unwrap());
    hive.sync(a).unwrap();
    assert!(
        hive.hub
            .store()
            .object_store()
            .missing(&[first])
            .unwrap()
            .is_empty()
    );
    repo.write_file("another", &"y".repeat(64));
    repo.jj(&["status"]);
    let second = current(&repo);
    assert!(held(&hive.sync(a).unwrap_err()));
    assert_eq!(
        hive.hub
            .store()
            .object_store()
            .missing(std::slice::from_ref(&second))
            .unwrap(),
        [second]
    );
    // An explicit commit makes those files intentional history and needs no override.
    repo.jj(&["commit", "-m", "Keep both large files"]);
    hive.sync(a).unwrap();
}

#[test]
fn a_first_join_hold_does_not_turn_unoffered_history_into_legacy_history() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    let mut hive = Hive::new(&env.root().join("hub"), Backend::GIT).unwrap();
    alpha.write_file("base", "base");
    alpha.jj(&["commit", "-m", "base"]);
    let a = add(&mut hive, &alpha);
    hive.sync(a).unwrap();
    beta.write_file("junk", &"x".repeat(64));
    beta.jj(&["status"]);
    let b = add(&mut hive, &beta);
    assert!(held(&hive.sync(b).unwrap_err()));
    std::fs::remove_file(beta.path().join("junk")).unwrap();
    beta.jj(&["status"]);
    let node = hive.members[b].adapter.repo_mut();
    let mut cache = PublicationCache::default();
    let outgoing = node.outgoing_publication(&mut cache).unwrap();
    let selected: Vec<_> = outgoing.operations.iter().map(|op| op.id.clone()).collect();
    let cleanup = node
        .preview_publication_cleanup(&selected, &mut cache)
        .unwrap();
    assert_eq!(cleanup.after.bytes, 0);
    node.apply_publication_cleanup(&selected, &cleanup.token, &mut cache)
        .unwrap();
    hive.sync(b).unwrap();
}
