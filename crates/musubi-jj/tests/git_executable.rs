//! A node runs the git jj is configured to use (`git.executable-path`), for its objects and
//! its remotes, not whatever `git` is on `PATH`.

#![allow(clippy::unwrap_used)]

use std::io;
use std::path::Path;

use jj_lib::backend::CommitId;
use jj_lib::config::ConfigLayer;
use jj_lib::config::ConfigSource;
use jj_lib::settings::UserSettings;
use musubi_jj::git_command::GitError;
use musubi_jj::node::NodeError;
use musubi_jj::node::NodeRepo;
use musubi_jj::objects::ObjectError;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;

/// `repo`'s settings, with `git.executable-path` set to `git`.
fn with_git(repo: &TestRepo, git: &Path) -> UserSettings {
    let settings = repo.settings();
    let mut layer = ConfigLayer::empty(ConfigSource::User);
    layer
        .set_value("git.executable-path", git.to_str().unwrap())
        .unwrap();
    let mut config = settings.config().clone();
    config.add_layer(layer);
    settings.with_new_config(config).unwrap()
}

/// Whether `err` says that there is no git to run.
fn not_found(err: &GitError) -> bool {
    matches!(err, GitError::Run { source, .. } if source.kind() == io::ErrorKind::NotFound)
}

#[test]
fn a_missing_configured_git_is_not_replaced_by_one_on_path() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let missing = env.root().join("no-such-git");
    let mut node = NodeRepo::open(&repo.repo_path(), &with_git(&repo, &missing)).unwrap();
    let err = node.check_complete().unwrap_err();
    assert!(
        matches!(&err, NodeError::Git(err) if not_found(err)),
        "{err:?}"
    );
    let err = node.reconcile_settings().unwrap_err();
    assert!(
        matches!(&err, NodeError::Git(err) if not_found(err)),
        "{err:?}"
    );
    let err = node
        .object_store()
        .unwrap()
        .missing(&[CommitId::from_bytes(&[1; 20])])
        .unwrap_err();
    assert!(
        matches!(&err, ObjectError::Git(err) if not_found(err)),
        "{err:?}"
    );
}

#[cfg(unix)]
#[test]
fn a_configured_git_is_run() {
    use std::fs;
    use std::os::unix::fs::PermissionsExt as _;

    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let ran = env.root().join("ran");
    let wrapper = env.root().join("their-git");
    // Notes what it was asked to do, then does it with the git on `PATH`.
    fs::write(
        &wrapper,
        format!(
            "#!/bin/sh\necho \"$*\" >> '{}'\nexec git \"$@\"\n",
            ran.display()
        ),
    )
    .unwrap();
    fs::set_permissions(&wrapper, fs::Permissions::from_mode(0o755)).unwrap();
    let node = NodeRepo::open(&repo.repo_path(), &with_git(&repo, &wrapper)).unwrap();
    node.join_summary().unwrap();
    node.object_store()
        .unwrap()
        .missing(&[CommitId::from_bytes(&[1; 20])])
        .unwrap();
    let ran = fs::read_to_string(&ran).unwrap();
    for asked in ["config --list", "remote -v", "cat-file --batch-check"] {
        assert!(ran.contains(asked), "{asked} isn't in:\n{ran}");
    }
}
