//! musubi merges each machine's working copies three-way as jj merges a workspace's
//! (`workspaces::merge_working_copy`). jj's own rule is private to jj-lib, so this has jj
//! merge concurrent operations, for every combination of changes, and checks the two agree.

#![allow(clippy::unwrap_used)]

use std::sync::Arc;

use jj_lib::backend::CommitId;
use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::ref_name::WorkspaceNameBuf;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use jj_lib::repo::RepoLoader;
use musubi_jj::workspaces::merge_working_copy;
use musubi_testutil::TestEnv;
use pollster::FutureExt as _;

#[test]
fn workspace_merge_matches_jj() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let commits: Vec<CommitId> = ["A", "B", "C"]
        .map(|message| {
            repo.jj(&["new", "--no-edit", "root()", "-m", message]);
            let hex = repo.jj(&[
                "log",
                "--no-graph",
                "-r",
                &format!("description(exact:\"{message}\n\")"),
                "-T",
                "commit_id",
            ]);
            CommitId::try_from_hex(hex.trim()).unwrap()
        })
        .into();
    let loader = RepoLoader::init_from_file_system(
        &repo.settings(),
        &repo.repo_path(),
        &default_backend_factories(),
    )
    .unwrap();
    let name = WorkspaceNameBuf::from("w");
    let set = |from: &Arc<ReadonlyRepo>, value: Option<&CommitId>, side: &str| {
        let mut tx = from.start_transaction();
        match value {
            Some(commit) => tx
                .repo_mut()
                .set_wc_commit(name.clone(), commit.clone())
                .unwrap(),
            None if tx.repo().view().get_wc_commit_id(&name).is_some() => {
                tx.repo_mut().remove_workspace(&name).block_on().unwrap();
            }
            None => {}
        }
        tx.commit(format!("set w, {side}")).block_on().unwrap()
    };
    let choices: Vec<Option<&CommitId>> =
        [None].into_iter().chain(commits.iter().map(Some)).collect();
    for &base in &choices {
        for &ours in &choices {
            for &theirs in &choices {
                let base_repo = set(&loader.load_at_head(None).block_on().unwrap(), base, "base");
                // Described apart, so that two sides setting the same are still two
                // operations: the settings' operation time is the same for both.
                let one = set(&base_repo, ours, "ours");
                set(&base_repo, theirs, "theirs");
                let merged = loader.load_at_head(None).block_on().unwrap();
                // jj merges with the merge operation's first parent as its own side.
                let (first, second) = if merged.operation().parent_ids()[0] == *one.op_id() {
                    (ours, theirs)
                } else {
                    (theirs, ours)
                };
                assert_eq!(
                    merged.view().get_wc_commit_id(&name),
                    merge_working_copy(first, base, second),
                    "base {base:?}, sides {first:?} and {second:?}"
                );
            }
        }
    }
}
