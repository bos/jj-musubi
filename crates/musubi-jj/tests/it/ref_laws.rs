//! jj's ref merge obeys the laws `formal/Musubi/Refs.lean` assumes of it (`RefAlg`):
//! `merge_ref_targets(a, b, b) = a`, `merge_ref_targets(b, b, c) = c` and
//! `merge_ref_targets(a, b, a) = a`, on targets from a small real repository, absent and
//! conflicted ones included. The model's theorems about per-machine refs rest on them, so a
//! jj upgrade that broke one would show here (docs/internals/conformance.md, "Per-machine refs").

#![allow(clippy::unwrap_used)]

use std::collections::BTreeMap;

use hegel::TestCase;
use hegel::generators as gs;
use jj_lib::backend::CommitId;
use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::merge::Merge;
use jj_lib::op_store::RefTarget;
use jj_lib::refs::merge_ref_targets;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use jj_lib::repo::RepoLoader;
use musubi_testutil::TestEnv;
use pollster::FutureExt as _;

/// The repository's commits, by description, and the root: `base`, `one` and `two` in a
/// line from it, and `three` beside them, for targets of every shape. jj settles the three
/// laws on whole values before it looks at any commit, so the graph doesn't decide them.
fn repository() -> (TestEnv, std::sync::Arc<ReadonlyRepo>, Vec<CommitId>) {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    for message in ["base", "one", "two"] {
        repo.jj(&["new", "-m", message]);
    }
    repo.jj(&["new", "@--", "-m", "three"]);
    let template = r#"description.first_line() ++ " " ++ commit_id ++ "\n""#;
    let ids: BTreeMap<String, String> = repo
        .jj(&["log", "--no-graph", "-r", "all()", "-T", template])
        .lines()
        .filter_map(|line| line.split_once(' '))
        .map(|(name, id)| (name.to_owned(), id.to_owned()))
        .collect();
    let loader = RepoLoader::init_from_file_system(
        &repo.settings(),
        &repo.repo_path(),
        &default_backend_factories(),
    )
    .unwrap();
    let loaded = loader.load_at_head().block_on().unwrap();
    let mut commits = vec![loaded.store().root_commit_id().clone()];
    commits.extend(
        ["base", "one", "two", "three"].map(|name| CommitId::try_from_hex(&ids[name]).unwrap()),
    );
    (env, loaded, commits)
}

/// A target: absent, one commit, or a conflict of three or five terms, any of them absent.
fn target(tc: &TestCase, commits: &[CommitId]) -> RefTarget {
    let term = || {
        let n = tc.draw(gs::integers::<usize>().max_value(commits.len()));
        commits.get(n).cloned()
    };
    match tc.draw(gs::integers::<usize>().max_value(2)) {
        0 => RefTarget::resolved(term()),
        sides => Merge::from_vec((0..2 * sides + 1).map(|_| term()).collect::<Vec<_>>()),
    }
}

#[hegel::test(test_cases = 300)]
fn merge_ref_targets_obeys_ref_alg(tc: TestCase) {
    thread_local!(static REPO: (TestEnv, std::sync::Arc<ReadonlyRepo>, Vec<CommitId>) = repository());
    REPO.with(|(_, repo, commits)| {
        let merge = |a: &RefTarget, b: &RefTarget, c: &RefTarget| {
            merge_ref_targets(repo.index(), a, b, c).block_on().unwrap()
        };
        let a = target(&tc, commits);
        let b = target(&tc, commits);
        let c = target(&tc, commits);
        assert_eq!(merge(&a, &b, &b), a, "merge_unchanged_other");
        assert_eq!(merge(&b, &b, &c), c, "merge_unchanged_self");
        assert_eq!(merge(&a, &b, &a), a, "merge_same_change");
    });
}
