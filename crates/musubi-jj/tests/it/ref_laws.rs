//! jj's ref merge obeys the laws `formal/Musubi/Refs.lean` assumes of it (`RefAlg`):
//! `merge_ref_targets(a, b, b) = a`, `merge_ref_targets(b, b, c) = c` and
//! `merge_ref_targets(a, b, a) = a`, on targets that may be absent or conflicted. The model's
//! theorems about per-machine refs rest on them, so a jj upgrade that broke one would show here
//! (docs/internals/conformance.md, "Per-machine refs").

#![allow(clippy::unwrap_used)]

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

/// jj settles these laws before it reads the index. An empty repository provides the
/// index its API needs; the targets need no commits or history behind them.
fn merge(a: &RefTarget, b: &RefTarget, c: &RefTarget) -> RefTarget {
    thread_local!(static REPO: (TestEnv, std::sync::Arc<ReadonlyRepo>) = {
        let env = TestEnv::new();
        let repo = env.init_repo("alpha");
        let loader = RepoLoader::init_from_file_system(
            &repo.settings(),
            &repo.repo_path(),
            &default_backend_factories(),
        )
        .unwrap();
        let loaded = loader.load_at_head(None).block_on().unwrap();
        (env, loaded)
    });
    REPO.with(|(_, repo)| merge_ref_targets(repo.index(), a, b, c).block_on().unwrap())
}

/// A target: absent, one commit, or a conflict of three or five terms, any of them absent.
fn target(tc: &TestCase) -> RefTarget {
    let term = || {
        let n = tc.draw(gs::integers::<u8>().max_value(5));
        (n < 5).then(|| CommitId::from_bytes(&[n; 20]))
    };
    match tc.draw(gs::integers::<usize>().max_value(2)) {
        0 => RefTarget::resolved(term()),
        sides => Merge::from_vec((0..2 * sides + 1).map(|_| term()).collect::<Vec<_>>()),
    }
}

#[hegel::test(test_cases = 300)]
fn merge_ref_targets_obeys_ref_alg(tc: TestCase) {
    let a = target(&tc);
    let b = target(&tc);
    let c = target(&tc);
    assert_eq!(merge(&a, &b, &b), a, "merge_unchanged_other");
    assert_eq!(merge(&b, &b, &c), c, "merge_unchanged_self");
    assert_eq!(merge(&a, &b, &a), a, "merge_same_change");
}

/// A fetch beside a realized conflict can cancel both present terms, leaving absence,
/// which neither side had. The refs conformance test must use that resolved value itself.
#[test]
fn a_fetch_can_resolve_a_conflict_to_neither_side() {
    let base = CommitId::from_bytes(&[1; 20]);
    let one = CommitId::from_bytes(&[2; 20]);
    let conflict = Merge::from_vec(vec![Some(base.clone()), Some(one.clone()), None]);
    assert_eq!(
        merge(&conflict, &RefTarget::normal(base), &RefTarget::normal(one)),
        RefTarget::absent(),
    );
}
