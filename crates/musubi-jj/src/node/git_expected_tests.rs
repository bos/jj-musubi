//! Check the shipping history walk against `Expected.lean` through the Lean oracle.
//! These are operation-DAG fixtures, not a model of jj's merge-base construction.

use futures::executor::block_on;
use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::op_store::RemoteRef;
use jj_lib::op_store::RemoteRefState;
use jj_lib::ref_name::RefName;
use jj_lib::ref_name::RemoteName;
use musubi_testutil::TestEnv;
use serde_json::Value;
use serde_json::json;

use super::*;
use crate::oracle::Oracle;

const REF: &str = "refs/remotes/origin/x";

struct Entry {
    op: Operation,
    target: RefTarget,
    parents: Vec<usize>,
    known: Option<Option<RefTarget>>,
    recorded: Option<Option<RefTarget>>,
    join: bool,
}

struct HistoryTest {
    _env: TestEnv,
    repo: Arc<ReadonlyRepo>,
    entries: Vec<Entry>,
    oracle: Oracle,
}

impl HistoryTest {
    fn new() -> (Self, [CommitId; 4]) {
        let env = TestEnv::new();
        let repo = env.init_repo("history");
        let loader = RepoLoader::init_from_file_system(
            &repo.settings(),
            &repo.repo_path(),
            &default_backend_factories(),
        )
        .unwrap();
        let repo = block_on(loader.load_at_head(None)).unwrap();
        let tree = repo.store().empty_merged_tree();
        let mut tx = repo.start_transaction();
        let commits = std::array::from_fn(|i| {
            let builder = tx
                .repo_mut()
                .new_commit(vec![repo.store().root_commit_id().clone()], tree.clone())
                .set_description(["side 0", "side 1", "later side", "side 3"][i]);
            let mut committer = builder.committer().clone();
            // Two tied sides, a later side, and a still later removal.
            committer.timestamp.timestamp.0 = [-2000, -2000, 1000, 2000][i];
            block_on(builder.set_committer(committer).write())
                .unwrap()
                .id()
                .clone()
        });
        let repo = block_on(tx.commit("commits for the history walk")).unwrap();
        let root = block_on(
            repo.loader()
                .load_operation(repo.op_store().root_operation_id()),
        )
        .unwrap();
        let root = Entry {
            op: root,
            target: RefTarget::absent(),
            parents: vec![],
            known: None,
            recorded: None,
            join: false,
        };
        (
            Self {
                _env: env,
                repo,
                entries: vec![root],
                oracle: Oracle::spawn(),
            },
            commits,
        )
    }

    fn add(
        &mut self,
        target: &RefTarget,
        parents: &[usize],
        join: bool,
        known: Option<Option<RefTarget>>,
        recorded: Option<Option<RefTarget>>,
    ) -> usize {
        let mut view = self.repo.view().store_view().clone();
        view.remote_views
            .entry(RemoteName::new("origin").to_owned())
            .or_default()
            .bookmarks
            .insert(
                RefName::new("x").to_owned(),
                RemoteRef {
                    target: target.clone(),
                    state: RemoteRefState::Tracked,
                },
            );
        let mut op = self.repo.operation().store_operation().clone();
        op.parents = parents
            .iter()
            .map(|&p| self.entries[p].op.id().clone())
            .collect();
        op.metadata.description = format!("history operation {}", self.entries.len());
        if let Some(value) = &recorded {
            op.metadata.attributes.insert(
                EXPECTED_ATTRIBUTE.to_owned(),
                format_expected(&[(REF.into(), value.clone())]).unwrap(),
            );
        }
        op.view_id = block_on(self.repo.op_store().write_view(&view)).unwrap();
        let id = block_on(self.repo.op_store().write_operation(&op)).unwrap();
        let op = block_on(self.repo.loader().load_operation(&id)).unwrap();
        let index = self.entries.len();
        self.entries.push(Entry {
            op,
            target: target.clone(),
            parents: parents.to_vec(),
            known,
            recorded,
            join,
        });
        index
    }

    /// `override_parents` supplies the historical parents used while recognizing an abandon.
    /// The oracle gets that logical DAG; the Rust walk gets the actual parent callback.
    fn check(
        &mut self,
        head: usize,
        override_parents: Option<(usize, Vec<usize>)>,
    ) -> Option<RefTarget> {
        let mut commits: Vec<_> = self
            .entries
            .iter()
            .flat_map(|entry| {
                std::iter::once(&entry.target)
                    .chain(entry.known.iter().flatten())
                    .chain(entry.recorded.iter().flatten())
            })
            .flat_map(|target| target.iter().flatten().cloned())
            .collect();
        commits.sort();
        commits.dedup();
        // Commit target numbers preserve commit-id order, independently of operation ids.
        let mut targets = vec![RefTarget::absent()];
        targets.extend(commits.into_iter().map(RefTarget::normal));
        for entry in &self.entries {
            if !targets.contains(&entry.target) {
                targets.push(entry.target.clone());
            }
        }
        let id = |target: &RefTarget| targets.iter().position(|t| t == target).unwrap();
        let checkpoint = |value: &Option<Option<RefTarget>>| -> Vec<Option<usize>> {
            value.iter().map(|v| v.as_ref().map(id)).collect()
        };
        let nodes: Vec<_> = self
            .entries
            .iter()
            .enumerate()
            .map(|(i, entry)| {
                let parents = override_parents
                    .as_ref()
                    .filter(|(at, _)| *at == i)
                    .map_or(&entry.parents, |(_, parents)| parents);
                json!({
                    "target": id(&entry.target), "known": checkpoint(&entry.known),
                    "recorded": checkpoint(&entry.recorded),
                    "boundary": entry.join || parents.as_slice() == [0], "parents": parents,
                })
            })
            .collect();
        let resolved: Vec<_> = (0..targets.len())
            .filter(|&i| targets[i].is_resolved())
            .collect();
        let sides: Vec<_> = targets
            .iter()
            .enumerate()
            .map(|(i, target)| {
                let candidates: Vec<_> = target
                    .iter()
                    .step_by(2)
                    .flatten()
                    .map(|commit| {
                        let time = self
                            .repo
                            .store()
                            .get_commit(commit)
                            .unwrap()
                            .committer()
                            .timestamp
                            .timestamp
                            .0;
                        (time, id(&RefTarget::normal(commit.clone())))
                    })
                    .collect();
                json!({"target": i, "candidates": candidates})
            })
            .collect();
        let reply = self.oracle.call(&json!({
            "op": "expected", "nodes": nodes, "resolved": resolved, "sides": sides,
            "head": head,
        }));
        assert_eq!(reply["ok"], true, "oracle refused history: {reply}");
        let model = match &reply["value"] {
            Value::Null => None,
            value => Some(targets[value.as_u64().unwrap() as usize].clone()),
        };
        let known = self
            .entries
            .iter()
            .filter_map(|entry| {
                entry
                    .known
                    .as_ref()
                    .map(|e| ((LocalOp(entry.op.id().clone()), REF.into()), e.clone()))
            })
            .collect();
        let parents = |op: &Operation| -> Result<Option<Vec<Operation>>, NodeError> {
            Ok(override_parents
                .as_ref()
                .filter(|(at, _)| op.id() == self.entries[*at].op.id())
                .map(|(_, ps)| ps.iter().map(|&p| self.entries[p].op.clone()).collect()))
        };
        let history = History {
            known: &known,
            roots: std::slice::from_ref(self.repo.op_store().root_operation_id()),
            is_join: &|op| self.entries.iter().any(|e| e.join && e.op.id() == op.id()),
            parents: &parents,
        };
        let actual = expected(
            self.repo.store(),
            &history,
            &self.entries[head].op,
            RemoteRefSymbol {
                name: RefName::new("x"),
                remote: RemoteName::new("origin"),
            },
            &REF.into(),
            &self.entries[head].target,
        )
        .unwrap();
        assert_eq!(actual, model, "history head {head}");
        actual
    }
}

/// Distinguishes always choosing a side, taking the last unchanged parent, following a
/// join's private parents, forgetting a restored conflict's parent, and treating absent or
/// no expectation as a missing checkpoint. Also checks real three-parent and criss-cross
/// operation DAGs without pretending to prove jj's construction of their merged views.
#[test]
fn expected_history_conforms_to_model() {
    let (mut h, [a, b, c, removed]) = HistoryTest::new();
    let at = |id: &CommitId| RefTarget::normal(id.clone());
    let conflict = RefTarget::from_removes_adds([None], [Some(a.clone()), Some(b.clone())]);
    let three = RefTarget::from_removes_adds(
        [None, None],
        [Some(a.clone()), Some(b.clone()), Some(c.clone())],
    );
    let ra = h.add(&at(&a), &[0], false, None, None);
    let rb = h.add(&at(&b), &[0], false, None, None);
    let rc = h.add(&at(&c), &[0], false, None, None);
    let merge = h.add(&conflict, &[ra, rb], false, None, None);
    let tied = at(std::cmp::max(&a, &b));
    assert_eq!(h.check(merge, None), Some(tied.clone()));
    let restore_a = h.add(&conflict, &[ra], false, None, None);
    let restore_b = h.add(&conflict, &[rb], false, None, None);
    assert_eq!(h.check(restore_a, None), Some(at(&a)));
    assert_eq!(h.check(restore_b, None), Some(at(&b)));
    for (parents, value) in [
        ([restore_a, restore_b], at(&a)),
        ([restore_b, restore_a], at(&b)),
    ] {
        let first = h.add(&conflict, &parents, false, None, None);
        assert_eq!(h.check(first, None), Some(value));
    }
    // Single-parent target changes continue through conflicts, not just unchanged targets.
    let changed = h.add(&three, &[restore_a], false, None, None);
    assert_eq!(h.check(changed, None), Some(at(&a)));
    // Join points and realized joins (whose sole parent is the root) cut private history.
    let private_parent = if a < b { restore_a } else { restore_b };
    let join = h.add(&conflict, &[private_parent], true, None, None);
    let realized_join = h.add(&conflict, &[0], false, None, None);
    assert_eq!(h.check(join, None), Some(tied.clone()));
    let inherited_join = h.add(&conflict, &[join], false, None, None);
    assert_eq!(h.check(inherited_join, None), Some(tied.clone()));
    assert_eq!(h.check(realized_join, None), Some(tied.clone()));
    let absent = h.add(&RefTarget::absent(), &[0], false, None, None);
    let restored_absent = h.add(&conflict, &[absent], false, None, None);
    assert_eq!(h.check(restored_absent, None), Some(RefTarget::absent()));
    for value in [Some(at(&a)), Some(RefTarget::absent()), None] {
        let fixup = h.add(&conflict, &[0], false, None, Some(value.clone()));
        assert_eq!(h.check(fixup, None), value);
        let child = h.add(&conflict, &[fixup], false, None, None);
        assert_eq!(h.check(child, None), value);
    }
    for value in [Some(at(&a)), Some(RefTarget::absent()), None] {
        let cached = h.add(
            &conflict,
            &[0],
            true,
            Some(value.clone()),
            Some(Some(at(&b))),
        );
        assert_eq!(h.check(cached, None), value);
        let child = h.add(&conflict, &[cached], false, None, None);
        assert_eq!(h.check(child, None), value);
    }
    // An unchanged third parent must be considered, too.
    let inherited_third = h.add(&conflict, &[ra, rb, restore_a], false, None, None);
    assert_eq!(h.check(inherited_third, None), Some(at(&a)));
    // Recognition walks logical pre-contraction parents rather than jj's rewritten root.
    let contracted = h.add(&conflict, &[0], false, None, None);
    assert_eq!(
        h.check(contracted, Some((contracted, vec![restored_absent]))),
        Some(RefTarget::absent())
    );
    let child = h.add(&conflict, &[contracted], false, None, None);
    assert_eq!(
        h.check(child, Some((contracted, vec![restored_absent]))),
        Some(RefTarget::absent())
    );
    assert!(
        &c < std::cmp::max(&a, &b),
        "fixture must oppose timestamp and commit-id order"
    );
    let multihead = h.add(&three, &[ra, rb, rc], false, None, None);
    assert_eq!(h.check(multihead, None), Some(at(&c)));
    // Two merges of the same concurrent fetches, then a merge with two merge bases.
    let other_merge = h.add(&conflict, &[rb, ra], false, None, None);
    let criss_cross = h.add(&conflict, &[merge, other_merge], false, None, None);
    assert_eq!(h.check(criss_cross, None), h.check(merge, None));
    // A correct memoized result is transparent, including when reached through a child.
    let cold = h.check(criss_cross, None);
    h.entries[merge].known = Some(h.check(merge, None));
    assert_eq!(h.check(criss_cross, None), cold);
    h.entries[merge].known = None;
    let removed_newest = RefTarget::from_removes_adds([Some(removed)], [Some(a), Some(c.clone())]);
    let removal = h.add(&removed_newest, &[ra, rc], false, None, None);
    assert_eq!(h.check(removal, None), Some(at(&c)));
    let no_sides = RefTarget::from_removes_adds([Some(b)], [None, None]);
    let no_side = h.add(&no_sides, &[ra, rb], false, None, None);
    assert_eq!(h.check(no_side, None), None);
}
