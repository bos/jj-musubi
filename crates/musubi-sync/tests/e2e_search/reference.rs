//! The reference that divergence and bookmark and tag conflicts are judged against: the
//! hive's history rebuilt in one jj repository, in which every merge is jj's own.
//!
//! The hub's canonical history is a graph of operations: each machine's commands (and the
//! operations musubi writes for it, such as a forget), and the merges that nodes and `jj`
//! commands made of concurrent ones. The reference takes the same operations, with the same
//! parents, into one jj repository. An operation with one parent is taken as it is, its view
//! the canonical one, while the reference agrees with the hive at its parent. A merge is jj's
//! own merge of the same parents, in the same order, by `RepoLoader::merge_operations`, as
//! concurrent processes on one machine would have it merged. A merge made on a machine, rather
//! than realized there, agrees too where it is jj's merge of the parents as that machine had
//! them, lacking the working-copy commit of another machine's workspace it forgot
//! (`merged_as_made`).
//!
//! Where jj's merge gives what the hive's did, the reference takes the hive's operation
//! itself, so that it goes on agreeing exactly. Where it doesn't, the reference goes its own
//! way from there: each later operation of one parent is applied to the reference's parent as
//! jj applies a concurrent operation, three-way against the hive's parent, and each later
//! merge merges the reference's operations, until an operation brings the two back into
//! agreement, and every later operation descending from where they parted descends from it
//! too. Agreement compares visible commits, bookmarks, tags and remote bookmarks, commits by
//! their contents, change ids and parents rather than their ids, since a commit a merge
//! rebases records when it was made, and without the author's time where jj resets it; a
//! commit of a change new to the operation, like the empty working-copy commit jj makes for an
//! abandoned one, by all but its change id. Workspaces aren't compared: which workspaces a
//! view has is musubi's (docs/internals/design.md, "Copies that go away").
//!
//! Divergence or a conflict that the hive has beyond the reference is musubi's: at its head,
//! and at any merge whose parents the two agree on, where jj's merge is exact. So that the
//! hive's history can stand for one repository's, every machine's realization of each
//! operation must have the hive's view of it, and no operation but a merge may make anything
//! diverge or conflict unless what it did explains it (`explained`).

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs;
use std::hash::Hash;
use std::hash::Hasher as _;
use std::process::Command;
use std::sync::Arc;

use futures::executor::block_on;
use jj_lib::backend::ChangeId;
use jj_lib::backend::CommitId;
use jj_lib::backend::MillisSinceEpoch;
use jj_lib::config::ConfigLayer;
use jj_lib::config::ConfigSource;
use jj_lib::config::StackedConfig;
use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::RefTarget;
use jj_lib::op_store::View;
use jj_lib::operation::Operation;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::RepoLoader;
use jj_lib::settings::UserSettings;
use jj_lib::workspace::Workspace;
use tempfile::TempDir;

use crate::world::World;

/// What the reference needs of a commit, read once.
struct Facts {
    change: ChangeId,
    parents: Vec<CommitId>,
    /// Tree, description and author, but not the author's time.
    content: u64,
    /// The author's time, unless jj resets it in a rewrite.
    author_time: Option<(i64, i32)>,
}

/// A name's target's terms, added and removed, by structural key, each sorted.
type Terms = (Vec<Option<u64>>, Vec<Option<u64>>);

/// A view as agreement compares it, with commits as structural keys (`Reference::keys`).
#[derive(PartialEq, Eq, Debug, Default)]
struct Summary {
    visible: BTreeMap<u64, usize>,
    refs: BTreeMap<String, Terms>,
}

pub struct Reference {
    _dir: TempDir,
    loader: RepoLoader,
    facts: HashMap<CommitId, Facts>,
    /// The commits visible at each set of heads (`heads_key`).
    visible: HashMap<Vec<u8>, Arc<HashSet<CommitId>>>,
    /// The hive's head, as copied into the reference, and the reference's own operation for
    /// it.
    head_copy: Operation,
    head_replay: Operation,
    /// Each operation where the reference parted from the hive or came back to it, oldest
    /// first, for failure messages.
    pub deviations: Vec<String>,
    /// Every rewrite the hive's merges record: the merge, the new commit, and its
    /// predecessors.
    rewrites: Vec<(OperationId, CommitId, Vec<CommitId>)>,
    /// Operations other than merges that made a change diverge or a bookmark or tag
    /// conflict, where nothing the operation did explains it (`explained`), and merges that
    /// did more of either than jj's merge of the same parents.
    pub unexplained: Vec<String>,
    /// The hive's history, but for the root.
    history: Vec<OperationId>,
}

/// Settings for the reference's merges. The user is the tests' user; a seed of its own for
/// the change ids of commits jj makes keeps them clear of the hive's.
fn settings() -> UserSettings {
    let mut config = StackedConfig::with_defaults();
    let text = r#"
user.name = "Test User"
user.email = "test@example.com"
operation.hostname = "reference"
operation.username = "test"
debug.randomness-seed = 9000000000000000000
"#;
    config.add_layer(ConfigLayer::parse(ConfigSource::User, text).unwrap());
    UserSettings::from_config_and_home_dir(config, None).unwrap()
}

fn hash(value: impl Hash) -> u64 {
    let mut hasher = std::hash::DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

impl Reference {
    /// Rebuilds the hub's canonical history, up to its head, in a new repository whose git
    /// store borrows machine 0's objects, and jj's record of their change ids and conflicts.
    pub fn build(world: &World) -> Self {
        let dir = musubi_testutil::tempdir();
        let git = dir.path().join("git");
        let status = Command::new("git")
            .args(["init", "--bare", "-q"])
            .arg(&git)
            .status()
            .unwrap();
        assert!(status.success(), "git init failed");
        let machine = world.fx.repo(0);
        fs::write(
            git.join("objects/info/alternates"),
            format!("{}\n", machine.path().join(".git/objects").display()),
        )
        .unwrap();
        let settings = settings();
        let root = dir.path().join("repo");
        fs::create_dir(&root).unwrap();
        block_on(Workspace::init_external_git(
            &settings,
            &root,
            WorkspaceName::DEFAULT,
            &git,
        ))
        .unwrap();
        let repo_path = root.join(".jj/repo");
        let extra = repo_path.join("store/extra");
        fs::remove_dir_all(&extra).unwrap();
        musubi_testutil::copy_tree(&machine.repo_path().join("store/extra"), &extra);
        let loader =
            RepoLoader::init_from_file_system(&settings, &repo_path, &default_backend_factories())
                .unwrap();

        // The hub's history, parents first.
        let store = world.fx.hive.hub.store();
        let canonical = store.canonical();
        let head = store.head().1.clone();
        let mut ops: BTreeMap<OperationId, op_store::Operation> = BTreeMap::new();
        let mut pending = vec![head.clone()];
        while let Some(id) = pending.pop() {
            if ops.contains_key(&id) || id == *canonical.root_operation_id() {
                continue;
            }
            let op = canonical.read_operation(&id).unwrap();
            pending.extend(op.parents.iter().cloned());
            ops.insert(id, op);
        }
        // Concurrent operations of a generation in the order they ended, which is the same
        // on every run of a case, unlike their ids: jj records each command's arguments,
        // temporary paths and all.
        let mut order: Vec<(u64, MillisSinceEpoch, String, OperationId)> = ops
            .iter()
            .map(|(id, op)| {
                (
                    canonical.generation(id).unwrap(),
                    op.metadata.time.end.timestamp,
                    op.view_id.hex(),
                    id.clone(),
                )
            })
            .collect();
        order.sort();

        let root_op = block_on(loader.root_operation());
        let mut reference = Self {
            _dir: dir,
            loader,
            facts: HashMap::new(),
            visible: HashMap::new(),
            head_copy: root_op.clone(),
            head_replay: root_op.clone(),
            deviations: vec![],
            rewrites: vec![],
            unexplained: vec![],
            history: order.iter().map(|(.., id)| id.clone()).collect(),
        };
        let root_view = canonical
            .read_operation_view(canonical.root_operation_id())
            .unwrap();
        let mut views: HashMap<OperationId, View> =
            HashMap::from([(canonical.root_operation_id().clone(), root_view)]);
        // The operations where the reference went its own way. It goes back to the hive's
        // only at an operation that every later operation descending from them descends
        // from too: otherwise some line of its history would keep commits of its own, and a
        // merge of that line with one that went back would take the hive's copies of them
        // for other commits.
        let mut deviated: BTreeSet<OperationId> = BTreeSet::new();
        let mut children: HashMap<OperationId, Vec<OperationId>> = HashMap::new();
        for (id, op) in &ops {
            for parent in &op.parents {
                children.entry(parent.clone()).or_default().push(id.clone());
            }
        }
        let mut copies: HashMap<OperationId, Operation> = HashMap::new();
        let mut replays: HashMap<OperationId, Operation> = HashMap::new();
        copies.insert(canonical.root_operation_id().clone(), root_op.clone());
        replays.insert(canonical.root_operation_id().clone(), root_op);
        for (.., id) in order {
            let op = &ops[&id];
            let view = canonical.read_view(&op.view_id).unwrap();
            if op.parents.len() > 1 {
                for (new, predecessors) in op.commit_predecessors.iter().flatten() {
                    reference
                        .rewrites
                        .push((id.clone(), new.clone(), predecessors.clone()));
                }
            }
            if let [parent] = op.parents.as_slice()
                && !explained(op)
            {
                let parent_view = views[parent].clone();
                let made: Vec<String> = reference
                    .made_divergent_or_conflicted(&parent_view, &view)
                    .iter()
                    .map(Made::to_string)
                    .collect();
                if !made.is_empty() {
                    reference.unexplained.push(format!(
                        "{}: {}",
                        describe(&id, op),
                        made.join(", ")
                    ));
                }
            }
            let op_store = reference.loader.op_store().clone();
            let copy = op_store::Operation {
                view_id: block_on(op_store.write_view(&view)).unwrap(),
                parents: op.parents.iter().map(|p| copies[p].id().clone()).collect(),
                metadata: op.metadata.clone(),
                commit_predecessors: op.commit_predecessors.clone(),
            };
            let copy_id = block_on(op_store.write_operation(&copy)).unwrap();
            let copy = block_on(reference.loader.load_operation(&copy_id)).unwrap();
            let parents: Vec<&Operation> = op.parents.iter().map(|p| &replays[p]).collect();
            let agreed = op.parents.iter().all(|p| replays[p].id() == copies[p].id());
            let replay = if op.parents.len() < 2 && agreed {
                copy.clone()
            } else {
                let (replayed, how) = if op.parents.len() < 2 {
                    (
                        reference.apply(&copies[&op.parents[0]], &copy, parents[0]),
                        "applied",
                    )
                } else {
                    (reference.merge(parents), "merged")
                };
                let known =
                    reference.changes_of(op.parents.iter().flat_map(|p| [&copies[p], &replays[p]]));
                let ours = reference.summary(&view, &known);
                let theirs = reference.summary(&replayed.view, &known);
                // The same parents on both sides, but a different merge: it may be jj's own,
                // on the machine that made it, of the parents as that machine had them.
                let as_made = if op.parents.len() > 1 && agreed && ours != theirs {
                    reference
                        .merged_as_made(world, &id, &op.parents, &replayed.view, &copies, &views)
                        .filter(|(merged, _)| reference.summary(merged, &known) == ours)
                } else {
                    None
                };
                if op.parents.len() > 1 && agreed && ours != theirs && as_made.is_none() {
                    // What the hive's merge did beyond jj's is musubi's, whatever later
                    // operations make of it.
                    let beyond = reference.beyond(&view, &replayed.view, &known);
                    if !beyond.is_empty() {
                        reference.unexplained.push(format!(
                            "{}: {} beyond jj's merge of the same parents",
                            describe(&id, op),
                            beyond.join(", ")
                        ));
                    }
                }
                if let Some((merged, machine)) = as_made {
                    reference.deviations.push(format!(
                        "{} merged by jj as {} had its parents",
                        describe(&id, op),
                        machine
                    ));
                    if dominates(&ops, &children, &deviated, &id) {
                        copy.clone()
                    } else {
                        // Its own, as where jj's merge agrees but other lines have parted.
                        deviated.insert(id.clone());
                        let parents = op.parents.iter().map(|p| replays[p].id().clone());
                        reference.write_like(&copy, &merged, parents.collect())
                    }
                } else if ours == theirs && dominates(&ops, &children, &deviated, &id) {
                    if !agreed {
                        reference
                            .deviations
                            .push(format!("agrees again at {}", describe(&id, op)));
                    }
                    copy.clone()
                } else if ours == theirs {
                    deviated.insert(id.clone());
                    replayed.op
                } else {
                    let diff = reference.difference(&view, &replayed.view, &known);
                    reference.deviations.push(format!(
                        "{} {how} by jj differs from the hive's: {diff}",
                        describe(&id, op)
                    ));
                    deviated.insert(id.clone());
                    replayed.op
                }
            };
            copies.insert(id.clone(), copy);
            replays.insert(id.clone(), replay);
            views.insert(id, view);
        }
        reference.head_copy = copies[&head].clone();
        reference.head_replay = replays[&head].clone();
        reference
    }

    /// The changes that diverge into more commits in `after` than in `before`, and the
    /// bookmarks and tags that conflict in `after` but not `before`, but for a bookmark on a
    /// commit `after` abandons, which jj moves to the commit's parents, so conflicts if it
    /// was a merge.
    fn made_divergent_or_conflicted(&mut self, before: &View, after: &View) -> Vec<Made> {
        let mut made = vec![];
        let (old, new) = (self.change_counts(before), self.change_counts(after));
        for (change, n) in &new {
            if *n > 1 && old.get(change).copied().unwrap_or(0) < *n {
                made.push(Made::Diverges(change.clone()));
            }
        }
        let visible = self.visible(after);
        let before_refs = refs(before);
        for (name, target) in refs(after) {
            if name.starts_with("remote ") || target.is_resolved() {
                continue;
            }
            let was = before_refs.get(&name);
            if was.is_some_and(|was| !was.is_resolved()) {
                continue;
            }
            let abandoned = was
                .and_then(|was| was.as_normal().cloned())
                .filter(|commit| !visible.contains(commit))
                .is_some_and(|commit| {
                    let parents: BTreeSet<CommitId> =
                        self.facts(&commit).parents.iter().cloned().collect();
                    target.adds().flatten().cloned().collect::<BTreeSet<_>>() == parents
                });
            if !abandoned {
                made.push(Made::Conflicts(name));
            }
        }
        made
    }

    /// How many visible commits each change has in `view`, by jj's change id.
    fn change_counts(&mut self, view: &View) -> BTreeMap<String, usize> {
        let mut counts = BTreeMap::new();
        for id in self.visible(view).iter() {
            *counts
                .entry(self.facts(id).change.reverse_hex())
                .or_default() += 1;
        }
        counts
    }

    /// Whether two of the hive's merges rewrote one commit of `change` the same way: into
    /// commits with the same contents, change id and parents (by structural key). That is the
    /// same rebase done twice, by two merges of the same operations, which the hub's
    /// sequencing exists to prevent. Two commits of a change can also end up alike when jj
    /// rebases two different rewrites of it onto the same parents, or when a command and a
    /// merge each rebase it the same way, as a `jj rebase -r` of its parent and a merge with
    /// a concurrent abandon of that parent do; neither is it.
    pub fn same_rebase_twice(&mut self, change: &str) -> bool {
        let rewrites = self.rewrites.clone();
        let ours: Vec<(OperationId, CommitId, Vec<CommitId>)> = rewrites
            .into_iter()
            .filter(|(_, new, _)| self.facts(new).change.reverse_hex() == change)
            .collect();
        let ids: Vec<CommitId> = ours.iter().map(|(_, new, _)| new.clone()).collect();
        let keys = self.keys(&ids, &|_| true);
        let mut made: HashMap<(CommitId, u64), (OperationId, CommitId)> = HashMap::new();
        for (op, new, predecessors) in ours {
            for predecessor in predecessors {
                match made.get(&(predecessor.clone(), keys[&new])) {
                    Some((other_op, other)) if *other_op != op && *other != new => return true,
                    Some(_) => {}
                    None => {
                        made.insert((predecessor, keys[&new]), (op.clone(), new.clone()));
                    }
                }
            }
        }
        false
    }

    /// Every machine's realization of each of the hive's operations, the operation another
    /// machine made or a merge, has the canonical view's visible commits, bookmarks and tags:
    /// a machine's commands run where the hive's history says they did. A machine's own
    /// operations have the canonical view's bookmarks and tags, and its visible commits but
    /// for those the canonical view keeps visible for other machines (`canonical_view`):
    /// whether keeping them makes anything diverge or conflict is judged against the
    /// canonical parent, as for any operation. Returns those that differ.
    pub fn check_realizations(&mut self, world: &World) -> Vec<String> {
        let store = world.fx.hive.hub.store();
        let canonical = store.canonical();
        let mut differ = vec![];
        for (m, member) in world.fx.hive.members.iter().enumerate() {
            let node = member.adapter.repo();
            let op_store = node.loader().op_store();
            for id in self.history.clone() {
                let Some(local) = node.local_of(&id) else {
                    differ.push(format!(
                        "{} hasn't realized {}",
                        world.machine(m),
                        &id.hex()[..12]
                    ));
                    continue;
                };
                let local_op = block_on(op_store.read_operation(&local)).unwrap();
                let ours = block_on(op_store.read_view(&local_op.view_id)).unwrap();
                let theirs = canonical.read_operation_view(&id).unwrap();
                let realized = local_op
                    .metadata
                    .attributes
                    .contains_key("musubi.canonical");
                let mut why = vec![];
                if realized {
                    if ours.head_ids != theirs.head_ids {
                        why.push("heads differ".to_owned());
                    }
                } else {
                    if !self.visible(&ours).is_subset(&self.visible(&theirs)) {
                        why.push("commits visible here are hidden in the hive".to_owned());
                    }
                }
                if ours.local_bookmarks != theirs.local_bookmarks {
                    why.push("bookmarks differ".to_owned());
                }
                if ours.local_tags != theirs.local_tags {
                    why.push("tags differ".to_owned());
                }
                if !why.is_empty() {
                    differ.push(format!(
                        "{}'s {} {} of {} \"{}\": {}",
                        world.machine(m),
                        if realized { "realization" } else { "operation" },
                        &local.hex()[..12],
                        &id.hex()[..12],
                        local_op
                            .metadata
                            .description
                            .lines()
                            .next()
                            .unwrap_or_default(),
                        why.join(", ")
                    ));
                }
            }
        }
        differ
    }

    /// jj's merge of `parents`, in their order.
    fn merge(&self, parents: Vec<&Operation>) -> Replayed {
        let ops: Vec<Operation> = parents.into_iter().cloned().collect();
        let merged = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            block_on(self.loader.merge_operations(
                ops,
                None,
                Some("reconcile divergent operations"),
                [],
            ))
        }));
        let repo = match merged {
            Ok(Ok((repo, _))) => repo,
            Ok(Err(err)) => panic!("the reference's merge failed: {err}"),
            Err(_) => panic!("jj panicked merging the reference's operations"),
        };
        Replayed::of(&repo)
    }

    /// `op`, made at `base`, applied to `onto` as jj applies a concurrent operation: its
    /// view's changes from `base`, merged three-way, then descendants of what it rewrote
    /// rebased.
    fn apply(&self, base: &Operation, op: &Operation, onto: &Operation) -> Replayed {
        block_on(async {
            let base = self.loader.load_at(base).await.unwrap();
            let other = self.loader.load_at(op).await.unwrap();
            let mut tx = self.loader.load_at(onto).await.unwrap().start_transaction();
            tx.repo_mut().merge(&base, &other).await.unwrap();
            tx.repo_mut().rebase_descendants().await.unwrap();
            let repo = tx
                .write(op.metadata().description.clone())
                .await
                .unwrap()
                .leave_unpublished();
            Replayed::of(&repo)
        })
    }

    /// jj's merge of a merge's two parents as the machine that made it had them, where they
    /// differ from the hive's: that machine's own views lack the working-copy commit of
    /// another machine's workspace it forgot, which `jj workspace forget` abandoned there but
    /// the hive keeps (docs/internals/races.md, "Known jj limitations"). jj's merge there,
    /// by a `jj` command or the machine's daemon, takes the commit for abandoned, as on one
    /// machine, moving bookmarks off it and rebasing work on it. So the parents, and their
    /// base, as the machine's merge found them, go in as the hive has them but with the heads
    /// the machine's views had, and without the workspaces whose commits those lacked, and
    /// only where they lacked nothing else. The merge then gets back the commits jj's merge of
    /// the hive's parents (`canonical`) keeps. `None` where that differs from nothing, or the
    /// merge has several bases.
    fn merged_as_made(
        &mut self,
        world: &World,
        id: &OperationId,
        parents: &[OperationId],
        canonical: &View,
        copies: &HashMap<OperationId, Operation>,
        views: &HashMap<OperationId, View>,
    ) -> Option<(View, &'static str)> {
        // The machine that made the merge, rather than realized it, and the merge there.
        let (m, node, local_op) =
            world
                .fx
                .hive
                .members
                .iter()
                .enumerate()
                .find_map(|(m, member)| {
                    let node = member.adapter.repo();
                    let local = node.local_of(id)?;
                    let local_op = block_on(node.loader().load_operation(&local)).unwrap();
                    let made = !local_op
                        .metadata()
                        .attributes
                        .contains_key("musubi.canonical");
                    made.then_some((m, node, local_op))
                })?;
        let local_parents = block_on(local_op.parents()).unwrap();
        let [first, second] = local_parents.as_slice() else {
            return None;
        };
        // The same parents, in the same order.
        let canonical_parents: Vec<Option<OperationId>> = local_parents
            .iter()
            .map(|parent| node.canonical_of(parent.id()))
            .collect();
        if canonical_parents
            .iter()
            .cloned()
            .collect::<Option<Vec<_>>>()?
            != parents
        {
            return None;
        }
        let bases = block_on(jj_lib::op_walk::closest_common_ancestors(
            vec![first.clone()],
            [second.clone()],
        ))
        .unwrap();
        let [base] = bases.as_slice() else {
            return None;
        };
        let mut kept: HashSet<CommitId> = HashSet::new();
        let mut as_had = vec![];
        for local in [base, first, second] {
            let canonical_id = node.canonical_of(local.id())?;
            let local_view = block_on(local.view()).unwrap().store_view().clone();
            let mut view = views.get(&canonical_id)?.clone();
            let visible = self.visible(&view);
            if !local_view
                .head_ids
                .iter()
                .all(|head| visible.contains(head))
            {
                return None;
            }
            let lacked: HashSet<CommitId> = visible
                .difference(&self.visible(&local_view))
                .cloned()
                .collect();
            let working_copies: HashSet<&CommitId> = view.wc_commit_ids.values().collect();
            if !lacked.iter().all(|commit| working_copies.contains(commit)) {
                return None;
            }
            view.head_ids = local_view.head_ids.clone();
            view.wc_commit_ids
                .retain(|_, commit| !lacked.contains(commit));
            kept.extend(lacked);
            let copy = copies.get(&canonical_id)?;
            as_had.push(self.write_like(copy, &view, copy.parent_ids().to_vec()));
        }
        if kept.is_empty() {
            return None;
        }
        let [base, first, second] = as_had.as_slice() else {
            unreachable!()
        };
        let mut merged = self.apply(base, second, first).view;
        let canonical = self.visible(canonical);
        merged
            .head_ids
            .extend(kept.into_iter().filter(|commit| canonical.contains(commit)));
        Some((merged, world.machine(m)))
    }

    /// `op` with `view` instead, on `parents`.
    fn write_like(&self, op: &Operation, view: &View, parents: Vec<OperationId>) -> Operation {
        let op_store = self.loader.op_store().clone();
        let written = op_store::Operation {
            view_id: block_on(op_store.write_view(view)).unwrap(),
            parents,
            ..op.store_operation().clone()
        };
        let id = block_on(op_store.write_operation(&written)).unwrap();
        block_on(self.loader.load_operation(&id)).unwrap()
    }

    fn facts(&mut self, id: &CommitId) -> &Facts {
        if !self.facts.contains_key(id) {
            let commit = self.loader.store().get_commit(id).unwrap();
            let author = commit.author();
            let content = hash((
                format!("{:?}", commit.tree_ids()),
                commit.description(),
                &author.name,
                &author.email,
            ));
            let facts = Facts {
                change: commit.change_id().clone(),
                parents: commit.parent_ids().to_vec(),
                content,
                // jj resets the author's time when it rewrites a discardable commit, one
                // that is empty with no description, as it rebases a working copy.
                author_time: (!commit.description().is_empty())
                    .then_some((author.timestamp.timestamp.0, author.timestamp.tz_offset)),
            };
            self.facts.insert(id.clone(), facts);
        }
        &self.facts[id]
    }

    /// The commits visible in `view`, the root's aside.
    fn visible(&mut self, view: &View) -> Arc<HashSet<CommitId>> {
        let key = heads_key(view);
        if let Some(found) = self.visible.get(&key) {
            return found.clone();
        }
        let root = self.loader.store().root_commit_id().clone();
        let mut found = HashSet::new();
        let mut pending: Vec<CommitId> = view.head_ids.iter().cloned().collect();
        while let Some(id) = pending.pop() {
            if id == root || !found.insert(id.clone()) {
                continue;
            }
            pending.extend(self.facts(&id).parents.clone());
        }
        let found = Arc::new(found);
        self.visible.insert(key, found.clone());
        found
    }

    /// The changes visible at any of `ops`.
    fn changes_of<'a>(&mut self, ops: impl Iterator<Item = &'a Operation>) -> HashSet<ChangeId> {
        let mut changes = HashSet::new();
        for op in ops {
            let view = block_on(self.loader.op_store().read_view(op.view_id())).unwrap();
            for id in self.visible(&view).iter() {
                changes.insert(self.facts(id).change.clone());
            }
        }
        changes
    }

    /// Structural keys for `ids` and their ancestors: a commit's change id (unless the
    /// change is new, not `known`), contents, author time (likewise), and parents' keys.
    fn keys(
        &mut self,
        ids: &[CommitId],
        known: &dyn Fn(&ChangeId) -> bool,
    ) -> HashMap<CommitId, u64> {
        let root = self.loader.store().root_commit_id().clone();
        let mut keys: HashMap<CommitId, u64> = HashMap::from([(root, 0)]);
        let mut pending: Vec<CommitId> = ids.to_vec();
        while let Some(id) = pending.last().cloned() {
            if keys.contains_key(&id) {
                pending.pop();
                continue;
            }
            let parents = self.facts(&id).parents.clone();
            let missing: Vec<CommitId> = parents
                .iter()
                .filter(|p| !keys.contains_key(*p))
                .cloned()
                .collect();
            if !missing.is_empty() {
                pending.extend(missing);
                continue;
            }
            pending.pop();
            let facts = self.facts(&id);
            let new = !known(&facts.change);
            let key = hash((
                (!new).then(|| facts.change.clone()),
                facts.content,
                facts.author_time.filter(|_| !new),
                parents.iter().map(|p| keys[p]).collect::<Vec<_>>(),
            ));
            keys.insert(id, key);
        }
        keys
    }

    fn summary(&mut self, view: &View, known: &HashSet<ChangeId>) -> Summary {
        let visible: Vec<CommitId> = self.visible(view).iter().cloned().collect();
        let named: Vec<CommitId> = refs(view)
            .values()
            .flat_map(|target| target.iter().flatten().cloned())
            .collect();
        let all: Vec<CommitId> = visible.iter().chain(&named).cloned().collect();
        let keys = self.keys(&all, &|change| known.contains(change));
        let mut summary = Summary::default();
        for id in &visible {
            *summary.visible.entry(keys[id]).or_default() += 1;
        }
        // A conflict's terms in any order are the same conflict: jj's merges order them by
        // the order they merge operations in.
        let key = |id: &Option<CommitId>| id.as_ref().map(|id| keys[id]);
        for (name, target) in refs(view) {
            let mut adds: Vec<Option<u64>> = target.adds().map(key).collect();
            let mut removes: Vec<Option<u64>> = target.removes().map(key).collect();
            adds.sort();
            removes.sort();
            summary.refs.insert(name, (adds, removes));
        }
        summary
    }

    /// How `view`, the hive's, differs from `replayed`, the reference's, for messages.
    fn difference(&mut self, view: &View, replayed: &View, known: &HashSet<ChangeId>) -> String {
        let ours = self.summary(view, known);
        let theirs = self.summary(replayed, known);
        let mut out = vec![];
        let mut described = |side: &str, view: &View, summary: &Summary, other: &Summary| {
            let visible: Vec<CommitId> = self.visible(view).iter().cloned().collect();
            let keys = self.keys(&visible, &|change| known.contains(change));
            let mut only: Vec<String> = visible
                .iter()
                .filter(|id| {
                    summary.visible.get(&keys[*id]) > other.visible.get(&keys[*id]).or(Some(&0))
                })
                .map(|id| {
                    let workspaces: Vec<&str> = view
                        .wc_commit_ids
                        .iter()
                        .filter(|(_, wc)| *wc == id)
                        .map(|(name, _)| name.as_str())
                        .collect();
                    let commit = self.loader.store().get_commit(id).unwrap();
                    let parents: Vec<String> = commit
                        .parent_ids()
                        .iter()
                        .map(|p| p.hex()[..12].to_owned())
                        .collect();
                    format!(
                        "{} ({}, on {}, {:?}{})",
                        &id.hex()[..12],
                        &self.facts(id).change.reverse_hex()[..12],
                        parents.join("+"),
                        commit.description().lines().next().unwrap_or_default(),
                        if workspaces.is_empty() {
                            String::new()
                        } else {
                            format!(", working copy of {}", workspaces.join(","))
                        }
                    )
                })
                .collect();
            only.sort();
            if !only.is_empty() {
                out.push(format!("visible only {side}: {}", only.join(", ")));
            }
        };
        described("in the hive", view, &ours, &theirs);
        described("in jj's", replayed, &theirs, &ours);
        let names: BTreeSet<&String> = ours.refs.keys().chain(theirs.refs.keys()).collect();
        let (view_refs, replayed_refs) = (refs(view), refs(replayed));
        for name in names {
            if ours.refs.get(name) != theirs.refs.get(name) {
                out.push(format!(
                    "{name}: {} in the hive, {} in jj's",
                    show_target(view_refs.get(name)),
                    show_target(replayed_refs.get(name))
                ));
            }
        }
        out.join("; ")
    }

    /// What `hive`, a view of the hive's, has beyond `jj`, the reference's view where the
    /// two had the same operations: changes that diverge into commits `jj` doesn't have as
    /// many of, as change ids name them, and bookmarks and tags conflicted with terms `jj`'s
    /// targets lack. Commits are compared by structural key, those of changes not `known`
    /// by all but their change ids.
    fn beyond(&mut self, hive: &View, jj: &View, known: &HashSet<ChangeId>) -> Vec<String> {
        let (hive_visible, jj_visible) = (self.visible(hive), self.visible(jj));
        let (hive_refs, jj_refs) = (refs(hive), refs(jj));
        let all: Vec<CommitId> = hive_visible
            .iter()
            .chain(jj_visible.iter())
            .chain(
                hive_refs
                    .values()
                    .chain(jj_refs.values())
                    .flat_map(|target| target.iter().flatten()),
            )
            .cloned()
            .collect();
        let keys = self.keys(&all, &|change| known.contains(change));
        let mut by_change =
            |visible: &HashSet<CommitId>| -> BTreeMap<String, BTreeMap<u64, usize>> {
                let mut by_change: BTreeMap<String, BTreeMap<u64, usize>> = BTreeMap::new();
                for id in visible {
                    let change = self.facts(id).change.reverse_hex();
                    *by_change
                        .entry(change)
                        .or_default()
                        .entry(keys[id])
                        .or_default() += 1;
                }
                by_change
            };
        let (hive_changes, jj_changes) = (by_change(&hive_visible), by_change(&jj_visible));
        let within = |ours: &BTreeMap<u64, usize>, theirs: Option<&BTreeMap<u64, usize>>| {
            ours.iter()
                .all(|(key, n)| theirs.and_then(|t| t.get(key)).is_some_and(|m| m >= n))
        };
        let mut beyond = vec![];
        for (change, commits) in &hive_changes {
            if commits.values().sum::<usize>() > 1 && !within(commits, jj_changes.get(change)) {
                beyond.push(format!("{change} diverges"));
            }
        }
        let terms = |target: &RefTarget| -> BTreeMap<u64, usize> {
            let mut terms = BTreeMap::new();
            // Added terms and removed ones apart, absent ones included.
            for (i, id) in target.iter().enumerate() {
                let key = hash((i % 2, id.as_ref().map(|id| keys[id])));
                *terms.entry(key).or_default() += 1;
            }
            terms
        };
        for (name, target) in &hive_refs {
            if name.starts_with("remote ") || target.is_resolved() {
                continue;
            }
            let theirs = jj_refs
                .get(name)
                .filter(|target| !target.is_resolved())
                .map(terms);
            if !within(&terms(target), theirs.as_ref()) {
                beyond.push(format!("{name} conflicts"));
            }
        }
        beyond
    }

    /// What the hive's head has beyond the reference's (`beyond`): divergence and conflicts
    /// jj wouldn't make of the same operations. Changes visible at only one of them count as
    /// new, as jj's and musubi's working-copy commits for an abandoned one are.
    pub fn beyond_jj(&mut self) -> Vec<String> {
        let read = |op: &Operation| block_on(self.loader.op_store().read_view(op.view_id()));
        let (hive, jj) = (
            read(&self.head_copy).unwrap(),
            read(&self.head_replay).unwrap(),
        );
        let changes = |reference: &mut Self, view: &View| -> HashSet<ChangeId> {
            let visible = reference.visible(view);
            visible
                .iter()
                .map(|id| reference.facts(id).change.clone())
                .collect()
        };
        let (ours, theirs) = (changes(self, &hive), changes(self, &jj));
        let known: HashSet<ChangeId> = ours.intersection(&theirs).cloned().collect();
        self.beyond(&hive, &jj, &known)
    }
}

/// Whether every operation descending from one of `deviated` is an ancestor or a
/// descendant of `id` (or `id`), in the history `ops` with `children`.
fn dominates(
    ops: &BTreeMap<OperationId, op_store::Operation>,
    children: &HashMap<OperationId, Vec<OperationId>>,
    deviated: &BTreeSet<OperationId>,
    id: &OperationId,
) -> bool {
    if deviated.is_empty() {
        return true;
    }
    let walk = |start: &OperationId, next: &dyn Fn(&OperationId) -> Vec<OperationId>| {
        let mut found: HashSet<OperationId> = HashSet::new();
        let mut pending = vec![start.clone()];
        while let Some(op) = pending.pop() {
            if found.insert(op.clone()) {
                pending.extend(next(&op));
            }
        }
        found
    };
    let parents = |op: &OperationId| ops.get(op).map_or(vec![], |op| op.parents.clone());
    let kids = |op: &OperationId| children.get(op).cloned().unwrap_or_default();
    let related: HashSet<OperationId> = walk(id, &parents)
        .into_iter()
        .chain(walk(id, &kids))
        .collect();
    deviated
        .iter()
        .all(|d| walk(d, &kids).iter().all(|op| related.contains(op)))
}

/// What a single operation did that would make a change diverge or a name conflict, as
/// `Reference::made_divergent_or_conflicted` finds it.
enum Made {
    Diverges(String),
    Conflicts(String),
}

impl std::fmt::Display for Made {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Diverges(change) => write!(f, "{change} diverges"),
            Self::Conflicts(name) => write!(f, "{name} conflicts"),
        }
    }
}

/// Whether what `op` did explains `made`, as jj would do it on one machine: a fetch brings
/// back a pushed commit beside its rewrite, or conflicts a bookmark with the remote's; an
/// undo, redo, restore or revert brings back an older view; and an import of git refs takes
/// what `.git` has where jj's record of it differs, which happens without anyone moving a
/// branch, as when an undo restores an older record and a conflicted bookmark can't be
/// exported over it. An import of git's HEAD likewise moves the working copy onto what
/// `.git`'s HEAD has, bringing back a rewritten commit there, as after a command at an older
/// operation wrote HEAD and jj's merge with the operations since conflicted its record of it.
/// (Whether musubi keeps those records as jj would is for the per-machine refs' conformance
/// test, docs/internals/conformance.md, and the check of every import, `imports`.) Anything
/// else that makes a change diverge or a name conflict on its own is musubi's: an operation of
/// its own, or a realization or canonical form that differs from what the machine did.
fn explained(op: &op_store::Operation) -> bool {
    let description = op.metadata.description.as_str();
    [
        "undo",
        "redo",
        "restore to operation",
        "revert operation",
        "fetch from git remote",
        "import git refs",
        "import git head",
    ]
    .iter()
    .any(|prefix| description.starts_with(prefix))
}

/// An operation the reference made, with its view.
struct Replayed {
    op: Operation,
    view: View,
}

impl Replayed {
    fn of(repo: &Arc<ReadonlyRepo>) -> Self {
        Self {
            op: repo.operation().clone(),
            view: repo.view().store_view().clone(),
        }
    }
}

/// A view's heads, for caching what's visible in it.
fn heads_key(view: &View) -> Vec<u8> {
    let mut heads: Vec<&CommitId> = view.head_ids.iter().collect();
    heads.sort();
    heads
        .into_iter()
        .flat_map(|head| head.as_bytes())
        .copied()
        .collect()
}

/// Every bookmark, tag and remote bookmark (outside the `git` pseudo-remote, which
/// canonical views don't have), as `bookmark <name>`, `tag <name>` and
/// `remote <name>@<remote> <state>`.
fn refs(view: &View) -> BTreeMap<String, RefTarget> {
    let mut refs = BTreeMap::new();
    for (name, target) in &view.local_bookmarks {
        refs.insert(format!("bookmark {}", name.as_str()), target.clone());
    }
    for (name, target) in &view.local_tags {
        refs.insert(format!("tag {}", name.as_str()), target.clone());
    }
    for (remote, remote_view) in &view.remote_views {
        for (name, remote_ref) in &remote_view.bookmarks {
            refs.insert(
                format!(
                    "remote {}@{} {:?}",
                    name.as_str(),
                    remote.as_str(),
                    remote_ref.state
                ),
                remote_ref.target.clone(),
            );
        }
    }
    refs
}

fn show_target(target: Option<&RefTarget>) -> String {
    match target {
        None => "absent".to_owned(),
        Some(target) => target
            .iter()
            .map(|id| {
                id.as_ref()
                    .map_or("-".to_owned(), |id| id.hex()[..12].to_owned())
            })
            .collect::<Vec<_>>()
            .join(","),
    }
}

/// A canonical operation, for messages: its description, id and machine.
fn describe(id: &OperationId, op: &op_store::Operation) -> String {
    format!(
        "\"{}\" ({} on {})",
        op.metadata.description.lines().next().unwrap_or_default(),
        &id.hex()[..12],
        op.metadata.hostname
    )
}
