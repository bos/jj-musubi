//! Classify each history entry, check it against its recorded source, and compare jj's replay
//! of it with the hive's.
//!
//! Source-recorded commands and retained operations have payload checks before replay. A merge
//! unlike jj's merge of the same parents is a deviation, and fails only for what it has beyond
//! jj's. Structural equality can rejoin the hive only across the full deviation frontier.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use futures::executor::block_on;
use jj_lib::backend::CommitId;
use jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
use jj_lib::op_store;
use jj_lib::op_store::View;
use jj_lib::operation::Operation;
use musubi_jj::op_id::CanonicalOp;

use super::rewrites::{MergeRewrite, Origin, brought_by_merge};
use super::{Made, Reference, describe, dominates, explained};
use crate::identity::SourceKey;
use crate::world::{CommandSnapshot, RetainedOperation, World, merge_key};

/// Source-recorded commands are checked as commands even if an abandon expanded their
/// parent frontier. A retained operation supplies additional, independent payload evidence.
#[derive(Clone, Copy)]
enum PayloadSource<'a> {
    Command(&'a CommandSnapshot),
    Merge,
    Operation,
}

/// One canonical operation with the evidence captured before replication changed it.
pub(super) struct HistoryEntry<'a> {
    id: &'a CanonicalOp,
    op: &'a op_store::Operation,
    parents: Vec<CanonicalOp>,
    view: View,
    source: PayloadSource<'a>,
    retained: Option<&'a RetainedOperation>,
}

impl<'a> HistoryEntry<'a> {
    pub(super) fn new(
        world: &'a World,
        id: &'a CanonicalOp,
        op: &'a op_store::Operation,
        view: View,
    ) -> Self {
        let parents = CanonicalOp::parents_of(op);
        let command = world.evidence.commands.get(&merge_key(op));
        let retained = world.evidence.kept_operations.get(&merge_key(op));
        let source = match command {
            Some(command) => PayloadSource::Command(command),
            None if parents.len() > 1 => PayloadSource::Merge,
            None => PayloadSource::Operation,
        };
        Self {
            id,
            op,
            parents,
            view,
            source,
            retained,
        }
    }

    fn command(&self) -> Option<&CommandSnapshot> {
        match self.source {
            PayloadSource::Command(command) => Some(command),
            _ => None,
        }
    }

    fn is_merge(&self) -> bool {
        matches!(self.source, PayloadSource::Merge)
    }
}

/// Copied canonical history and its independent jj replay, advanced together.
/// `deviated` prevents joining back while a parallel replay branch still has its own commits.
pub(super) struct ReplayHistory<'a> {
    operations: &'a BTreeMap<CanonicalOp, op_store::Operation>,
    children: HashMap<CanonicalOp, Vec<CanonicalOp>>,
    copies: HashMap<CanonicalOp, Operation>,
    replays: HashMap<CanonicalOp, Operation>,
    views: HashMap<CanonicalOp, View>,
    deviated: BTreeSet<CanonicalOp>,
}

impl<'a> ReplayHistory<'a> {
    pub(super) fn new(
        operations: &'a BTreeMap<CanonicalOp, op_store::Operation>,
        root: &CanonicalOp,
        root_op: Operation,
        root_view: View,
    ) -> Self {
        let views = HashMap::from([(root.clone(), root_view)]);
        let deviated = BTreeSet::new();
        let mut children: HashMap<CanonicalOp, Vec<CanonicalOp>> = HashMap::new();
        for (id, op) in operations {
            for parent in CanonicalOp::parents_of(op) {
                children.entry(parent).or_default().push(id.clone());
            }
        }
        let copies = HashMap::from([(root.clone(), root_op.clone())]);
        let replays = HashMap::from([(root.clone(), root_op)]);
        Self {
            operations,
            children,
            copies,
            replays,
            views,
            deviated,
        }
    }

    /// `id` and every operation of the hive's history it descends from, by source key
    /// without operation ids, and whether a user's command made each, as `world` recorded
    /// it (`brought_to`).
    fn history_of(&self, world: &World, id: &CanonicalOp) -> HashMap<SourceKey, Origin> {
        let mut seen = HashSet::new();
        let mut history = HashMap::new();
        let mut pending = vec![id.clone()];
        while let Some(op) = pending.pop() {
            if let Some(operation) = self.operations.get(&op)
                && seen.insert(op)
            {
                let key = merge_key(operation);
                let origin = if world.evidence.commands.contains_key(&key) {
                    Origin::Command
                } else {
                    Origin::Other
                };
                // Two operations with one key: unless both are commands, neither counts as one.
                history
                    .entry(key.without_op_ids())
                    .and_modify(|known| {
                        if origin != Origin::Command {
                            *known = Origin::Other;
                        }
                    })
                    .or_insert(origin);
                pending.extend(CanonicalOp::parents_of(operation));
            }
        }
        history
    }

    fn can_rejoin(&self, id: &CanonicalOp) -> bool {
        dominates(self.operations, &self.children, &self.deviated, id)
    }

    pub(super) fn record(&mut self, entry: HistoryEntry<'_>, copy: Operation, replay: Operation) {
        self.copies.insert(entry.id.clone(), copy);
        self.replays.insert(entry.id.clone(), replay);
        self.views.insert(entry.id.clone(), entry.view);
    }

    pub(super) fn heads(&self, head: &CanonicalOp) -> (Operation, Operation) {
        (self.copies[head].clone(), self.replays[head].clone())
    }
}

impl Reference {
    /// Check the payload against its independently recorded sources before constructing
    /// any replay. Retained operations and commands can both supply evidence for one entry.
    pub(super) fn validate_source(
        &mut self,
        world: &World,
        entry: &HistoryEntry<'_>,
        history: &ReplayHistory<'_>,
    ) {
        let views = &history.views;
        let (id, op, parents, view) = (entry.id, entry.op, &entry.parents, &entry.view);
        let kept = entry.retained;
        let command = entry.command();
        let is_merge = entry.is_merge();
        let source_copy = command.map(|command| command.copy.as_str()).or_else(|| {
            kept.filter(|source| source.native)
                .map(|source| source.copy.as_str())
        });
        let protected = source_copy
            .map(|copy| {
                self.retained_foreign_targets(
                    world,
                    copy,
                    command.and_then(|c| c.input.as_ref()),
                    op,
                    view,
                )
            })
            .unwrap_or_default();
        let with_foreign = |native: &View| {
            let mut expected = native.clone();
            expected.head_ids.extend(protected.iter().cloned());
            expected
        };
        if is_merge && op.commit_predecessors.iter().flatten().next().is_some() {
            let shown: Vec<_> = parents.iter().map(|p| self.visible(&views[p])).collect();
            let histories: Vec<_> = parents
                .iter()
                .map(|p| history.history_of(world, p))
                .collect();
            for (new, predecessors) in op.commit_predecessors.iter().flatten() {
                // A merge `jj op abandon` gave other parents rewrote for its original ones.
                let brought = brought_by_merge(predecessors, kept.is_some(), &shown, &histories);
                self.rewrites.push(MergeRewrite {
                    operation: id.0.clone(),
                    new: new.clone(),
                    predecessors: predecessors.clone(),
                    brought,
                });
            }
        }
        // A `jj op abandon` survivor keeps its original view, whatever its parents
        // are now: it must be that source view, as the
        // realizations are held to theirs (`check_realizations`).
        if let Some(replaced) = kept
            && let Some(why) = self.unlike_replaced(&replaced.view, replaced.realized, view)
        {
            self.unexplained.push(format!(
                "{}, which jj op abandon rewrote, keeping its view: {why}",
                describe(id, op)
            ));
        }
        if let Some(source) = kept
            && let Some(parent) = &source.parent
            && command.is_none()
            && !source.realized
            && !explained(op)
        {
            let made: Vec<String> = self
                .made_divergent_or_conflicted(parent, &source.view)
                .iter()
                .map(Made::to_string)
                .collect();
            if !made.is_empty() {
                self.unexplained.push(format!(
                    "{} introduced in its original source: {}",
                    describe(id, op),
                    made.join(", ")
                ));
            }
        }
        if let Some(source) = kept {
            let made: Vec<String> = self
                .made_divergent_or_conflicted(&with_foreign(&source.view), view)
                .iter()
                .map(Made::to_string)
                .collect();
            if !made.is_empty() {
                self.unexplained.push(format!(
                    "{} differs from its retained source: {}",
                    describe(id, op),
                    made.join(", ")
                ));
            }
        }
        if let Some(command) = command
            && let Some(why) = self.unlike_replaced(&command.made, false, view)
        {
            self.unexplained.push(format!(
                "{}, which is a source-recorded command: {why}",
                describe(id, op)
            ));
        }
        if let Some(command) = command {
            let mut remotes = command.made.remote_views.clone();
            remotes.remove(REMOTE_NAME_FOR_LOCAL_GIT_REPO);
            if remotes != view.remote_views {
                self.unexplained.push(format!(
                    "{}, which is a source-recorded command: remote refs differ",
                    describe(id, op)
                ));
            }
        }
        if let Some(command) = command
            && !explained(op)
        {
            let made =
                self.unexplained_command_changes(&command.base, &with_foreign(&command.made), view);
            if !made.is_empty() {
                self.unexplained
                    .push(format!("{}: {}", describe(id, op), made.join(", ")));
            }
        }
        if let [parent] = parents.as_slice()
            && command.is_none()
            && !explained(op)
            && kept.is_none()
        {
            let parent_view = views[parent].clone();
            let made: Vec<String> = self
                .made_divergent_or_conflicted(&parent_view, view)
                .iter()
                .map(Made::to_string)
                .collect();
            if !made.is_empty() {
                self.unexplained
                    .push(format!("{}: {}", describe(id, op), made.join(", ")));
            }
        }
    }

    /// The working copies of other copies' workspaces that the canonical view `view` of `op`
    /// keeps visible where `copy`'s own operation hid them: musubi keeps another machine's
    /// working copy visible even when a local operation drops its alias or rewrites it. Only
    /// a target bound to the same workspace in one of the operation's inputs, visible there,
    /// and still bound to it in `view` counts.
    fn retained_foreign_targets(
        &mut self,
        world: &World,
        copy: &str,
        command_input: Option<&CanonicalOp>,
        op: &op_store::Operation,
        view: &View,
    ) -> BTreeSet<CommitId> {
        let mut inputs = CanonicalOp::parents_of(op);
        inputs.extend(command_input.cloned());
        inputs.sort();
        inputs.dedup();
        let mut targets = BTreeSet::new();
        for input in inputs {
            let Some(source) = world.fx.hive.members.iter().find_map(|member| {
                let store = member.adapter.repo().canonical_store();
                let input = store
                    .has_operation(&input)
                    .then(|| store.read_operation(&input).ok())??;
                store.read_view(&input.view_id).ok()
            }) else {
                continue;
            };
            let visible = self.visible(&source);
            for (name, target) in &source.wc_commit_ids {
                let foreign = name
                    .as_str()
                    .split_once('/')
                    .is_some_and(|(owner, _)| owner != copy);
                if foreign
                    && view.wc_commit_ids.get(name) == Some(target)
                    && visible.contains(target)
                {
                    targets.insert(target.clone());
                }
            }
        }
        targets
    }

    /// Store the canonical payload on copied canonical parents, independently of replay.
    pub(super) fn copy_operation(
        &self,
        entry: &HistoryEntry<'_>,
        history: &ReplayHistory<'_>,
    ) -> Operation {
        let (op, view) = (entry.op, &entry.view);
        let op_store = self.loader.op_store().clone();
        let copy = op_store::Operation {
            view_id: block_on(op_store.write_view(view)).unwrap(),
            parents: entry
                .parents
                .iter()
                .map(|p| history.copies[p].id().clone())
                .collect(),
            metadata: op.metadata.clone(),
            commit_predecessors: op.commit_predecessors.clone(),
        };
        let copy_id = block_on(op_store.write_operation(&copy)).unwrap();
        block_on(self.loader.load_operation(&copy_id)).unwrap()
    }

    /// Replay the operation, then record whether it agrees with the hive's or deviates.
    /// The deviation frontier controls rejoining.
    pub(super) fn replay_operation(
        &mut self,
        entry: &HistoryEntry<'_>,
        copy: &Operation,
        history: &mut ReplayHistory<'_>,
    ) -> Operation {
        let (id, op, op_parents, view) = (entry.id, entry.op, &entry.parents, &entry.view);
        let is_merge = entry.is_merge();
        let kept = entry.retained;
        let parents: Vec<&Operation> = op_parents.iter().map(|p| &history.replays[p]).collect();
        let agreed = op_parents
            .iter()
            .all(|p| history.replays[p].id() == history.copies[p].id());
        // A merge `jj op abandon` gave other parents keeps its view, as jj keeps every
        // operation's: it goes in as the hive has it, as a command does.
        if (!is_merge || kept.is_some()) && agreed {
            return copy.clone();
        }
        let (replayed, how) = if !is_merge {
            let replayed = if let [parent] = op_parents.as_slice() {
                self.apply(&history.copies[parent], copy, parents[0])
            } else {
                // Lift the command's payload between independently merged copy
                // and replay frontiers, retaining the existing deviation tracking.
                let input = self.merge(op_parents.iter().map(|p| &history.copies[p]).collect());
                let onto = self.merge(parents);
                self.apply(&input.op, copy, &onto.op)
            };
            (replayed, "applied")
        } else {
            (self.merge(parents), "merged")
        };
        if is_merge {
            let alike = self.alike_changes(&replayed.view);
            if !alike.is_empty() {
                self.jj_alike.insert(id.0.clone(), alike);
            }
        }
        let known = self.changes_of(
            op_parents
                .iter()
                .flat_map(|p| [&history.copies[p], &history.replays[p]]),
        );
        let ours = self.summary(view, &known);
        let theirs = self.summary(&replayed.view, &known);
        let exact = ours == theirs;
        if is_merge && agreed && !exact {
            // What the hive's merge did beyond jj's is musubi's, whatever later
            // operations make of it.
            let beyond = self.beyond(view, &replayed.view, &known);
            if !beyond.is_empty() {
                self.unexplained.push(format!(
                    "{}: {} beyond jj's merge of the same parents",
                    describe(id, op),
                    beyond.join(", ")
                ));
            }
        }
        // A merge unlike jj's of the same parents has had its excess judged above. Where no
        // other line has parted, the reference goes on from the hive's merge, as from jj's
        // own, so that the merges after it are judged each against jj's merge too.
        let rejoin = (exact || (is_merge && agreed)) && history.can_rejoin(id);
        if !exact {
            let diff = self.difference(view, &replayed.view, &known);
            let then = if rejoin {
                "; the reference goes on from the hive's"
            } else {
                ""
            };
            self.deviations.push(format!(
                "{} {how} by jj differs from the hive's: {diff}{then}",
                describe(id, op)
            ));
        } else if rejoin && !agreed {
            self.deviations
                .push(format!("agrees again at {}", describe(id, op)));
        }
        if rejoin {
            return copy.clone();
        }
        history.deviated.insert(id.clone());
        replayed.op
    }
}

/// The allowance for another machine's working copy that the canonical view keeps visible
/// where a native command hid it extends a command's payload only by a commit bound to the
/// same foreign workspace in an input, visible there, and still bound in the output.
#[test]
fn native_payloads_allow_only_foreign_working_copies_retained_from_their_inputs() {
    use std::collections::HashSet;

    use jj_lib::object_id::ObjectId as _;
    use jj_lib::op_store::OperationId;
    use jj_lib::ref_name::WorkspaceName;

    use crate::world::{Naming, Setup};

    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Default,
        prejoin: false,
        secondary: false,
    });
    let key = format!("{}/default", world.fx.machine_key(1));
    let base = CanonicalOp(world.fx.hive.hub.store().head().1.clone());
    let store = world.fx.hive.members[0].adapter.repo().canonical_store();
    let template = store.read_operation(&base).unwrap();
    let source_view = store.read_view(&template.view_id).unwrap();
    let old = source_view.wc_commit_ids[WorkspaceName::new(&key)].clone();
    let native_base = world.latest_op_head(0);
    world.jj(0, &["describe", &old.hex(), "-m", "first foreign rewrite"]);
    let first = OperationId::try_from_hex(world.latest_op_head(0)).unwrap();
    world.jj_at_op(
        0,
        &native_base,
        &["describe", &old.hex(), "-m", "second foreign rewrite"],
    );
    let second = OperationId::try_from_hex(world.latest_op_head(0)).unwrap();
    let snapshot = |id: &OperationId| {
        world
            .evidence
            .commands
            .values()
            .find(|c| c.id == *id)
            .unwrap()
            .clone()
    };
    // The one commit each rewrite made of the foreign working copy.
    let replacement = |id: &OperationId| {
        let command = snapshot(id);
        let before: HashSet<_> = command.base.head_ids.iter().cloned().collect();
        let made: Vec<_> = command
            .made
            .head_ids
            .iter()
            .filter(|head| !before.contains(*head))
            .cloned()
            .collect();
        let [made] = made.as_slice() else {
            panic!("one rewrite of the working copy: {made:?}");
        };
        made.clone()
    };
    let (first_version, second_version) = (replacement(&first), replacement(&second));
    let mut command = snapshot(&first);
    command.made.head_ids = HashSet::from([first_version.clone()]);
    let mut reference = Reference::build(&world);
    let store = world.fx.hive.members[0].adapter.repo().canonical_store();
    let root = world.fx.hive.members[0]
        .adapter
        .repo()
        .loader()
        .store()
        .root_commit_id()
        .clone();
    for case in ["retained", "missing slot", "hidden", "new target", "own"] {
        let mut source = source_view.clone();
        if case == "missing slot" {
            source.wc_commit_ids.remove(WorkspaceName::new(&key));
        }
        if case == "hidden" {
            source.head_ids = HashSet::from([root.clone()]);
        }
        let mut input = template.clone();
        input.metadata.attributes.clear();
        input.metadata.description = format!("foreign visibility input: {case}");
        input.parents = vec![base.0.clone()];
        input.view_id = store.write_view(&source).unwrap();
        let input_id = store.write_operation(&input).unwrap();
        command.input = Some(input_id.clone());
        command.copy = world.fx.machine_key(if case == "own" { 1 } else { 0 });
        let mut output = input;
        output.parents = vec![input_id.0];
        let mut canonical = command.made.clone();
        canonical.head_ids.insert(old.clone());
        canonical.wc_commit_ids.insert(
            key.clone().into(),
            if case == "new target" {
                second_version.clone()
            } else {
                old.clone()
            },
        );
        let protected = reference.retained_foreign_targets(
            &world,
            &command.copy,
            command.input.as_ref(),
            &output,
            &canonical,
        );
        assert_eq!(protected.contains(&old), case == "retained", "{case}");
        let mut expected = command.made.clone();
        expected.head_ids.extend(protected);
        let unexpected =
            reference.unexplained_command_changes(&command.base, &expected, &canonical);
        assert_eq!(
            unexpected.is_empty(),
            case == "retained",
            "{case}: {unexpected:?}"
        );
        if case == "retained" {
            canonical.head_ids.insert(second_version.clone());
            assert!(
                !reference
                    .unexplained_command_changes(&command.base, &expected, &canonical)
                    .is_empty(),
                "a third version is still extra"
            );
            canonical.head_ids.remove(&first_version);
            assert!(
                !reference
                    .unexplained_command_changes(&command.base, &expected, &canonical)
                    .is_empty(),
                "equal counts cannot hide a different version"
            );
        }
    }
}
