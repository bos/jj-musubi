//! Classify each history entry, check its source evidence, and adjudicate its native replay.
//!
//! Source-recorded commands and retained operations have payload checks before replay.
//! A differing merge needs one of three independent native witnesses, tried in order:
//! captured maker inputs, certified private workspace bindings, then the native DAG/index.
//! Structural equality alone can rejoin the hive only across the full deviation frontier.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use futures::executor::block_on;
use jj_lib::backend::ChangeId;
use jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
use jj_lib::op_store;
use jj_lib::op_store::View;
use jj_lib::operation::Operation;
use musubi_jj::op_id::CanonicalOp;

use super::comparison::Summary;
use super::replay::CertifiedParent;
use super::rewrites::MergeRewrite;
use super::witnesses::{RejectionCause, WitnessFailures, WitnessKind};
use super::{Made, Reference, describe, dominates, explained};
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

enum Agreement {
    Exact,
    Native(Box<NativeMergeWitness>),
    Different(Option<WitnessFailures>),
}

/// The independent observation that licenses a merge unlike the canonical-parent replay.
/// Every variant has already passed complete structural comparison with the candidate.
enum NativeMergeWitness {
    CapturedMakerInputs { merged: View, machine: &'static str },
    CertifiedPrivateBindings { merged: View, machine: &'static str },
    NativeDag { merged: View, machine: &'static str },
}

impl NativeMergeWitness {
    fn into_result(self) -> (View, &'static str) {
        match self {
            Self::CapturedMakerInputs { merged, machine }
            | Self::CertifiedPrivateBindings { merged, machine }
            | Self::NativeDag { merged, machine } => (merged, machine),
        }
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
        if is_merge {
            for (new, predecessors) in op.commit_predecessors.iter().flatten() {
                self.rewrites.push(MergeRewrite {
                    operation: id.0.clone(),
                    new: new.clone(),
                    predecessors: predecessors.clone(),
                    native_inputs: Arc::default(),
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

    /// Replay the operation, then choose whether it agrees, has an independent native
    /// explanation, or must remain a deviation. The deviation frontier controls rejoining.
    pub(super) fn replay_operation(
        &mut self,
        world: &World,
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
            copy.clone()
        } else {
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
            let known = self.changes_of(
                op_parents
                    .iter()
                    .flat_map(|p| [&history.copies[p], &history.replays[p]]),
            );
            let ours = self.summary(view, &known);
            let theirs = self.summary(&replayed.view, &known);
            if is_merge && agreed && ours == theirs {
                self.certify_serial_rebases(
                    id,
                    op,
                    &replayed,
                    op_parents,
                    &history.views,
                    (&ours, &theirs),
                );
            }
            // The same parents on both sides, but a different merge: it may be jj's own,
            // on the machine that made it, of the parents as that machine had them.
            let agreement = if ours == theirs {
                Agreement::Exact
            } else if is_merge && agreed {
                self.native_merge_witness(world, entry, &replayed.view, &ours, &known, history)
                    .map_or_else(
                        |failures| Agreement::Different(Some(failures)),
                        |witness| Agreement::Native(Box::new(witness)),
                    )
            } else {
                Agreement::Different(None)
            };
            if is_merge && agreed && matches!(&agreement, Agreement::Different(_)) {
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
            match agreement {
                Agreement::Native(witness) => {
                    let (merged, machine) = (*witness).into_result();
                    self.deviations.push(format!(
                        "{} merged by jj as {} had its parents",
                        describe(id, op),
                        machine
                    ));
                    if history.can_rejoin(id) {
                        copy.clone()
                    } else {
                        // Its own, as where jj's merge agrees but other lines have parted.
                        history.deviated.insert(id.clone());
                        let parents = op_parents.iter().map(|p| history.replays[p].id().clone());
                        self.write_like(copy, &merged, parents.collect())
                    }
                }
                Agreement::Exact if history.can_rejoin(id) => {
                    if !agreed {
                        self.deviations
                            .push(format!("agrees again at {}", describe(id, op)));
                    }
                    copy.clone()
                }
                Agreement::Exact => {
                    history.deviated.insert(id.clone());
                    replayed.op
                }
                Agreement::Different(failures) => {
                    let diff = self.difference(view, &replayed.view, &known);
                    let attempts = failures
                        .map(|failures| format!("; native witnesses rejected: {failures}"))
                        .unwrap_or_default();
                    self.deviations.push(format!(
                        "{} {how} by jj differs from the hive's: {diff}{attempts}",
                        describe(id, op)
                    ));
                    history.deviated.insert(id.clone());
                    replayed.op
                }
            }
        }
    }

    /// Try native explanations in evidence order. A failed or structurally different
    /// witness cannot authorize the next one; each candidate must qualify independently.
    fn native_merge_witness(
        &mut self,
        world: &World,
        entry: &HistoryEntry<'_>,
        canonical: &View,
        ours: &Summary,
        known: &HashSet<ChangeId>,
        history: &ReplayHistory<'_>,
    ) -> Result<NativeMergeWitness, WitnessFailures> {
        let mut failures = WitnessFailures::default();
        match self.merged_as_made(
            world,
            entry.id,
            &entry.parents,
            canonical,
            &history.copies,
            &history.views,
        ) {
            Ok((merged, machine)) if self.summary(&merged, known) == *ours => {
                return Ok(NativeMergeWitness::CapturedMakerInputs { merged, machine });
            }
            Ok((_, machine)) => failures.reject(
                WitnessKind::CapturedMakerInputs,
                Some(machine),
                RejectionCause::StructuralResultDiffers,
            ),
            Err(rejection) => failures.push(rejection),
        }
        let inputs: Vec<_> = entry
            .parents
            .iter()
            .map(|parent| self.workspace_certificate(world, parent))
            .collect();
        let parents: Vec<_> = entry
            .parents
            .iter()
            .zip(&inputs)
            .map(|(canonical, certificate)| CertifiedParent {
                canonical,
                certificate,
            })
            .collect();
        let candidates = self.workspace_private_candidates(world, entry.id, &parents);
        failures.extend(candidates.rejections);
        for replay in candidates.replays {
            let Some((maker, _)) = replay.private else {
                failures.reject(
                    WitnessKind::CertifiedPrivateBindings,
                    None,
                    RejectionCause::PrivateMakerMissing,
                );
                continue;
            };
            let Some(m) = (0..world.nodes()).find(|&m| world.fx.machine_key(m) == maker) else {
                failures.reject(
                    WitnessKind::CertifiedPrivateBindings,
                    Some(&maker),
                    RejectionCause::MakerNotActive,
                );
                continue;
            };
            if self.summary(&replay.view, known) == *ours {
                return Ok(NativeMergeWitness::CertifiedPrivateBindings {
                    merged: replay.view,
                    machine: world.machine(m),
                });
            }
            failures.reject(
                WitnessKind::CertifiedPrivateBindings,
                Some(world.machine(m)),
                RejectionCause::StructuralResultDiffers,
            );
        }
        match self.native_merge_matches(
            world,
            entry.id,
            &entry.parents,
            &entry.view,
            known,
            &history.views,
        ) {
            Ok(machine) => Ok(NativeMergeWitness::NativeDag {
                merged: entry.view.clone(),
                machine,
            }),
            Err(rejections) => {
                failures.extend(rejections);
                Err(failures)
            }
        }
    }
}
