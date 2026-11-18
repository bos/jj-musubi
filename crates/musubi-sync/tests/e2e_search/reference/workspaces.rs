//! Evidence that a workspace binding existed at an operation's actual source inputs.
//!
//! Names and targets are authenticated independently of the merge being checked. A
//! canonical marker or a later workspace birth cannot establish an earlier binding.
//! Certificates follow source dependencies iteratively, so deep histories use no call stack.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashSet;

use futures::executor::block_on;
use jj_lib::backend::CommitId;
use jj_lib::op_store;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::View;
use jj_lib::operation::Operation;
use jj_lib::ref_name::WorkspaceName;
use musubi_jj::canonical::Work;
use musubi_jj::op_id::CanonicalOp;
use musubi_jj::op_id::LocalOp;
use musubi_jj::presence::Presence;

use super::Reference;
use super::replay::CertifiedParent;
use super::replay::WorkspaceReplay;
use crate::world::CommandSnapshot;
use crate::world::World;
use crate::world::merge_key;

/// Evidence for each workspace is kept together. Name authentication never certifies a
/// target: a native merge can prove a name whose working-copy replacement remains unknown.
#[derive(Clone, Default)]
pub(super) struct WorkspaceCertificate {
    evidence: BTreeMap<String, WorkspaceEvidence>,
}

#[derive(Clone, Copy, Default, PartialEq, Eq)]
enum NameAuthentication {
    #[default]
    Unknown,
    Authenticated,
}

#[derive(Clone, Copy, Default, PartialEq, Eq)]
enum BirthWitness {
    #[default]
    Unknown,
    NativeMerge,
}

#[derive(Clone, Copy, Default, PartialEq, Eq)]
enum BindingPresence {
    #[default]
    Live,
    Dormant,
}

/// Four independent facts about one workspace. Revoking a binding does not revoke its
/// name; retaining its name does not certify a replacement binding. Dormancy records a
/// namespace omitted centrally, rather than an owner deleting it.
///
/// The transitions below preserve every unmentioned fact:
///
/// | Transition | Binding | Presence | Birth witness | Name |
/// | --- | --- | --- | --- | --- |
/// | carry input | replace | dormant if omitted | inherit | keep |
/// | confirm live | replace | live | inherit | keep |
/// | reject payload | remove | keep | remove | keep |
/// | drop owned binding | remove | live | remove | keep |
/// | owner creates | replace | live | remove | keep |
/// | native merge name | keep | keep | native merge | authenticated |
/// | native merge binding | replace | dormant if omitted | native merge | keep |
/// | opaque dormant carry | insert if absent | dormant | inherit | keep |
///
/// After all transitions, every certified binding authenticates its name. A dormant
/// marker can outlive a rejected binding; by itself it never authorizes a target.
#[derive(Clone, Default)]
pub(super) struct WorkspaceEvidence {
    binding: Option<CommitId>,
    presence: BindingPresence,
    birth: BirthWitness,
    name: NameAuthentication,
}

impl WorkspaceEvidence {
    pub(super) fn remember_binding(&mut self, target: CommitId) {
        self.binding = Some(target);
    }

    pub(super) fn authenticate_name(&mut self) {
        self.name = NameAuthentication::Authenticated;
    }

    pub(super) fn witness_merge_birth(&mut self) {
        self.birth = BirthWitness::NativeMerge;
    }

    pub(super) fn mark_dormant(&mut self) {
        self.presence = BindingPresence::Dormant;
    }

    fn inherit_birth(&mut self, source: &Self) {
        if source.birth == BirthWitness::NativeMerge {
            self.witness_merge_birth();
        }
    }

    fn carry_input(&mut self, target: CommitId, source: &Self, dormant: bool) {
        self.remember_binding(target);
        if dormant {
            self.mark_dormant();
        }
        self.inherit_birth(source);
    }

    fn confirm_live(&mut self, target: CommitId, source: &Self) {
        self.confirm_membership(target, source.birth == BirthWitness::NativeMerge);
    }

    fn confirm_membership(&mut self, target: CommitId, has_birth: bool) {
        self.remember_binding(target);
        self.presence = BindingPresence::Live;
        if has_birth {
            self.witness_merge_birth();
        }
    }

    fn reject_payload(&mut self) {
        self.binding = None;
        self.birth = BirthWitness::Unknown;
    }

    fn drop_owned_binding(&mut self) {
        self.reject_payload();
        self.presence = BindingPresence::Live;
    }

    fn owner_created(&mut self, target: CommitId) {
        self.remember_binding(target);
        self.presence = BindingPresence::Live;
        self.birth = BirthWitness::Unknown;
    }

    fn native_merge_name(&mut self) {
        self.authenticate_name();
        self.witness_merge_birth();
    }

    fn native_merge_binding(&mut self, target: CommitId, dormant: bool) {
        self.remember_binding(target);
        self.witness_merge_birth();
        if dormant {
            self.mark_dormant();
        }
    }

    fn carry_opaque_dormant(&mut self, target: &CommitId, has_birth: bool) {
        self.binding.get_or_insert_with(|| target.clone());
        self.mark_dormant();
        if has_birth {
            self.witness_merge_birth();
        }
    }
}

impl WorkspaceCertificate {
    pub(super) fn entry(&mut self, key: String) -> &mut WorkspaceEvidence {
        self.evidence.entry(key).or_default()
    }

    pub(super) fn binding(&self, key: &str) -> Option<&CommitId> {
        self.evidence.get(key)?.binding.as_ref()
    }

    pub(super) fn bindings(&self) -> impl Iterator<Item = (&String, &CommitId)> {
        self.evidence
            .iter()
            .filter_map(|(key, evidence)| evidence.binding.as_ref().map(|target| (key, target)))
    }

    fn evidence_for(&self, key: &str) -> &WorkspaceEvidence {
        self.evidence.get(key).expect("a binding has evidence")
    }

    pub(super) fn has_name(&self, key: &str) -> bool {
        self.evidence
            .get(key)
            .is_some_and(|evidence| evidence.name == NameAuthentication::Authenticated)
    }

    pub(super) fn names(&self) -> impl Iterator<Item = &String> {
        self.evidence.iter().filter_map(|(key, evidence)| {
            (evidence.name == NameAuthentication::Authenticated).then_some(key)
        })
    }

    pub(super) fn has_merge_birth(&self, key: &str) -> bool {
        self.evidence
            .get(key)
            .is_some_and(|evidence| evidence.birth == BirthWitness::NativeMerge)
    }

    pub(super) fn merge_births(&self) -> impl Iterator<Item = &String> {
        self.evidence.iter().filter_map(|(key, evidence)| {
            (evidence.birth == BirthWitness::NativeMerge).then_some(key)
        })
    }

    pub(super) fn is_dormant(&self, key: &str) -> bool {
        self.evidence
            .get(key)
            .is_some_and(|evidence| evidence.presence == BindingPresence::Dormant)
    }

    pub(super) fn dormant_names(&self) -> impl Iterator<Item = &String> {
        self.evidence.iter().filter_map(|(key, evidence)| {
            (evidence.presence == BindingPresence::Dormant).then_some(key)
        })
    }

    fn authenticate_names(&mut self, names: impl IntoIterator<Item = String>) {
        for key in names {
            self.entry(key).authenticate_name();
        }
    }

    fn inherit_known_births(&mut self, input: &Self) {
        for key in input.merge_births() {
            if self.has_name(key) {
                self.entry(key.clone()).witness_merge_birth();
            }
        }
    }

    fn retain_names(&mut self, keep: impl Fn(&str) -> bool) {
        for (key, evidence) in &mut self.evidence {
            if evidence.name == NameAuthentication::Authenticated && !keep(key) {
                evidence.name = NameAuthentication::Unknown;
            }
        }
    }

    fn authenticate_bindings(&mut self) {
        for evidence in self.evidence.values_mut() {
            if evidence.binding.is_some() {
                evidence.authenticate_name();
            }
        }
    }

    // Negative controls independently revoke each kind of witness.
    pub(super) fn remove_binding(&mut self, key: &str) {
        if let Some(evidence) = self.evidence.get_mut(key) {
            evidence.binding = None;
        }
    }

    pub(super) fn remove_name(&mut self, key: &str) {
        if let Some(evidence) = self.evidence.get_mut(key) {
            evidence.name = NameAuthentication::Unknown;
        }
    }

    pub(super) fn clear_bindings(&mut self) {
        for evidence in self.evidence.values_mut() {
            evidence.binding = None;
        }
    }

    pub(super) fn clear_names(&mut self) {
        for evidence in self.evidence.values_mut() {
            evidence.name = NameAuthentication::Unknown;
        }
    }

    pub(super) fn clear_merge_births(&mut self) {
        for evidence in self.evidence.values_mut() {
            evidence.birth = BirthWitness::Unknown;
        }
    }

    pub(super) fn clear_dormancy(&mut self) {
        for evidence in self.evidence.values_mut() {
            evidence.presence = BindingPresence::Live;
        }
    }

    pub(super) fn foreign_binding_carried_by_command(
        &self,
        command: &CommandSnapshot,
        key: &str,
        actual: &CommitId,
        visible: &HashSet<CommitId>,
    ) -> bool {
        let Some((owner, _)) = key.split_once('/') else {
            return false;
        };
        let Some(old) = self.binding(key) else {
            return false;
        };
        if owner == command.copy || self.is_dormant(key) {
            return false;
        }
        let rewrites: Vec<_> = command
            .predecessors
            .iter()
            .flat_map(|preds| preds.iter())
            .filter(|(_, predecessors)| predecessors.contains(old))
            .map(|(new, _)| new)
            .collect();
        if old == actual {
            return rewrites.is_empty();
        }
        rewrites
            .into_iter()
            .filter(|new| visible.contains(*new))
            .collect::<Vec<_>>()
            == [actual]
    }

    pub(super) fn names_carried_by_command<'a>(
        &'a self,
        command: &'a CommandSnapshot,
        births: &'a BTreeSet<String>,
    ) -> impl Iterator<Item = &'a String> {
        self.names().filter(move |key| {
            command_workspace_alias(command, births, key, None)
                .is_some_and(|alias| command.made.wc_commit_ids.contains_key(&alias))
        })
    }
}

/// One unambiguous raw alias for an already-certified key. The copy history is captured
/// with the command, including departed copies; an owned literal cannot name a foreign slot.
pub(super) fn command_workspace_alias(
    command: &CommandSnapshot,
    births: &BTreeSet<String>,
    key: &str,
    target: Option<&CommitId>,
) -> Option<jj_lib::ref_name::WorkspaceNameBuf> {
    let (owner, workspace) = key.split_once('/')?;
    let candidates: Vec<_> = command
        .base
        .wc_commit_ids
        .iter()
        .filter(|(name, base)| {
            if target.is_some_and(|target| *base != target) {
                return false;
            }
            if owner == command.copy {
                return name.as_str() == workspace;
            }
            let Some((prefix, shown_workspace)) = name.as_str().split_once('/') else {
                return false;
            };
            !births.contains(&format!("{}/{}", command.copy, name.as_str()))
                && shown_workspace == workspace
                && command
                    .copies
                    .iter()
                    .filter(|copy| musubi_jj::workspaces::could_be_shown_as(copy, prefix))
                    .count()
                    == 1
                && musubi_jj::workspaces::could_be_shown_as(owner, prefix)
        })
        .map(|(name, _)| name.clone())
        .collect();
    match candidates.as_slice() {
        [name] => Some(name.clone()),
        _ => None,
    }
}

pub(super) fn workspace_fixup_input<'a>(
    world: &'a World,
    id: &CanonicalOp,
    op: &'a op_store::Operation,
) -> Option<(&'a str, &'a CanonicalOp)> {
    let (trimmer, input) = world.evidence.workspace_fixup_inputs.get(&merge_key(op))?;
    let owner = op.metadata.attributes.get("musubi.work")?;
    (input != id && owner != trimmer).then_some((owner.as_str(), input))
}

/// The exact foreign alias is absent from this captured command's output. An owned
/// literal never stands for a foreign slot, and an ambiguous foreign prefix is not absent.
pub(super) fn foreign_alias_absent(
    command: &CommandSnapshot,
    authenticated_name: impl Fn(&str) -> bool,
    key: &str,
) -> bool {
    let Some((owner, workspace)) = key.split_once('/') else {
        return false;
    };
    owner != command.copy
        && command.made.wc_commit_ids.keys().all(|name| {
            authenticated_name(&format!("{}/{}", command.copy, name.as_str()))
                || !name
                    .as_str()
                    .split_once('/')
                    .is_some_and(|(prefix, shown)| {
                        shown == workspace
                            && musubi_jj::workspaces::could_be_shown_as(owner, prefix)
                    })
        })
}

pub(super) fn workspace_source_parents(op: &op_store::Operation) -> Option<Vec<CanonicalOp>> {
    match op.metadata.attributes.get("musubi.original-parents") {
        Some(text) => text
            .split_whitespace()
            .map(OperationId::try_from_hex)
            .map(|id| id.map(CanonicalOp))
            .collect(),
        None => Some(CanonicalOp::parents_of(op)),
    }
}

/// The inputs already observed for one certificate derivation. Optional historical
/// sources are deliberately absent: each guarded phase reads them only when it needs them.
#[derive(Clone, Copy)]
struct WorkspaceDerivation<'a> {
    id: &'a CanonicalOp,
    op: &'a op_store::Operation,
    view: &'a View,
    parents: &'a [CanonicalOp],
    inputs: &'a [WorkspaceCertificate],
    presence: &'a Presence<Work>,
    command: Option<&'a CommandSnapshot>,
}

impl WorkspaceDerivation<'_> {
    fn private_at(&self, key: &str) -> bool {
        let Some((owner, _)) = key.split_once('/') else {
            return false;
        };
        !self.presence.is_present(owner)
            || (self.op.metadata.workspace_name.is_none()
                && self
                    .op
                    .metadata
                    .attributes
                    .get("musubi.work")
                    .is_some_and(|copy| copy == owner))
    }

    fn rewritten(&self, target: &CommitId) -> bool {
        self.op
            .commit_predecessors
            .iter()
            .flat_map(|preds| preds.values())
            .chain(
                self.command.into_iter().flat_map(|command| {
                    command.predecessors.iter().flat_map(|preds| preds.values())
                }),
            )
            .any(|old| old.contains(target))
    }

    /// Carry authenticated names, births and unchanged input bindings. This phase adds
    /// provisional evidence; later command checks may revoke it, and merge replay replaces it.
    fn inherit_inputs(&self, result: &mut WorkspaceCertificate) {
        let WorkspaceDerivation {
            view,
            parents,
            inputs,
            command,
            ..
        } = *self;
        if command.is_none() && parents.len() == 1 {
            for input in inputs {
                result.authenticate_names(
                    input
                        .names()
                        .filter(|key| {
                            view.wc_commit_ids.contains_key(WorkspaceName::new(key))
                                || self.private_at(key)
                        })
                        .cloned(),
                );
                // A proven merge birth authenticates the name independently of its
                // current commit. Replacing an abandoned working copy does not create a
                // new logical name; it also does not certify the replacement's payload.
                result.inherit_known_births(input);
            }
        }
        for input in inputs {
            for (key, target) in input.bindings() {
                let live = !input.is_dormant(key)
                    && view.wc_commit_ids.get(WorkspaceName::new(key)) == Some(target);
                let dormant = !view.wc_commit_ids.contains_key(WorkspaceName::new(key))
                    && self.private_at(key)
                    && !inputs.is_empty()
                    && inputs
                        .iter()
                        .all(|other| other.binding(key) == Some(target))
                    && !self.rewritten(target);
                if live || dormant {
                    result.entry(key.clone()).carry_input(
                        target.clone(),
                        input.evidence_for(key),
                        dormant,
                    );
                }
            }
        }
    }

    /// Seed only exact targets observed at setup or a native join. Existing name, birth
    /// and dormancy evidence is retained; a later command or merge may supersede it.
    fn seed_observed_bindings(&self, world: &World, result: &mut WorkspaceCertificate) {
        let WorkspaceDerivation { op, view, .. } = *self;
        if world.baseline_operation(&merge_key(op)) {
            for key in &world.evidence.initial_workspace_keys {
                if let Some(target) = view.wc_commit_ids.get(WorkspaceName::new(key)) {
                    result.entry(key.clone()).remember_binding(target.clone());
                }
            }
        }
        if let Some(bindings) = world.evidence.workspace_joins.get(&merge_key(op)) {
            for (key, target) in bindings {
                if view.wc_commit_ids.get(WorkspaceName::new(key)) == Some(target) {
                    result.entry(key.clone()).remember_binding(target.clone());
                }
            }
        }
    }
}

impl Reference {
    /// Canonical views keep other copies' working copies visible even when a native
    /// operation removes their local aliases. Only exact live input bindings retained unchanged
    /// by the result can extend the native command's visible payload.
    pub(super) fn retained_foreign_targets(
        &mut self,
        world: &World,
        copy: &str,
        command_input: Option<&CanonicalOp>,
        op: &op_store::Operation,
        view: &View,
    ) -> BTreeSet<CommitId> {
        let mut inputs = workspace_source_parents(op).unwrap_or_default();
        inputs.extend(command_input.cloned());
        inputs.sort();
        inputs.dedup();
        let mut targets = BTreeSet::new();
        for input in inputs {
            let certificate = self.workspace_certificate(world, &input);
            let Some(source) = Self::workspace_source(world, &input) else {
                continue;
            };
            let Some(source) = world.fx.hive.members.iter().find_map(|member| {
                member
                    .adapter
                    .repo()
                    .canonical_store()
                    .read_view(&source.view_id)
                    .ok()
            }) else {
                continue;
            };
            let visible = self.visible(&source);
            for (key, target) in certificate.bindings() {
                let Some((owner, _)) = key.split_once('/') else {
                    continue;
                };
                if owner != copy
                    && !certificate.is_dormant(key)
                    && source.wc_commit_ids.get(WorkspaceName::new(key)) == Some(target)
                    && view.wc_commit_ids.get(WorkspaceName::new(key)) == Some(target)
                    && visible.contains(target)
                {
                    targets.insert(target.clone());
                }
            }
        }
        targets
    }

    /// Extra logical names need an independent native birth witness. Plain commands may
    /// preserve an injected name, so only their actual additions authorize new keys.
    pub fn witnessed_workspace_names(&mut self, world: &World) -> BTreeSet<String> {
        let head = CanonicalOp(world.fx.hive.hub.store().head().1.clone());
        self.workspace_certificate(world, &head)
            .merge_births()
            .cloned()
            .collect()
    }

    pub(super) fn workspace_source(world: &World, id: &CanonicalOp) -> Option<op_store::Operation> {
        world.fx.hive.members.iter().find_map(|member| {
            let store = member.adapter.repo().canonical_store();
            store
                .has_operation(id)
                .then(|| store.read_operation(id).ok())
                .flatten()
        })
    }

    pub(super) fn workspace_copy(&mut self, world: &World, id: &CanonicalOp) -> Option<Operation> {
        let root = world.fx.hive.members[0]
            .adapter
            .repo()
            .canonical_store()
            .root_operation_id();
        self.workspace_copies
            .entry(root.clone())
            .or_insert_with(|| block_on(self.loader.root_operation()));
        let mut pending = vec![(id.clone(), false)];
        while let Some((next, ready)) = pending.pop() {
            if self.workspace_copies.contains_key(&next) {
                continue;
            }
            let mut op = Self::workspace_source(world, &next)?;
            if !ready {
                pending.push((next, true));
                pending.extend(
                    CanonicalOp::parents_of(&op)
                        .into_iter()
                        .rev()
                        .map(|p| (p, false)),
                );
                continue;
            }
            let view = world.fx.hive.members.iter().find_map(|member| {
                member
                    .adapter
                    .repo()
                    .canonical_store()
                    .read_view(&op.view_id)
                    .ok()
            })?;
            let store = self.loader.op_store();
            op.view_id = block_on(store.write_view(&view)).ok()?;
            let copied = block_on(store.write_operation(&op)).ok()?;
            if copied != next.0 {
                return None;
            }
            let copied = block_on(self.loader.load_operation(&copied)).ok()?;
            self.workspace_copies.insert(next, copied);
        }
        self.workspace_copies.get(id).cloned()
    }

    /// Existing marked identities remain useful after the disposable map loses an
    /// unreachable alias. Read stored bodies only; observing a source creates no identity.
    pub(super) fn source_aliases(
        world: &World,
        node: &musubi_jj::node::NodeRepo,
        local: &LocalOp,
    ) -> Vec<CanonicalOp> {
        let marked = block_on(node.loader().op_store().read_operation(&local.0))
            .ok()
            .and_then(|op| {
                op.metadata
                    .attributes
                    .get(musubi_jj::node::CANONICAL_ATTRIBUTE)
                    .and_then(OperationId::try_from_hex)
                    .map(CanonicalOp)
            })
            .filter(|id| Self::workspace_source(world, id).is_some());
        let mut aliases: Vec<_> = marked.into_iter().collect();
        if let Some(mapped) = node.canonical_of(local)
            && !aliases.contains(&mapped)
        {
            aliases.push(mapped);
        }
        aliases
    }

    pub(super) fn workspace_dependencies(world: &World, id: &CanonicalOp) -> Vec<CanonicalOp> {
        let Some(op) = Self::workspace_source(world, id) else {
            return vec![];
        };
        let mut dependencies = workspace_source_parents(&op).unwrap_or_default();
        if let Some(input) = world
            .evidence
            .commands
            .get(&merge_key(&op))
            .and_then(|c| c.input.as_ref())
        {
            dependencies.push(input.clone());
        }
        if let Some((_, input)) = workspace_fixup_input(world, id, &op) {
            dependencies.push(input.clone());
        }
        dependencies
    }

    /// Optional historical bases cannot borrow the certificate being proved, even
    /// indirectly through a source parent, captured command or trim input. Preflight the
    /// entire candidate before writing any certificate or changing the active proof stack.
    pub(super) fn workspace_dependencies_available(
        &self,
        world: &World,
        bases: &[CanonicalOp],
    ) -> bool {
        let mut pending: Vec<_> = bases.iter().rev().map(|id| (id.clone(), false)).collect();
        let mut visiting = HashSet::new();
        let mut finished = HashSet::new();
        while let Some((next, ready)) = pending.pop() {
            if self.workspace_certificates.contains_key(&next) || finished.contains(&next) {
                continue;
            }
            if ready {
                visiting.remove(&next);
                finished.insert(next);
                continue;
            }
            if self.workspace_in_progress.contains(&next) || !visiting.insert(next.clone()) {
                return false;
            }
            pending.push((next.clone(), true));
            pending.extend(
                Self::workspace_dependencies(world, &next)
                    .into_iter()
                    .rev()
                    .map(|id| (id, false)),
            );
        }
        true
    }

    pub(super) fn workspace_certificate(
        &mut self,
        world: &World,
        id: &CanonicalOp,
    ) -> WorkspaceCertificate {
        // A certificate's frame contains merge views and witnesses. Keep history depth on
        // the heap rather than one such frame per source operation on the test thread.
        let mut pending = vec![(id.clone(), false)];
        while let Some((next, ready)) = pending.pop() {
            if self.workspace_certificates.contains_key(&next) {
                continue;
            }
            if ready {
                let certificate = self.workspace_certificate_of(world, &next);
                self.workspace_certificates
                    .insert(next.clone(), certificate);
                self.workspace_in_progress.remove(&next);
                continue;
            }
            assert!(
                self.workspace_in_progress.insert(next.clone()),
                "workspace source dependencies cycle at {next:?}"
            );
            pending.push((next.clone(), true));
            pending.extend(
                Self::workspace_dependencies(world, &next)
                    .into_iter()
                    .rev()
                    .map(|parent| (parent, false)),
            );
        }
        self.workspace_certificates[id].clone()
    }

    pub(super) fn workspace_certificate_of(
        &mut self,
        world: &World,
        id: &CanonicalOp,
    ) -> WorkspaceCertificate {
        if let Some(known) = self.workspace_certificates.get(id) {
            return known.clone();
        }
        let Some(op) = Self::workspace_source(world, id) else {
            return WorkspaceCertificate::default();
        };
        let Some(view) = world.fx.hive.members.iter().find_map(|member| {
            member
                .adapter
                .repo()
                .canonical_store()
                .read_view(&op.view_id)
                .ok()
        }) else {
            return WorkspaceCertificate::default();
        };
        let Some(presence) = world
            .fx
            .hive
            .members
            .iter()
            .find_map(|member| member.adapter.repo().presence(id).ok())
        else {
            return WorkspaceCertificate::default();
        };
        // Contraction preserves the original parent identities. Use those source parents
        // to certify a retained operation, including a merge now represented on root.
        let Some(parents) = workspace_source_parents(&op) else {
            return WorkspaceCertificate::default();
        };
        let inputs: Vec<_> = parents
            .iter()
            .map(|parent| self.workspace_certificate(world, parent))
            .collect();
        let command = world.evidence.commands.get(&merge_key(&op));
        let context = WorkspaceDerivation {
            id,
            op: &op,
            view: &view,
            parents: &parents,
            inputs: &inputs,
            presence: &presence,
            command,
        };
        let mut result = WorkspaceCertificate::default();
        context.inherit_inputs(&mut result);
        context.seed_observed_bindings(world, &mut result);
        self.repair_trim_workspace_bindings(world, &context, &mut result);
        if let Some(command) = command {
            self.derive_command_workspaces(world, &context, command, &mut result);
        } else if parents.len() > 1 {
            self.derive_merge_workspaces(world, &context, &mut result);
        }
        self.reconcile_present_workspace_bindings(world, &context, &mut result);
        result.authenticate_bindings();
        self.workspace_certificates
            .insert(id.clone(), result.clone());
        result
    }

    /// Confirm unchanged slots from a captured pre-trim input. A confirmed slot becomes
    /// live and inherits its birth witness; the fix-up output cannot certify itself.
    fn repair_trim_workspace_bindings(
        &mut self,
        world: &World,
        context: &WorkspaceDerivation<'_>,
        result: &mut WorkspaceCertificate,
    ) {
        let WorkspaceDerivation { id, op, view, .. } = *context;
        // A full native trim removes the ancestry of other copies' last work. Its
        // fix-up must preserve their accepted slots. Use the history observed before
        // the trim, never the fix-up's work marker alone, to certify an unchanged slot.
        if let Some((owner, input)) = workspace_fixup_input(world, id, op) {
            let source = self.workspace_certificate(world, input);
            for (key, target) in source.bindings() {
                if key.split_once('/').is_some_and(|(copy, _)| copy == owner)
                    && view.wc_commit_ids.get(WorkspaceName::new(key)) == Some(target)
                {
                    result
                        .entry(key.clone())
                        .confirm_live(target.clone(), source.evidence_for(key));
                }
            }
        }
    }

    /// Check the actual owner command after its source is authenticated. This phase may
    /// revoke bindings and birth witnesses, remove deleted owned names, or record new names.
    /// Native visibility and any optional command input are observed only inside this guard.
    fn derive_command_workspaces(
        &mut self,
        world: &World,
        context: &WorkspaceDerivation<'_>,
        command: &CommandSnapshot,
        result: &mut WorkspaceCertificate,
    ) {
        let WorkspaceDerivation {
            op,
            view,
            inputs,
            presence,
            ..
        } = *context;
        if op
            .metadata
            .workspace_name
            .as_ref()
            .and_then(|key| musubi_jj::workspaces::split_key(key.as_str()))
            .is_some_and(|(owner, _)| owner == command.copy)
        {
            let native_visible = self.visible(&command.made);
            let mut command_inputs = inputs.to_vec();
            if let Some(input) = &command.input {
                command_inputs.push(self.workspace_certificate(world, input));
            }
            if command.input.is_none() {
                self.workspace_unmapped
                    .insert((command.copy.clone(), command.parent.clone()));
            }
            for input in &command_inputs {
                result.authenticate_names(
                    input
                        .names_carried_by_command(command, &world.evidence.workspace_births)
                        .cloned(),
                );
                // Forgetting a local alias cannot delete the other owner's name.
                // Later commands may no longer have that alias even at their base.
                // Keep only the independently known namespace, never its target.
                result.authenticate_names(
                    input
                        .names()
                        .filter(|key| {
                            key.split_once('/')
                                .is_some_and(|(owner, _)| owner != command.copy)
                                && view.wc_commit_ids.contains_key(WorkspaceName::new(key))
                        })
                        .cloned(),
                );
                result.inherit_known_births(input);
            }
            // `jj op abandon`, or musubi reparenting a machine's operations, can move a command
            // onto other parents, keeping its view, which jj computed on the input the command
            // ran on. Where the retained source records that input as the command's base, a new
            // parent's binding for one of the maker's own slots need not be that base's: the
            // command's own output certifies the slot, as it does for any command. The
            // adjudication already holds a retained operation to its view, not its parents.
            let reparented = world
                .evidence
                .kept_operations
                .get(&merge_key(op))
                .is_some_and(|kept| {
                    kept.native
                        && !kept.realized
                        && kept.copy == command.copy
                        && kept.parent.as_ref() == Some(&command.base)
                });
            for input in &command_inputs {
                for (key, base) in input.bindings() {
                    let owned = key
                        .split_once('/')
                        .is_some_and(|(owner, _)| owner == command.copy);
                    if let Some(actual) = view.wc_commit_ids.get(WorkspaceName::new(key))
                        && key
                            .split_once('/')
                            .is_some_and(|(owner, _)| presence.is_present(owner))
                        && input.foreign_binding_carried_by_command(
                            command,
                            key,
                            actual,
                            &native_visible,
                        )
                    {
                        let evidence = result.entry(key.clone());
                        evidence.authenticate_name();
                        evidence.confirm_live(actual.clone(), input.evidence_for(key));
                        continue;
                    }
                    let Some(alias) = command_workspace_alias(
                        command,
                        &world.evidence.workspace_births,
                        key,
                        (!(owned && reparented)).then_some(base),
                    ) else {
                        // A native command by another copy cannot remove a dormant
                        // owner's namespace. Carry only this already-certified absent
                        // binding, without authorizing a live payload or a new name.
                        let owner = key.split_once('/').unwrap().0;
                        let untouched = command.made.wc_commit_ids.keys().all(|name| {
                            !name.as_str().split_once('/').is_some_and(|(prefix, _)| {
                                musubi_jj::workspaces::could_be_shown_as(owner, prefix)
                            })
                        });
                        if owner != command.copy
                            && input.is_dormant(key)
                            && untouched
                            && !context.rewritten(base)
                            && context.private_at(key)
                            && !view.wc_commit_ids.contains_key(WorkspaceName::new(key))
                        {
                            result.entry(key.clone()).carry_input(
                                base.clone(),
                                input.evidence_for(key),
                                true,
                            );
                        }
                        continue;
                    };
                    let owner = key.split_once('/').unwrap().0;
                    let target = command.made.wc_commit_ids.get(&alias);
                    if let Some(target) = target {
                        if view.wc_commit_ids.get(WorkspaceName::new(key)) == Some(target) {
                            result
                                .entry(key.clone())
                                .confirm_live(target.clone(), input.evidence_for(key));
                        } else {
                            result.entry(key.clone()).reject_payload();
                        }
                    } else if owner == command.copy {
                        result.entry(key.clone()).reject_payload();
                    }
                }
            }
            let removed: Vec<_> = result
                .bindings()
                .map(|(key, _)| key)
                .filter(|key| {
                    let (owner, name) = key.split_once('/').unwrap();
                    owner == command.copy
                        && !command
                            .made
                            .wc_commit_ids
                            .contains_key(WorkspaceName::new(name))
                })
                .cloned()
                .collect();
            for key in removed {
                result.entry(key).drop_owned_binding();
            }
            result.retain_names(|key| {
                let (owner, name) = key.split_once('/').unwrap();
                owner != command.copy
                    || command
                        .made
                        .wc_commit_ids
                        .contains_key(WorkspaceName::new(name))
            });
            for (name, target) in &command.made.wc_commit_ids {
                if name.as_str().contains('/') || command.base.wc_commit_ids.contains_key(name) {
                    continue;
                }
                let key = format!("{}/{}", command.copy, name.as_str());
                if world.evidence.workspace_births.contains(&key)
                    && view.wc_commit_ids.get(WorkspaceName::new(&key)) == Some(target)
                {
                    result.entry(key).owner_created(target.clone());
                }
            }
        }
    }

    /// Attempt the ordered native source copies first, then discard all provisional
    /// evidence. Only independent native replay may establish merge names and targets;
    /// an opaque dormant carry additionally requires every input to agree.
    fn derive_merge_workspaces(
        &mut self,
        world: &World,
        context: &WorkspaceDerivation<'_>,
        result: &mut WorkspaceCertificate,
    ) {
        let WorkspaceDerivation {
            id,
            view,
            parents,
            inputs,
            ..
        } = *context;
        // The source graph's ordered parents are replayed by jj, rather than accepting
        // the merge payload as evidence of its own additions or moves.
        let copies: Option<Vec<_>> = parents
            .iter()
            .map(|parent| self.workspace_copy(world, parent))
            .collect();
        *result = WorkspaceCertificate::default();
        if let Some(copies) = copies {
            let parent_views: Vec<_> = copies
                .iter()
                .map(|source| block_on(source.view()).unwrap().store_view().clone())
                .collect();
            let mut replays = vec![WorkspaceReplay {
                view: self.merge(copies.iter().collect()).view,
                parents: parent_views,
                private: None,
            }];
            let certified: Vec<_> = parents
                .iter()
                .zip(inputs)
                .map(|(canonical, certificate)| CertifiedParent {
                    canonical,
                    certificate,
                })
                .collect();
            replays.extend(self.workspace_private_replays(world, id, &certified));
            for WorkspaceReplay {
                view: native,
                parents: source_views,
                private,
            } in replays
            {
                let mut known = self.changes_of(copies.iter());
                for source in &source_views {
                    for target in source.wc_commit_ids.values() {
                        known.insert(self.facts(target).change.clone());
                    }
                }
                let private_made = private.as_ref().map(|(_, made): &(String, View)| made);
                let named: Vec<_> = native
                    .wc_commit_ids
                    .values()
                    .chain(view.wc_commit_ids.values())
                    .chain(
                        private_made
                            .into_iter()
                            .flat_map(|made| made.wc_commit_ids.values()),
                    )
                    .cloned()
                    .collect();
                let structural = self.keys(&named, &|change| known.contains(change));
                for (key, target) in &native.wc_commit_ids {
                    let name = key.as_str();
                    if world.evidence.workspace_births.contains(name)
                        && inputs.iter().zip(&source_views).any(|(input, source)| {
                            input.has_name(name) && source.wc_commit_ids.contains_key(key)
                        })
                        && let Some(actual) = view.wc_commit_ids.get(key)
                        && structural[actual] == structural[target]
                    {
                        result.entry(name.to_owned()).native_merge_name();
                    }
                    if !world.evidence.workspace_births.contains(name)
                        || !inputs.iter().zip(&source_views).any(|(input, source)| {
                            input.binding(name).is_some_and(|certified| {
                                source.wc_commit_ids.get(key) == Some(certified)
                            }) || (private.as_ref().is_some_and(|(maker, _)| {
                                name.split_once('/')
                                    .is_some_and(|(owner, _)| owner == maker)
                            }) && input.has_name(name)
                                && source.wc_commit_ids.contains_key(key))
                        })
                    {
                        continue;
                    }
                    if let Some(actual) = view.wc_commit_ids.get(key) {
                        if structural[actual] == structural[target] {
                            result
                                .entry(name.to_owned())
                                .native_merge_binding(actual.clone(), false);
                        }
                    } else if context.private_at(name)
                        && let Some((maker, made)) = &private
                        && let Some((owner, workspace)) = name.split_once('/')
                        && owner == maker
                        && let Some(actual) = made.wc_commit_ids.get(WorkspaceName::new(workspace))
                        && structural[actual] == structural[target]
                    {
                        result
                            .entry(name.to_owned())
                            .native_merge_binding(actual.clone(), true);
                    }
                }
            }
            // A membership-forgotten owner retains its private names, but an absent
            // certificate on any branch vetoes opaque dormant carry.
            for (key, target) in inputs.iter().flat_map(|input| input.bindings()) {
                if context.private_at(key)
                    && !context.rewritten(target)
                    && !view.wc_commit_ids.contains_key(WorkspaceName::new(key))
                    && inputs
                        .iter()
                        .all(|input| input.binding(key) == Some(target))
                {
                    result.entry(key.clone()).carry_opaque_dormant(
                        target,
                        inputs.iter().any(|input| input.has_merge_birth(key)),
                    );
                }
            }
        }
    }

    /// Reconcile live membership after command/merge derivation. Only sources where the
    /// owner is present can approve its target; confirmation may replace a binding and
    /// clear dormancy, while an old forgotten branch cannot veto newer live work.
    fn reconcile_present_workspace_bindings(
        &mut self,
        world: &World,
        context: &WorkspaceDerivation<'_>,
        result: &mut WorkspaceCertificate,
    ) {
        let WorkspaceDerivation {
            view,
            parents,
            inputs,
            presence,
            command,
            ..
        } = *context;
        // Membership omission is not owner deletion. Only parents where the owner is
        // present contribute its bindings. Every such source must certify the name and
        // agree, allowing a hidden target to follow its unique visible rewrite. A stale
        // forgotten branch cannot veto newer live work. No output certifies itself.
        if command.is_none() && !parents.is_empty() {
            let sources: Option<Vec<_>> = parents
                .iter()
                .map(|parent| {
                    let source = Self::workspace_source(world, parent)?;
                    world.fx.hive.members.iter().find_map(|member| {
                        let node = member.adapter.repo();
                        Some((
                            node.canonical_store().read_view(&source.view_id).ok()?,
                            node.presence(parent).ok()?,
                        ))
                    })
                })
                .collect();
            if let Some(sources) = sources {
                for (name, actual) in &view.wc_commit_ids {
                    let key = name.as_str();
                    let Some((owner, _)) = key.split_once('/') else {
                        continue;
                    };
                    if !presence.is_present(owner)
                        || context.rewritten(actual)
                        || !inputs
                            .iter()
                            .zip(&sources)
                            .any(|(input, (_, source_presence))| {
                                !input.is_dormant(key)
                                    && source_presence.is_present(owner)
                                    && input.binding(key).is_some()
                            })
                    {
                        continue;
                    }
                    let agreed =
                        inputs
                            .iter()
                            .zip(&sources)
                            .all(|(input, (source, source_presence))| {
                                if !source_presence.is_present(owner) {
                                    return true;
                                }
                                let Some(old) = input.binding(key) else {
                                    return false;
                                };
                                if input.is_dormant(key) {
                                    return old == actual
                                        && !source.wc_commit_ids.contains_key(name);
                                }
                                if source.wc_commit_ids.get(name) != Some(old) {
                                    return false;
                                }
                                if old == actual {
                                    return true;
                                }
                                let visible = self.visible(source);
                                if visible.contains(old) {
                                    return false;
                                }
                                let change = self.facts(old).change.clone();
                                let rewrites: Vec<_> = visible
                                    .iter()
                                    .filter(|id| self.facts(id).change == change)
                                    .collect();
                                rewrites.as_slice() == [actual]
                            });
                    if agreed {
                        result.entry(key.to_owned()).confirm_membership(
                            actual.clone(),
                            parents.len() > 1
                                || inputs.iter().any(|input| input.has_merge_birth(key)),
                        );
                    }
                }
            }
        }
    }
}
