//! Independent native evidence for the reference replay. Captures command inputs,
//! operation bodies, original identities and workspace bindings before canonicalization or
//! `jj op abandon` changes their representation. A realization marker alone is no witness.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use musubi_jj::op_id::CanonicalOp;
use musubi_jj::op_id::LocalOp;
use musubi_sync::OpId;

use crate::identity::{HistoryKey, NativeOperation, SourceHeader, SourceKey};

use super::CommandSnapshot;
use super::GitRecordAuthorization;
use super::GitRecordInput;
use super::NativeOrigin;
use super::NativeOrigins;
use super::OperationSource;
use super::RetainedOperation;
use super::World;
use super::merge_key;
use super::operation_header;
use super::same_source_body;
use super::shared_origin_view;

/// Inputs captured before later actors can rewrite their native representation. The
/// baseline and join cuts identify the history being judged; command and operation sources
/// record what actually happened; workspace and publication witnesses qualify when that
/// source may explain a later result. Live actors and their recovery policy belong to World.
pub struct NativeEvidence {
    /// Names actually created in each copy, independent of the resulting hive namespace.
    pub workspace_births: BTreeSet<String>,
    pub initial_workspace_keys: BTreeSet<String>,
    /// Each machine's operation ids and keys once the hive was set up.
    pub(super) baseline_ids: Vec<BTreeSet<String>>,
    pub baseline_keys: Vec<BTreeSet<HistoryKey>>,
    /// Each copy's join point, observed before joining, apart from its parents.
    pub(super) join_points: Vec<OpId>,
    /// Actual native inputs captured before the fixture joins or adds a copy.
    pub(super) join_inputs: Vec<OpId>,
    /// The keys of every machine's operations once the hive was set up: what a copy made
    /// later has of them is its baseline too.
    pub(super) hive_baseline: BTreeSet<HistoryKey>,
    pub(super) baseline_merge_keys: BTreeSet<SourceKey>,
    /// Operations a `jj op abandon` rewrote, by `merge_key`, with their preserved views
    /// and whether each was a realization. Their new parents need not explain those views.
    pub kept_operations: BTreeMap<SourceKey, RetainedOperation>,
    pub(super) operation_sources: BTreeMap<(usize, SourceKey), Option<OperationSource>>,
    pub(super) operation_seen: Vec<BTreeSet<jj_lib::op_store::OperationId>>,
    pub(super) native_origins: Vec<NativeOrigins>,
    pub(super) published_seen: BTreeSet<CanonicalOp>,
    pub(super) published_headers: BTreeSet<SourceHeader>,
    pub commands: BTreeMap<SourceKey, CommandSnapshot>,
    /// Owned native bindings observed before each replacement copy joins. Its synthetic
    /// join has different metadata from the native prejoin head.
    pub workspace_joins: BTreeMap<SourceKey, BTreeMap<String, CommitId>>,
    /// The object and jj metadata stores of command sources, including copies later
    /// replaced. The fixture retains their directories until the case ends.
    pub command_sources: BTreeMap<PathBuf, PathBuf>,
}

impl World {
    /// The source history before a command. Keys also recognize operations an abandon
    /// rewrites without changing their metadata, so those are not mistaken for new work.
    pub(super) fn command_history(&self, m: usize) -> BTreeSet<SourceKey> {
        let store = self.fx.hive.members[m].adapter.repo().loader().op_store();
        let mut pending = self.op_heads(m);
        let mut seen = BTreeSet::new();
        let mut keys = BTreeSet::new();
        while let Some(head) = pending.pop() {
            if !seen.insert(head.clone()) {
                continue;
            }
            let id = jj_lib::op_store::OperationId::try_from_hex(&head).unwrap();
            let op = futures::executor::block_on(store.read_operation(&id)).unwrap();
            keys.insert(merge_key(&op));
            pending.extend(op.parents.iter().map(jj_lib::object_id::ObjectId::hex));
        }
        keys
    }

    /// Preserve every new native effect, including one written before a refusal.
    pub(super) fn record_commands(&mut self, m: usize, history_before: &BTreeSet<SourceKey>) {
        let store = self.fx.hive.members[m]
            .adapter
            .repo()
            .loader()
            .op_store()
            .clone();
        let mut pending = self.op_heads(m);
        let mut seen = BTreeSet::new();
        while let Some(head) = pending.pop() {
            if !seen.insert(head.clone()) {
                continue;
            }
            let id = jj_lib::op_store::OperationId::try_from_hex(&head).unwrap();
            let op = futures::executor::block_on(store.read_operation(&id)).unwrap();
            if history_before.contains(&merge_key(&op)) {
                continue;
            }
            // A command can first write a snapshot or import, then its requested work.
            // Record the complete new interval, not just its final operation head.
            pending.extend(op.parents.iter().map(jj_lib::object_id::ObjectId::hex));
            let [parent] = op.parents.as_slice() else {
                continue;
            };
            // A command can trigger jj's automatic reconciliation before doing no work.
            // Such a merge must still be compared with jj, never trusted as a payload.
            if NativeOperation::of(&op) == NativeOperation::Reconciliation {
                continue;
            }
            let snapshot = futures::executor::block_on(async {
                let parent_id = parent.clone();
                let parent = store.read_operation(&parent_id).await.unwrap();
                let input = self.fx.hive.members[m]
                    .adapter
                    .repo()
                    .canonical_of(&LocalOp(parent_id.clone()))
                    .filter(|input| {
                        self.fx.hive.members[m]
                            .adapter
                            .repo()
                            .canonical_store()
                            .read_operation(input)
                            .is_ok_and(|canonical| merge_key(&canonical) == merge_key(&parent))
                            || self.baseline_operation(&merge_key(&parent))
                    });
                CommandSnapshot {
                    parent: parent_id,
                    input,
                    predecessors: op.commit_predecessors.clone(),
                    id: id.clone(),
                    copy: self.fx.machine_key(m),
                    copies: self
                        .evidence
                        .workspace_births
                        .iter()
                        .filter_map(|key| key.split_once('/').map(|(copy, _)| copy.to_owned()))
                        .collect(),
                    base: store.read_view(&parent.view_id).await.unwrap(),
                    made: store.read_view(&op.view_id).await.unwrap(),
                }
            });
            let repo = self.fx.repo(m);
            self.evidence.command_sources.insert(
                repo.path().join(".git/objects"),
                repo.repo_path().join("store/extra"),
            );
            // Later rewrites keep the same key; retain the actual command's first input.
            if let std::collections::btree_map::Entry::Vacant(entry) =
                self.evidence.commands.entry(merge_key(&op))
            {
                entry.insert(snapshot);
            }
        }
    }

    pub(super) fn git_record_input(&self, m: usize) -> Option<GitRecordInput> {
        if m >= self.imports.preserved_heads.len() {
            return None;
        }
        let authorization = GitRecordAuthorization::PrivateWorkspaces(self.private_git_names(m)?);
        let node = self.fx.hive.members[m].adapter.repo();
        let heads: Vec<_> = self
            .op_heads(m)
            .iter()
            .map(|s| OpId::try_from_hex(s).unwrap())
            .collect();
        let mut before = BTreeSet::new();
        let mut todo = heads.clone();
        while let Some(id) = todo.pop() {
            if before.insert(id.clone()) {
                let op = futures::executor::block_on(node.loader().op_store().read_operation(&id))
                    .ok()?;
                todo.extend(op.parents);
            }
        }
        Some(GitRecordInput {
            copy: self.fx.machine_key(m),
            target: self.fx.hive.hub.store().head().1.clone(),
            heads,
            before,
            authorization,
        })
    }

    /// The search creates plain workspace names, recording their births independently.
    /// A known forgotten copy may preserve their current Git fields.
    pub(super) fn private_git_names(&self, m: usize) -> Option<BTreeSet<String>> {
        let copy = self.fx.machine_key(m);
        let presence = self.fx.hive.hub.store().presence().ok()?;
        if !presence.known().contains(&copy) || presence.is_present(&copy) {
            return None;
        }
        let store = self.fx.hive.members[m].adapter.repo().loader().op_store();
        let mut common: Option<BTreeSet<String>> = None;
        for id in self.op_heads(m) {
            let id = OpId::try_from_hex(&id)?;
            let op = futures::executor::block_on(store.read_operation(&id)).ok()?;
            let view = futures::executor::block_on(store.read_view(&op.view_id)).ok()?;
            let names = view
                .wc_commit_ids
                .keys()
                .filter(|name| {
                    !name.as_str().contains('/')
                        && self
                            .evidence
                            .workspace_births
                            .contains(&format!("{copy}/{}", name.as_str()))
                })
                .map(|name| name.as_str().to_owned())
                .collect::<BTreeSet<_>>();
            common = Some(match common {
                Some(old) => old.intersection(&names).cloned().collect(),
                None => names,
            });
        }
        common.filter(|names| !names.is_empty())
    }

    pub(super) fn finish_git_record_input(&mut self, m: usize, input: Option<GitRecordInput>) {
        let Some(input) = input.filter(|input| input.copy == self.fx.machine_key(m)) else {
            return;
        };
        let store = self.fx.hive.members[m].adapter.repo().loader().op_store();
        let mut todo: Vec<_> = self
            .op_heads(m)
            .iter()
            .map(|s| OpId::try_from_hex(s).unwrap())
            .collect();
        let mut seen = input.before;
        while let Some(id) = todo.pop() {
            if !seen.insert(id.clone()) {
                continue;
            }
            let Ok(op) = futures::executor::block_on(store.read_operation(&id)) else {
                continue;
            };
            todo.extend(op.parents.iter().cloned());
            if op
                .metadata
                .attributes
                .get(musubi_jj::node::CANONICAL_ATTRIBUTE)
                .is_some_and(|target| *target == input.target.hex())
            {
                let GitRecordAuthorization::PrivateWorkspaces(names) = &input.authorization;
                let Ok(view) = futures::executor::block_on(store.read_view(&op.view_id)) else {
                    continue;
                };
                if !view
                    .wc_commit_ids
                    .keys()
                    .any(|name| names.contains(name.as_str()))
                {
                    continue;
                }
                self.imports.preserved_heads[m]
                    .entry(id)
                    .or_insert_with(|| crate::imports::PreservedHeadInput {
                        carrier: op,
                        heads: input.heads.clone(),
                    });
            }
        }
    }

    /// Observe operations before and after receipt too. A publisher cannot observe an
    /// offline copy's old operation, but `jj op abandon` keeps its view while reparenting it.
    pub(super) fn observe_operation_sources(&mut self, m: usize) {
        self.observe_native_origins(m);
        self.evidence
            .operation_seen
            .resize_with(self.nodes(), BTreeSet::new);
        let store = self.fx.hive.members[m]
            .adapter
            .repo()
            .loader()
            .op_store()
            .clone();
        let mut pending = self.op_heads(m);
        let mut found = BTreeMap::<SourceKey, Vec<jj_lib::op_store::Operation>>::new();
        while let Some(hex) = pending.pop() {
            let id = jj_lib::op_store::OperationId::try_from_hex(&hex).unwrap();
            if !self.evidence.operation_seen[m].insert(id.clone()) {
                continue;
            }
            let op = futures::executor::block_on(store.read_operation(&id)).unwrap();
            pending.extend(op.parents.iter().map(jj_lib::object_id::ObjectId::hex));
            let key = merge_key(&op);
            found.entry(key).or_default().push(op);
        }
        for (key, versions) in found {
            let [op] = versions.as_slice() else {
                self.evidence.operation_sources.insert((m, key), None);
                continue;
            };
            let source_key = (m, key.clone());
            match self.evidence.operation_sources.get(&source_key) {
                Some(Some(source)) if source.operation.parents != op.parents => {
                    if same_source_body(&source.operation, op) {
                        let retained = source.retained.clone();
                        self.remember_retained(key, retained);
                    } else {
                        // Equal time/description alone does not identify an original.
                        self.evidence.operation_sources.insert(source_key, None);
                    }
                }
                Some(_) => {}
                None => {
                    let retained = self.retained_source(m, op);
                    self.evidence.operation_sources.insert(
                        source_key,
                        Some(OperationSource {
                            operation: op.clone(),
                            retained,
                        }),
                    );
                }
            }
        }
    }

    /// Observe native creation independently of work ownership: a copy can write a
    /// repair carrying another copy's last-use marker. Freeze already established original
    /// identities before caches or native files disappear; never mint one to observe it.
    pub(super) fn observe_native_origins(&mut self, m: usize) {
        self.evidence
            .native_origins
            .resize_with(self.nodes(), NativeOrigins::default);
        let copy = self.fx.machine_key(m);
        if self.evidence.native_origins[m].copy != copy {
            self.evidence.native_origins[m] = NativeOrigins {
                copy,
                ..NativeOrigins::default()
            };
        }
        let node = self.fx.hive.members[m].adapter.repo();
        let store = node.loader().op_store().clone();
        for file in fs::read_dir(node.repo_path().join("op_store/operations"))
            .unwrap()
            .flatten()
        {
            let Some(id) = file.file_name().to_str().and_then(OpId::try_from_hex) else {
                continue;
            };
            if self.evidence.native_origins[m].seen.contains(&id) {
                continue;
            }
            let Ok(op) = futures::executor::block_on(store.read_operation(&id)) else {
                continue;
            };
            if !op
                .metadata
                .attributes
                .contains_key(musubi_jj::node::CANONICAL_ATTRIBUTE)
            {
                let Ok(view) = futures::executor::block_on(store.read_view(&op.view_id)) else {
                    continue;
                };
                self.evidence.native_origins[m]
                    .pending
                    .insert(id.clone(), (op, shared_origin_view(view)));
            }
            self.evidence.native_origins[m].seen.insert(id);
        }
        let learned: Vec<_> = self.evidence.native_origins[m]
            .pending
            .keys()
            .filter_map(|id| {
                self.known_original(m, id)
                    .map(|original| (id.clone(), original))
            })
            .collect();
        for (id, original) in learned {
            let (op, view) = self.evidence.native_origins[m].pending.remove(&id).unwrap();
            self.evidence.native_origins[m]
                .known
                .entry(original)
                .or_default()
                .push(NativeOrigin {
                    header: operation_header(&op),
                    view,
                });
        }
    }

    /// A canonical marker names an alias, not its native author. Only independently
    /// observed local creation of this original and unchanged shared payload establish
    /// native origin. Work ownership and hostnames cannot identify the maker.
    pub(crate) fn realized(
        &self,
        m: usize,
        id: &CanonicalOp,
        op: &jj_lib::op_store::Operation,
    ) -> bool {
        if !op
            .metadata
            .attributes
            .contains_key(musubi_jj::node::CANONICAL_ATTRIBUTE)
        {
            return false;
        }
        let Some(origins) = self
            .evidence
            .native_origins
            .get(m)
            .filter(|origins| origins.copy == self.fx.machine_key(m))
        else {
            return true;
        };
        let Some(original) = self
            .fx
            .hive
            .members
            .iter()
            .find_map(|member| member.adapter.repo().canonical_store().original_id(id).ok())
        else {
            return true;
        };
        let Some(witnesses) = origins.known.get(&original) else {
            return true;
        };
        let node = self.fx.hive.members[m].adapter.repo();
        let Ok(view) = futures::executor::block_on(node.loader().op_store().read_view(&op.view_id))
        else {
            return true;
        };
        let shared = shared_origin_view(view);
        !witnesses
            .iter()
            .any(|source| source.header == operation_header(op) && source.view == shared)
    }

    /// Unambiguous native bodies observed before rewriting, excluding marked renderings.
    pub fn captured_record_sources(
        &self,
        m: usize,
    ) -> BTreeMap<SourceKey, jj_lib::op_store::Operation> {
        self.evidence
            .operation_sources
            .iter()
            .filter_map(|((machine, key), source)| {
                let source = source.as_ref()?;
                (*machine == m
                    && !source
                        .operation
                        .metadata
                        .attributes
                        .contains_key(musubi_jj::node::CANONICAL_ATTRIBUTE))
                .then(|| (key.clone(), source.operation.clone()))
            })
            .collect()
    }

    pub(super) fn remember_retained(&mut self, key: SourceKey, source: RetainedOperation) {
        // A later abandon must not replace the original input with an already-reparented one.
        // An own operation knows that input; a received realization has a different parent.
        self.evidence
            .kept_operations
            .entry(key)
            .and_modify(|before| {
                if source.native && !before.native || before.realized && !source.realized {
                    *before = source.clone();
                }
            })
            .or_insert(source);
    }

    pub(super) fn retained_source(
        &self,
        m: usize,
        op: &jj_lib::op_store::Operation,
    ) -> RetainedOperation {
        let repo = self.fx.hive.members[m].adapter.repo();
        let store = repo.loader().op_store();
        let parent = if let [id] = op.parents.as_slice() {
            let parent = futures::executor::block_on(store.read_operation(id)).unwrap();
            Some(futures::executor::block_on(store.read_view(&parent.view_id)).unwrap())
        } else {
            None
        };
        RetainedOperation::capture(
            self.fx.machine_key(m),
            op,
            futures::executor::block_on(store.read_view(&op.view_id)).unwrap(),
            op.metadata
                .attributes
                .get(musubi_jj::node::CANONICAL_ATTRIBUTE)
                .and_then(OpId::try_from_hex)
                .map(CanonicalOp)
                .is_some_and(|id| self.realized(m, &id, op)),
            parent,
        )
    }

    /// Records the commits node `m`'s merges made, after a sync.
    pub fn record_merges(&mut self, m: usize) {
        self.observe_operation_sources(m);
        self.observe_published_operations();
        self.resolve_retained_operations(m);
        let after = self.seen(m);
        let what = format!("{}: merge by its node", self.machine(m));
        self.ledger.record_sync(m, &what, &after);
    }

    /// Remember only histories actually accepted by the hub, including ones a later
    /// rollback or `jj op abandon` removes. A local command with similar metadata is not
    /// publication.
    pub(super) fn observe_published_operations(&mut self) {
        let store = self.fx.hive.hub.store();
        let canonical = store.canonical();
        let mut pending = vec![CanonicalOp(store.head().1.clone())];
        while let Some(id) = pending.pop() {
            if !self.evidence.published_seen.insert(id.clone()) {
                continue;
            }
            let op = canonical.read_operation(&id).unwrap();
            self.evidence
                .published_headers
                .insert(operation_header(&op));
            pending.extend(op.parents.into_iter().map(CanonicalOp));
        }
    }

    /// Native abandonment can leave another alias whose mapping musubi has not yet read.
    /// Resolve only frozen native survivors, including exact links through later native
    /// abandons. This cannot excuse an alias created by a sync that resurrected the operation.
    fn resolve_retained_operations(&mut self, m: usize) {
        let copy = self.fx.machine_key(m);
        let mut learned = vec![];
        for (i, op) in self.abandoned.iter().enumerate() {
            for key in op
                .native_witnesses
                .keys()
                .filter(|(owner, _)| *owner == copy)
            {
                if let Some(original) = self.known_original(m, &key.1) {
                    learned.push((i, key.clone(), original));
                }
            }
        }
        for (i, key, original) in learned {
            self.abandoned[i].qualify_native(&key, original);
        }
        // A private operation may first acquire a mapping during the sync. Learning the
        // identity of the exact removed source strengthens its obligation; it never excuses
        // a new rendering. Keep a published source's pre-fault identity unchanged.
        let newly_known: Vec<_> = self
            .abandoned
            .iter()
            .enumerate()
            .filter_map(|(i, op)| {
                (op.copy == copy && !op.shared && op.originals.is_none())
                    .then(|| self.known_original(m, &op.native).map(|id| (i, id)))
                    .flatten()
            })
            .collect();
        for (i, id) in newly_known {
            self.abandoned[i].originals = Some(BTreeSet::from([id]));
        }
        let resolved: BTreeSet<_> = self
            .abandoned
            .iter()
            .enumerate()
            .filter_map(|(i, op)| {
                let wanted = op.originals.as_ref()?;
                (op.native_witnesses
                    .values()
                    .flatten()
                    .any(|id| wanted.contains(id)))
                .then_some(i)
            })
            .collect();
        let mut i = 0;
        self.abandoned.retain(|_| {
            let keep = !resolved.contains(&i);
            i += 1;
            keep
        });
    }
}
