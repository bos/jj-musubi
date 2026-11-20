//! Native jj execution from independently authenticated inputs.
//!
//! Ordinary merges use the copied canonical parents. Native workspace projections are
//! eligible only when their source names and bindings have certificates; the full shared
//! result must still agree structurally. The candidate merge payload never certifies itself.

use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs;
use std::sync::Arc;

use futures::executor::block_on;
use jj_lib::backend::ChangeId;
use jj_lib::backend::CommitId;
use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::View;
use jj_lib::operation::Operation;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::repo::ReadonlyRepo;
use musubi_jj::node::NodeRepo;
use musubi_jj::op_id::CanonicalOp;
use musubi_jj::op_id::LocalOp;

use super::Reference;
use super::settings;
use super::witnesses::{RejectionCause, WitnessFailures, WitnessKind, WitnessRejection};
use super::workspaces::WorkspaceCertificate;
use super::workspaces::foreign_alias_absent;
use crate::world::World;
use crate::world::merge_key;

#[derive(Default)]
pub(super) struct WorkspaceCandidates {
    pub(super) replays: Vec<WorkspaceReplay>,
    pub(super) rejections: WitnessFailures,
}

pub(super) struct WorkspaceReplay {
    pub(super) view: View,
    pub(super) parents: Vec<View>,
    pub(super) private: Option<(String, View)>,
}

/// A canonical parent paired with the independent certificate that qualifies its bindings.
#[derive(Clone, Copy)]
pub(super) struct CertifiedParent<'a> {
    pub(super) canonical: &'a CanonicalOp,
    pub(super) certificate: &'a WorkspaceCertificate,
}

/// The canonical inputs whose certificates may justify a native workspace projection.
struct PrivateMergeRequest<'a> {
    id: &'a CanonicalOp,
    parents: [CertifiedParent<'a>; 2],
    frontier_names: BTreeSet<String>,
}

struct ProjectedBase {
    canonical: CanonicalOp,
    view: View,
}

struct ProjectedParent {
    operation: Operation,
    view: View,
}

/// All bases and both ordered parents have passed the source and certificate checks.
/// Construction reads only those inputs; the maker's result is read after native replay.
struct ProjectedMergeInputs {
    maker_operation: Operation,
    bases: Vec<ProjectedBase>,
    parents: [ProjectedParent; 2],
}

#[derive(Default)]
struct WorkspaceReplayCache {
    merges: HashMap<(OperationId, OperationId, OperationId), View>,
    bases: HashMap<Vec<OperationId>, Operation>,
}

/// A copy's shared absence cannot delete its private namespace. Only this merge's
/// authenticated input names may bridge that omission; the raw owned slot supplies the
/// proposed binding, which the caller still has jj replay and compare structurally.
pub(super) fn project_private_workspaces<'a>(
    canonical: &mut View,
    native: &View,
    maker: &str,
    source_names: impl IntoIterator<Item = &'a String>,
    frontier_names: &'a BTreeSet<String>,
    absent: bool,
) {
    canonical.wc_commit_ids.retain(|key, _| {
        !key.as_str()
            .split_once('/')
            .is_some_and(|(owner, _)| owner == maker)
    });
    for key in source_names
        .into_iter()
        .chain(frontier_names.iter().filter(|_| absent))
    {
        let Some((owner, workspace)) = key.split_once('/') else {
            continue;
        };
        if owner == maker
            && let Some(target) = native.wc_commit_ids.get(WorkspaceName::new(workspace))
        {
            canonical
                .wc_commit_ids
                .insert(key.clone().into(), target.clone());
        }
    }
}

/// An operation the reference made, with its view.
pub(super) struct Replayed {
    pub(super) op: Operation,
    pub(super) view: View,
}

impl Replayed {
    pub(super) fn of(repo: &Arc<ReadonlyRepo>) -> Self {
        Self {
            op: repo.operation().clone(),
            view: repo.view().store_view().clone(),
        }
    }
}

impl Reference {
    /// Replay an authenticated local merge with that copy's actual owned bindings, for
    /// independently certified names. Foreign native rewrites can differ from canonical
    /// bindings, and membership forgets omit private slots centrally.
    /// Realizations are eligible too: their marker is no evidence, but their authenticated
    /// parents and base can independently witness the same merge through native jj.
    pub(super) fn workspace_private_replays(
        &mut self,
        world: &World,
        id: &CanonicalOp,
        parents: &[CertifiedParent<'_>],
    ) -> Vec<WorkspaceReplay> {
        self.workspace_private_candidates(world, id, parents)
            .replays
    }

    /// Keep the failed prerequisites alongside qualified candidates for final adjudication.
    /// The certificate builder needs only the candidates, so its wrapper discards diagnostics.
    pub(super) fn workspace_private_candidates(
        &mut self,
        world: &World,
        id: &CanonicalOp,
        parents: &[CertifiedParent<'_>],
    ) -> WorkspaceCandidates {
        let kind = WitnessKind::CertifiedPrivateBindings;
        let mut candidates = WorkspaceCandidates::default();
        if parents.len() != 2 {
            candidates.rejections.reject(
                kind,
                None,
                RejectionCause::TwoParentsRequired {
                    found: parents.len(),
                },
            );
            return candidates;
        }
        let request = PrivateMergeRequest {
            id,
            parents: [parents[0], parents[1]],
            frontier_names: parents
                .iter()
                .flat_map(|input| input.certificate.names().cloned())
                .collect(),
        };
        let mut cache = WorkspaceReplayCache::default();
        for member in &world.fx.hive.members {
            let node = member.adapter.repo();
            let maker = node.machine().key();
            let files = match fs::read_dir(node.repo_path().join("op_store/operations")) {
                Ok(files) => files,
                Err(error) => {
                    candidates.rejections.reject(
                        kind,
                        Some(maker),
                        RejectionCause::ReadFailed {
                            input: "the native operation directory",
                            error: error.to_string(),
                        },
                    );
                    continue;
                }
            };
            for file in files {
                let file = match file {
                    Ok(file) => file,
                    Err(error) => {
                        candidates.rejections.reject(
                            kind,
                            Some(maker),
                            RejectionCause::ReadFailed {
                                input: "a native operation directory entry",
                                error: error.to_string(),
                            },
                        );
                        continue;
                    }
                };
                let Some(local) = file
                    .file_name()
                    .to_str()
                    .and_then(OperationId::try_from_hex)
                    .map(LocalOp)
                else {
                    continue;
                };
                if !Self::source_aliases(world, node, &local).contains(id) {
                    continue;
                }
                let result = self
                    .qualify_workspace_merge(world, node, &local, &request)
                    .and_then(|inputs| {
                        self.replay_workspace_merge(world, maker, inputs, &mut cache)
                    });
                match result {
                    Ok(replay) => candidates.replays.push(replay),
                    Err(cause) => candidates.rejections.reject(kind, Some(maker), cause),
                }
            }
        }
        if candidates.replays.is_empty() && candidates.rejections.is_empty() {
            candidates
                .rejections
                .reject(kind, None, RejectionCause::NativeMakerMissing);
        }
        candidates
    }

    /// Qualify one mapped native candidate, preserving its ordered parent frontier and
    /// independently certified bases. No candidate result is used to project these inputs.
    fn qualify_workspace_merge(
        &mut self,
        world: &World,
        node: &NodeRepo,
        local: &LocalOp,
        request: &PrivateMergeRequest<'_>,
    ) -> Result<ProjectedMergeInputs, RejectionCause> {
        let operation =
            block_on(node.loader().op_store().read_operation(&local.0)).map_err(|error| {
                RejectionCause::ReadFailed {
                    input: "the mapped native operation",
                    error: error.to_string(),
                }
            })?;
        if operation.parents.len() != 2 {
            return Err(RejectionCause::TwoParentsRequired {
                found: operation.parents.len(),
            });
        }
        if !operation
            .parents
            .iter()
            .zip(request.parents)
            .all(|(raw, expected)| {
                Self::source_aliases(world, node, &LocalOp(raw.clone()))
                    .contains(expected.canonical)
            })
        {
            return Err(RejectionCause::OrderedParentsDiffer);
        }
        let local_op = block_on(node.loader().load_operation(&local.0)).map_err(|error| {
            RejectionCause::ReadFailed {
                input: "the mapped native operation",
                error: error.to_string(),
            }
        })?;
        let local_parents =
            block_on(local_op.parents()).map_err(|error| RejectionCause::ReadFailed {
                input: "the native parents",
                error: error.to_string(),
            })?;
        let bases = block_on(jj_lib::op_walk::closest_common_ancestors(
            vec![local_parents[0].clone()],
            [local_parents[1].clone()],
        ))
        .map_err(|error| RejectionCause::ReadFailed {
            input: "the native common bases",
            error: error.to_string(),
        })?;
        let base_ids = bases
            .iter()
            .map(|base| {
                Self::source_aliases(world, node, &LocalOp(base.id().clone()))
                    .into_iter()
                    .next()
            })
            .collect::<Option<Vec<_>>>()
            .ok_or(RejectionCause::BaseMappingMissing)?;
        if base_ids.is_empty() {
            return Err(RejectionCause::BaseSetEmpty);
        }
        if base_ids.contains(request.id) {
            return Err(RejectionCause::BaseIsCandidate);
        }
        if !self.workspace_dependencies_available(world, &base_ids) {
            return Err(RejectionCause::BaseCertificatesUnavailable);
        }
        let certificates = base_ids
            .iter()
            .map(|base| self.workspace_certificate(world, base))
            .collect::<Vec<_>>();
        let maker = node.machine().key();
        // Project every base first, then the ordered parents, stopping at the first
        // missing prerequisite. Keep the same observation order as native qualification.
        let bases = bases
            .iter()
            .zip(&base_ids)
            .zip(&certificates)
            .map(|((source, id), certificate)| {
                Ok(ProjectedBase {
                    canonical: id.clone(),
                    view: self.project_workspace_input(
                        world,
                        maker,
                        source,
                        id,
                        certificate,
                        &request.frontier_names,
                    )?,
                })
            })
            .collect::<Result<Vec<_>, RejectionCause>>()?;
        let parent = |index: usize| -> Result<ProjectedParent, RejectionCause> {
            Ok(ProjectedParent {
                operation: local_parents[index].clone(),
                view: self.project_workspace_input(
                    world,
                    maker,
                    &local_parents[index],
                    request.parents[index].canonical,
                    request.parents[index].certificate,
                    &request.frontier_names,
                )?,
            })
        };
        let parents = [parent(0)?, parent(1)?];
        Ok(ProjectedMergeInputs {
            maker_operation: local_op,
            bases,
            parents,
        })
    }

    /// Project one authenticated native input onto its checked canonical view. Only
    /// certified names may carry the maker's private bindings across a shared omission.
    fn project_workspace_input(
        &self,
        world: &World,
        maker: &str,
        source: &Operation,
        canonical_id: &CanonicalOp,
        certificate: &WorkspaceCertificate,
        frontier_names: &BTreeSet<String>,
    ) -> Result<View, RejectionCause> {
        let canonical = Self::workspace_source(world, canonical_id)
            .ok_or(RejectionCause::CanonicalInputMissing)?;
        let mut view = world
            .fx
            .hive
            .members
            .iter()
            .find_map(|member| {
                member
                    .adapter
                    .repo()
                    .canonical_store()
                    .read_view(&canonical.view_id)
                    .ok()
            })
            .ok_or(RejectionCause::CanonicalViewMissing)?;
        let raw = block_on(source.view()).map_err(|error| RejectionCause::ReadFailed {
            input: "an authenticated native input view",
            error: error.to_string(),
        })?;
        let absent = world
            .fx
            .hive
            .members
            .iter()
            .find_map(|member| member.adapter.repo().presence(canonical_id).ok())
            .is_some_and(|presence| !presence.is_present(maker));
        project_private_workspaces(
            &mut view,
            raw.store_view(),
            maker,
            certificate.names(),
            frontier_names,
            absent,
        );
        Ok(view)
    }

    /// Execute only qualified inputs. Preserve the native base graph and jj's base order;
    /// the maker's result is read last and cannot influence the projected replay inputs.
    fn replay_workspace_merge(
        &mut self,
        world: &World,
        maker: &str,
        inputs: ProjectedMergeInputs,
        cache: &mut WorkspaceReplayCache,
    ) -> Result<WorkspaceReplay, RejectionCause> {
        let ProjectedMergeInputs {
            maker_operation,
            bases,
            parents: [left, right],
        } = inputs;
        let base_copy = if bases.len() == 1 {
            let root = block_on(self.loader.root_operation());
            self.write_like(&root, &bases[0].view, vec![root.id().clone()])
        } else {
            let copies = bases
                .iter()
                .map(|base| {
                    let copy = self.workspace_copy(world, &base.canonical)?;
                    Some(self.write_like(&copy, &base.view, copy.parent_ids().to_vec()))
                })
                .collect::<Option<Vec<_>>>()
                .ok_or(RejectionCause::CopiedInputMissing)?;
            let key = copies.iter().map(|op| op.id().clone()).collect::<Vec<_>>();
            cache
                .bases
                .entry(key)
                .or_insert_with(|| self.merge(copies.iter().collect()).op)
                .clone()
        };
        let left_copy = self.write_like(&left.operation, &left.view, vec![base_copy.id().clone()]);
        let right_copy =
            self.write_like(&right.operation, &right.view, vec![base_copy.id().clone()]);
        let input = (
            base_copy.id().clone(),
            left_copy.id().clone(),
            right_copy.id().clone(),
        );
        let merged = if let Some(view) = cache.merges.get(&input) {
            view.clone()
        } else {
            let view = self.merge(vec![&left_copy, &right_copy]).view;
            cache.merges.insert(input, view.clone());
            view
        };
        let made =
            block_on(maker_operation.view()).map_err(|error| RejectionCause::ReadFailed {
                input: "the native maker's result",
                error: error.to_string(),
            })?;
        Ok(WorkspaceReplay {
            view: merged,
            parents: vec![left.view, right.view],
            private: Some((maker.to_owned(), made.store_view().clone())),
        })
    }

    /// jj's merge of `parents`, in their order.
    pub(super) fn merge(&self, parents: Vec<&Operation>) -> Replayed {
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
    pub(super) fn apply(&self, base: &Operation, op: &Operation, onto: &Operation) -> Replayed {
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
    /// only where they lacked nothing else. An exact captured native input can also omit
    /// an independently certified foreign slot while keeping its commit visible: whether a
    /// commit is a working copy changes jj's merge too. A later workspace birth cannot prove
    /// that omission; owned literals must be certified at the input itself.
    /// The merge then gets back the commits jj's merge of
    /// the hive's parents (`canonical`) keeps. Reject where there is no workspace-only
    /// omission to explain, or the merge has several bases.
    pub(super) fn merged_as_made(
        &mut self,
        world: &World,
        id: &CanonicalOp,
        parents: &[CanonicalOp],
        canonical: &View,
        copies: &HashMap<CanonicalOp, Operation>,
        views: &HashMap<CanonicalOp, View>,
    ) -> Result<(View, &'static str), WitnessRejection> {
        let kind = WitnessKind::CapturedMakerInputs;
        // The machine that made the merge, rather than realized it, and the merge there.
        let (m, node, local_op) = world
            .fx
            .hive
            .members
            .iter()
            .enumerate()
            .find_map(|(m, member)| {
                let node = member.adapter.repo();
                let local = node.local_of(id)?;
                let local_op = block_on(node.loader().load_operation(&local.0)).unwrap();
                let made = !world.realized(m, id, local_op.store_operation());
                made.then_some((m, node, local_op))
            })
            .ok_or_else(|| WitnessRejection::new(kind, None, RejectionCause::NativeMakerMissing))?;
        let reject = |cause| WitnessRejection::new(kind, Some(world.machine(m)), cause);
        let local_parents = block_on(local_op.parents()).unwrap();
        let [first, second] = local_parents.as_slice() else {
            return Err(reject(RejectionCause::TwoParentsRequired {
                found: local_parents.len(),
            }));
        };
        // The same parents, in the same order.
        let canonical_parents: Vec<Option<CanonicalOp>> = local_parents
            .iter()
            .map(|parent| node.canonical_of(&LocalOp(parent.id().clone())))
            .collect();
        if canonical_parents
            .iter()
            .cloned()
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| reject(RejectionCause::ParentMappingMissing))?
            != parents
        {
            return Err(reject(RejectionCause::OrderedParentsDiffer));
        }
        let bases = block_on(jj_lib::op_walk::closest_common_ancestors(
            vec![first.clone()],
            [second.clone()],
        ))
        .unwrap();
        let [base] = bases.as_slice() else {
            return Err(reject(RejectionCause::SingleBaseRequired {
                found: bases.len(),
            }));
        };
        let mut kept: HashSet<CommitId> = HashSet::new();
        let mut omitted_workspace = false;
        let mut as_had = vec![];
        for local in [base, first, second] {
            let canonical_id = node
                .canonical_of(&LocalOp(local.id().clone()))
                .ok_or_else(|| reject(RejectionCause::InputMappingMissing))?;
            let local_view = block_on(local.view()).unwrap().store_view().clone();
            let mut view = views
                .get(&canonical_id)
                .ok_or_else(|| reject(RejectionCause::CheckedInputMissing))?
                .clone();
            let working_copies: HashSet<CommitId> = view.wc_commit_ids.values().cloned().collect();
            // Forgetting a foreign alias locally leaves its canonical slot intact. Even
            // with identical visible heads, that slot changes which empty working copies
            // jj abandons while merging. Use only an independently captured native input,
            // and omit only an existing certified foreign slot absent from that input.
            if let Some(command) = world
                .evidence
                .commands
                .get(&merge_key(local.store_operation()))
                && command.id == *local.id()
                && command.copy == node.machine().key()
            {
                let certificate = self.workspace_certificate(world, &canonical_id);
                view.wc_commit_ids.retain(|key, target| {
                    let absent = certificate.binding(key.as_str()) == Some(target)
                        && foreign_alias_absent(
                            command,
                            |name| certificate.has_name(name),
                            key.as_str(),
                        );
                    omitted_workspace |= absent;
                    !absent
                });
            }
            let visible = self.visible(&view);
            if !local_view
                .head_ids
                .iter()
                .all(|head| visible.contains(head))
            {
                return Err(reject(RejectionCause::InputAddsVisibleCommits));
            }
            let lacked: HashSet<CommitId> = visible
                .difference(&self.visible(&local_view))
                .cloned()
                .collect();
            if !lacked.iter().all(|commit| working_copies.contains(commit)) {
                return Err(reject(RejectionCause::InputOmitsNonWorkspaceCommits));
            }
            view.head_ids = local_view.head_ids.clone();
            view.wc_commit_ids
                .retain(|_, commit| !lacked.contains(commit));
            kept.extend(lacked);
            let copy = copies
                .get(&canonical_id)
                .ok_or_else(|| reject(RejectionCause::CopiedInputMissing))?;
            as_had.push(self.write_like(copy, &view, copy.parent_ids().to_vec()));
        }
        if kept.is_empty() && !omitted_workspace {
            return Err(reject(RejectionCause::WorkspaceOmissionMissing));
        }
        let [base, first, second] = as_had.as_slice() else {
            unreachable!()
        };
        let mut merged = self.apply(base, second, first).view;
        let canonical = self.visible(canonical);
        merged
            .head_ids
            .extend(kept.into_iter().filter(|commit| canonical.contains(commit)));
        Ok((merged, world.machine(m)))
    }

    /// Replay the actual native DAG and index when rebuilding its views in the
    /// reference changes jj's result. Every parent and closest base must independently
    /// agree with an already checked shared input. The merge payload is never an input.
    pub(super) fn native_merge_matches(
        &mut self,
        world: &World,
        id: &CanonicalOp,
        parents: &[CanonicalOp],
        output: &View,
        known: &HashSet<ChangeId>,
        views: &HashMap<CanonicalOp, View>,
    ) -> Result<&'static str, WitnessFailures> {
        let kind = WitnessKind::NativeDag;
        let mut failures = WitnessFailures::default();
        for (m, member) in world.fx.hive.members.iter().enumerate() {
            let node = member.adapter.repo();
            let machine = world.machine(m);
            let Some(local) = node.local_of(id) else {
                continue;
            };
            let operation = block_on(node.loader().load_operation(&local.0)).map_err(|error| {
                failures.stopped(
                    kind,
                    machine,
                    RejectionCause::ReadFailed {
                        input: "the mapped native operation",
                        error: error.to_string(),
                    },
                )
            })?;
            if operation
                .metadata()
                .attributes
                .contains_key(musubi_jj::node::CANONICAL_ATTRIBUTE)
            {
                failures.reject(kind, Some(machine), RejectionCause::RealizationIsNotMaker);
                continue;
            }
            // A later `jj op abandon`, or musubi reparenting this machine's operations to
            // match the hive's contraction, gives a merge other parents and keeps its view,
            // which jj computed on the parents it had. So where the merge itself fails, each
            // native version of it, the same but for its parents, can witness it, qualifying
            // and replaying as the merge itself does. A version's parent may be an earlier
            // version of one of the merge's own: it stands for that parent's canonical op.
            let current = block_on(operation.parents()).map_err(|error| {
                failures.stopped(
                    kind,
                    machine,
                    RejectionCause::ReadFailed {
                        input: "the native parents",
                        error: error.to_string(),
                    },
                )
            })?;
            let stands_for = |input: &Operation| {
                node.canonical_of(&LocalOp(input.id().clone())).or_else(|| {
                    current
                        .iter()
                        .find(|parent| same_but_parents(parent, input))
                        .and_then(|parent| node.canonical_of(&LocalOp(parent.id().clone())))
                })
            };
            let mut pending = vec![operation.clone()];
            let mut earlier = false;
            loop {
                let Some(version) = pending.pop() else {
                    if earlier {
                        break;
                    }
                    earlier = true;
                    pending = native_versions(node, &operation).map_err(|error| {
                        failures.stopped(
                            kind,
                            machine,
                            RejectionCause::ReadFailed {
                                input: "the native versions of the merge",
                                error,
                            },
                        )
                    })?;
                    pending.reverse();
                    continue;
                };
                let label = if earlier {
                    format!("{machine}, version {}", &version.id().hex()[..12])
                } else {
                    machine.to_owned()
                };
                let machine = label.as_str();
                let native_parents = block_on(version.parents()).map_err(|error| {
                    failures.stopped(
                        kind,
                        machine,
                        RejectionCause::ReadFailed {
                            input: "the native parents",
                            error: error.to_string(),
                        },
                    )
                })?;
                if native_parents.len() != 2 {
                    failures.reject(
                        kind,
                        Some(machine),
                        RejectionCause::TwoParentsRequired {
                            found: native_parents.len(),
                        },
                    );
                    continue;
                }
                let mapped: Option<Vec<_>> = native_parents.iter().map(stands_for).collect();
                if mapped.as_deref() != Some(parents) {
                    let cause = if mapped.is_none() {
                        RejectionCause::ParentMappingMissing
                    } else {
                        RejectionCause::OrderedParentsDiffer
                    };
                    failures.reject(kind, Some(machine), cause);
                    continue;
                }
                let bases = block_on(jj_lib::op_walk::closest_common_ancestors(
                    vec![native_parents[0].clone()],
                    [native_parents[1].clone()],
                ))
                .map_err(|error| {
                    failures.stopped(
                        kind,
                        machine,
                        RejectionCause::ReadFailed {
                            input: "the native common bases",
                            error: error.to_string(),
                        },
                    )
                })?;
                // A recursive base merge consumes further views. Keep this fallback to one
                // independently qualified base; the other replay paths handle known omissions.
                if bases.len() != 1 {
                    failures.reject(
                        kind,
                        Some(machine),
                        RejectionCause::SingleBaseRequired { found: bases.len() },
                    );
                    continue;
                }
                // Translation keeps the merge's own native ancestry in the canonical graph,
                // but not an earlier version's: its base must still be below both parents.
                if earlier && let Some(base) = node.canonical_of(&LocalOp(bases[0].id().clone())) {
                    let mut shared = true;
                    for parent in parents {
                        shared &= node
                            .canonical_store()
                            .is_ancestor_of(&base, parent)
                            .map_err(|error| {
                                failures.stopped(
                                    kind,
                                    machine,
                                    RejectionCause::ReadFailed {
                                        input: "the canonical ancestry of the native base",
                                        error: error.to_string(),
                                    },
                                )
                            })?;
                    }
                    if !shared {
                        failures.reject(kind, Some(machine), RejectionCause::BaseNotShared);
                        continue;
                    }
                }
                let mut qualified = true;
                // A base stands only for itself: only parents have versions standing in.
                let inputs = native_parents
                    .iter()
                    .zip(parents.iter().cloned().map(Some))
                    .chain(
                        bases
                            .iter()
                            .map(|base| (base, node.canonical_of(&LocalOp(base.id().clone())))),
                    );
                for (input, mapped) in inputs {
                    let Some(mapped) = mapped else {
                        failures.reject(kind, Some(machine), RejectionCause::InputMappingMissing);
                        qualified = false;
                        break;
                    };
                    let Some(expected) = views.get(&mapped) else {
                        failures.reject(kind, Some(machine), RejectionCause::CheckedInputMissing);
                        qualified = false;
                        break;
                    };
                    let mut actual = block_on(input.view())
                        .map_err(|error| {
                            failures.stopped(
                                kind,
                                machine,
                                RejectionCause::ReadFailed {
                                    input: "an independently checked native input",
                                    error: error.to_string(),
                                },
                            )
                        })?
                        .store_view()
                        .clone();
                    let certificate = self.workspace_certificate(world, &mapped);
                    let presence = world
                        .fx
                        .hive
                        .members
                        .iter()
                        .find_map(|member| member.adapter.repo().presence(&mapped).ok())
                        .ok_or_else(|| {
                            failures.stopped(
                                kind,
                                machine,
                                RejectionCause::InputPresenceUnavailable,
                            )
                        })?;
                    let maker = node.machine().key();
                    // Workspace bindings influence jj's shared merge even when visible
                    // commits agree. Require a bijection with exact certified input slots;
                    // an opaque name alone cannot authorize a changed target or omission.
                    let mut matched = BTreeSet::new();
                    let bindings = actual.wc_commit_ids.len() == expected.wc_commit_ids.len()
                        && actual.wc_commit_ids.iter().all(|(raw, target)| {
                            let candidates = expected
                                .wc_commit_ids
                                .iter()
                                .filter(|(key, value)| {
                                    if *value != target
                                        || certificate.binding(key.as_str()) != Some(target)
                                    {
                                        return false;
                                    }
                                    let Some((owner, workspace)) = key.as_str().split_once('/')
                                    else {
                                        return false;
                                    };
                                    if owner == maker {
                                        return raw.as_str() == workspace;
                                    }
                                    let Some((prefix, shown)) = raw.as_str().split_once('/') else {
                                        return false;
                                    };
                                    shown == workspace
                                        && !certificate
                                            .has_name(&format!("{maker}/{}", raw.as_str()))
                                        && musubi_jj::workspaces::could_be_shown_as(owner, prefix)
                                        && presence
                                            .known()
                                            .iter()
                                            .filter(|copy| {
                                                musubi_jj::workspaces::could_be_shown_as(
                                                    copy, prefix,
                                                )
                                            })
                                            .count()
                                            == 1
                                })
                                .map(|(key, _)| key.clone())
                                .collect::<Vec<_>>();
                            match candidates.as_slice() {
                                [key] => matched.insert(key.clone()),
                                _ => false,
                            }
                        });
                    if !bindings {
                        failures.reject(
                            kind,
                            Some(machine),
                            RejectionCause::CertifiedInputBindingsDiffer,
                        );
                        qualified = false;
                        break;
                    }
                    actual.remote_views.remove(REMOTE_NAME_FOR_LOCAL_GIT_REPO);
                    if self.summary(&actual, known) != self.summary(expected, known) {
                        failures.reject(kind, Some(machine), RejectionCause::SharedInputDiffers);
                        qualified = false;
                        break;
                    }
                }
                if !qualified || bases.is_empty() {
                    continue;
                }
                let dir = musubi_testutil::tempdir();
                let root = dir.path().join("repo");
                musubi_testutil::copy_tree(world.fx.repo(m).path(), &root);
                let loader = default_backend_factories()
                    .load_repo(&settings(), &root.join(".jj/repo"))
                    .map_err(|error| {
                        failures.stopped(
                            kind,
                            machine,
                            RejectionCause::ReadFailed {
                                input: "the isolated native repository",
                                error: error.to_string(),
                            },
                        )
                    })?;
                let inputs = native_parents
                    .iter()
                    .map(|p| block_on(loader.load_operation(p.id())))
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|error| {
                        failures.stopped(
                            kind,
                            machine,
                            RejectionCause::ReadFailed {
                                input: "the isolated native parents",
                                error: error.to_string(),
                            },
                        )
                    })?;
                let (merged, _) = block_on(loader.merge_operations(
                    inputs,
                    None,
                    Some("reference native merge"),
                    [],
                ))
                .map_err(|error| {
                    failures.stopped(
                        kind,
                        machine,
                        RejectionCause::ReadFailed {
                            input: "the isolated native merge result",
                            error: error.to_string(),
                        },
                    )
                })?;
                let mut actual = merged.view().store_view().clone();
                actual.remote_views.remove(REMOTE_NAME_FOR_LOCAL_GIT_REPO);
                // Rebased commits exist only in this isolated store. Read their structural
                // facts there, with the reference's independent settings and random generator.
                let reference_loader = std::mem::replace(&mut self.loader, loader);
                let replayed = self.summary(&actual, known);
                self.loader = reference_loader;
                if replayed == self.summary(output, known) {
                    return Ok(world.machine(m));
                }
                failures.reject(kind, Some(machine), RejectionCause::StructuralResultDiffers);
            }
        }
        if failures.is_empty() {
            failures.reject(kind, None, RejectionCause::NativeMakerMissing);
        }
        Err(failures)
    }

    /// `op` with `view` instead, on `parents`.
    pub(super) fn write_like(
        &self,
        op: &Operation,
        view: &View,
        parents: Vec<OperationId>,
    ) -> Operation {
        let op_store = self.loader.op_store().clone();
        let written = op_store::Operation {
            view_id: block_on(op_store.write_view(view)).unwrap(),
            parents,
            ..op.store_operation().clone()
        };
        let id = block_on(op_store.write_operation(&written)).unwrap();
        block_on(self.loader.load_operation(&id)).unwrap()
    }
}

/// The operations in `node`'s store that are `op` but for their parents, as jj's and musubi's
/// reparenting write them, in a fixed order.
fn native_versions(node: &NodeRepo, op: &Operation) -> Result<Vec<Operation>, String> {
    let files = fs::read_dir(node.repo_path().join("op_store/operations"))
        .map_err(|error| error.to_string())?;
    let mut versions = vec![];
    for file in files {
        let file = file.map_err(|error| error.to_string())?;
        let Some(id) = file
            .file_name()
            .to_str()
            .and_then(OperationId::try_from_hex)
        else {
            continue;
        };
        if id == *op.id() {
            continue;
        }
        let other =
            block_on(node.loader().load_operation(&id)).map_err(|error| error.to_string())?;
        if same_but_parents(op, &other) {
            versions.push(other);
        }
    }
    versions.sort_by(|a, b| a.id().cmp(b.id()));
    Ok(versions)
}

/// Whether `a` and `b` are the same operation but for their parents.
fn same_but_parents(a: &Operation, b: &Operation) -> bool {
    let mut body = b.store_operation().clone();
    body.parents.clone_from(&a.store_operation().parents);
    body == *a.store_operation()
}
