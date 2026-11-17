//! A fetch beside a realization made while taking another machine's `jj op abandon`: the
//! fetches of `two` and `three` conflict `y@origin`, and musubi writes its side, `three`, to
//! both `.git`s. The other machine abandons the operation this machine's op head stands
//! for, so this machine realizes the hub's head, which keeps the conflict, before taking the
//! abandon (protocol.md, "Supersedes"). A `jj git fetch` of `two`, a term of the conflict,
//! publishes after the sync's step has checked the op heads and before the realization is
//! published, as only a command running concurrently can: the test makes the step's calls
//! itself, mapping the op heads before the realization as a node opened since does.
//!
//! It stays out of the `Realization` scenarios, which have the other machine run a native
//! command and then sync as a whole. Here the point is a step of the sync itself, run by hand,
//! and what it publishes on the canonical history: the abandon, which no `RefCommand` makes,
//! the renamed fetch, and the contraction of the dropped operation (`abandon_beside` and
//! `contraction` in the Lean model), none of which the state machine's model has.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use futures::executor::block_on;
use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::RefTarget;
use musubi_core::node::LocalRepo as _;
use musubi_core::node::Step;
use musubi_jj::node::NodeRepo;
use musubi_jj::op_id::CanonicalOp;
use musubi_jj::op_id::LocalOp;
use serde_json::json;

use super::HERE;
use super::Ref;
use super::THERE;
use super::hive;
use super::read;
use super::slot;
use crate::fixture::Fixture;
use crate::refs_model::RefsModel;
use crate::refs_model::Slot;

/// The hive with `origin` as both machines' remote, and the two commits `y` moves between.
struct Scene {
    f: Fixture,
    origin: String,
    two: String,
    three: String,
}

/// What the Lean model and an independent contraction of the dropped operation say the
/// realization must publish.
struct Prediction {
    parents: BTreeSet<CanonicalOp>,
    slot: Slot,
    graph: OriginalGraph,
}

impl Scene {
    fn new() -> Self {
        let f = hive();
        let origin = f.env.root().join("origin.git");
        let origin = origin.to_str().unwrap().to_owned();
        for index in [HERE, THERE] {
            f.repo(index).git(&["remote", "set-url", "origin", &origin]);
        }
        let [two, three] = ["two", "three"].map(|m| f.commit_id(HERE, m));
        Self {
            f,
            origin,
            two,
            three,
        }
    }

    /// `y` moves in `origin` to the commit `id`.
    fn upstream(&self, id: &str) {
        self.f
            .repo(HERE)
            .git(&["--git-dir", &self.origin, "update-ref", "refs/heads/y", id]);
    }

    /// What the other machine's `.git` has for `y@origin`.
    fn git_y(&self) -> String {
        let git = self
            .f
            .repo(THERE)
            .git(&["rev-parse", "refs/remotes/origin/y"]);
        git.trim().to_owned()
    }

    /// A `jj` command here that imports nothing, so that the conflict stays.
    fn jj_here(&self, args: &[&str]) {
        self.f
            .repo(HERE)
            .jj(&[&["--ignore-working-copy"], args].concat());
    }

    /// The descriptions of machine `index`'s operations.
    fn op_log(&self, index: usize) -> String {
        let template = "description ++ \"\\n\"";
        self.f.repo(index).jj(&[
            "--ignore-working-copy",
            "op",
            "log",
            "--no-graph",
            "-T",
            template,
        ])
    }

    /// Concurrent fetches of `two` and `three` conflict `y@origin`, and both machines sync.
    fn conflict_y_at_origin(&mut self) {
        self.upstream(&self.two);
        self.f.repo(HERE).jj(&["git", "fetch"]);
        self.upstream(&self.three);
        self.f.repo(THERE).jj(&["git", "fetch"]);
        self.f.hive.sync(HERE).unwrap();
        self.f.hive.sync(THERE).unwrap();
        self.f.hive.sync(HERE).unwrap();
        assert_eq!(self.git_y(), self.three, "musubi's side");
    }

    /// The other machine's operation `dropped`, which this machine takes with it, is
    /// abandoned by a later operation here. Returns the canonical operation dropped.
    fn abandon_an_operation(&mut self) -> CanonicalOp {
        self.jj_here(&["bookmark", "create", "dropped", "-r", "@"]);
        let dropped = self.f.load(HERE).op_id().hex();
        let dropped_canonical = self
            .f
            .node(HERE)
            .canonicalize(&LocalOp(OperationId::try_from_hex(&dropped).unwrap()))
            .unwrap();
        self.f.sync();
        self.jj_here(&["new", "-m", "kept"]);
        self.jj_here(&["op", "abandon", &dropped]);
        self.f.hive.sync(HERE).unwrap();
        let (head_slot, _) = read(&self.f.load(HERE), Ref::Origin);
        assert!(!head_slot.r.is_resolved(), "{head_slot:?}");
        dropped_canonical
    }

    /// A fix-up keeps the pre-abandon expectation explicitly, rather than inferring it
    /// from the shortened history. Its canonical shared view is its parent's.
    fn assert_a_fixup_keeps_the_expectation(&mut self) {
        let three = &self.three;
        let mut fixups = 0;
        let node = self.f.node(HERE);
        let heads = node.canonical_heads().unwrap();
        let history = node
            .canonical_store()
            .ancestors_until(&heads, |_| false)
            .unwrap();
        for op in history {
            let raw = node.canonical_store().read_operation(&op).unwrap();
            if let Some(expected) = raw.metadata.attributes.get("musubi.expected") {
                assert!(
                    expected
                        .lines()
                        .any(|line| line == format!("refs/remotes/origin/y {three}"))
                );
                let parent = node.canonical_store().parents(&op).unwrap();
                assert_eq!(parent.len(), 1);
                assert_eq!(
                    raw.view_id,
                    node.canonical_store()
                        .read_operation(&parent[0])
                        .unwrap()
                        .view_id
                );
                fixups += 1;
            }
        }
        assert!(
            fixups > 0,
            "the expected-value snapshot is carried across the drop"
        );
    }

    /// The sync's steps up to the realization, the first of which prepares to take the
    /// abandon. Nothing is published yet. Returns the hub head the realization is of.
    fn sync_up_to_the_realization(&mut self) -> OperationId {
        self.f.hive.fetch(THERE).unwrap();
        let unpublished_heads = self.f.node(THERE).local_heads().unwrap();
        let canonical_before = self.canonical_operations();
        let known = loop {
            let member = &mut self.f.hive.members[THERE];
            let known = member.core.known().head.clone();
            if member.adapter.is_local(&known).unwrap() {
                break known;
            }
            let step = member.core.step(&mut member.adapter).unwrap();
            assert!(matches!(step, Step::Realized(_)), "{step:?}");
        };
        assert_eq!(self.f.node(THERE).local_heads().unwrap(), unpublished_heads);
        assert_eq!(
            self.git_y(),
            self.three,
            "unpublished realization exports nothing"
        );
        assert_eq!(self.canonical_operations(), canonical_before);
        known
    }

    fn canonical_operations(&mut self) -> BTreeSet<CanonicalOp> {
        self.f
            .node(THERE)
            .canonical_store()
            .operation_ids()
            .unwrap()
            .into_iter()
            .collect()
    }

    /// The fetch of `two` that runs concurrently with the sync.
    fn fetch_two_beside(&mut self) {
        self.upstream(&self.two);
        self.f.repo(THERE).jj(&["git", "fetch"]);
    }

    /// What the realization of `known`, the hub's head, must publish, from the Lean model of
    /// the abandon and an independent contraction of `dropped`. Maps the op heads before the
    /// realization, as `realize` does on a node opened since the records were prepared, which
    /// gives the fetch a canonical form on the abandoned operation.
    fn predict_the_realization(
        &mut self,
        known: &OperationId,
        dropped: &CanonicalOp,
    ) -> Prediction {
        let (two, three) = (self.two.clone(), self.three.clone());
        let old_heads = self.f.node(THERE).canonical_heads().unwrap();
        let incoming = self
            .f
            .node(THERE)
            .to_node(&musubi_jj::records::HubOp(CanonicalOp(
                OperationId::try_from_hex(known.hex()).unwrap(),
            )))
            .unwrap()[0]
            .0
            .clone();
        // Independently contract the old heads, then take max(images(heads) ∪ {incoming}).
        // Using the old names as parents would revive the dropped operation.
        let node = self.f.node(THERE);
        let store = node.canonical_store();
        let mut contraction =
            musubi_jj::canonical::Contraction::new(store, [dropped.clone()]).unwrap();
        let mut candidates = vec![incoming.clone()];
        for head in &old_heads {
            candidates.extend(contraction.images(store, head).unwrap());
        }
        let expected_parents: BTreeSet<_> = candidates
            .iter()
            .filter(|a| {
                !candidates
                    .iter()
                    .any(|b| a != &b && store.is_ancestor_of(a, b).unwrap())
            })
            .cloned()
            .collect();
        assert_eq!(
            expected_parents.len(),
            2,
            "the renamed fetch and the incoming head"
        );

        let graph = OriginalGraph::observe(node, &old_heads, &incoming);
        let bases = store
            .closest_common_ancestors(
                std::slice::from_ref(&incoming),
                &expected_parents
                    .iter()
                    .filter(|op| **op != incoming)
                    .cloned()
                    .collect::<Vec<_>>(),
            )
            .unwrap();
        assert_eq!(bases.len(), 1);
        let at = |local: &LocalOp| {
            let op = block_on(node.loader().load_operation(&local.0)).unwrap();
            slot(block_on(op.view()).unwrap().store_view(), Ref::Origin)
        };
        let base_slot = at(&node.local_of(&bases[0]).unwrap());
        let local = node.local_heads().unwrap();
        assert_eq!(local.len(), 1);
        let local_slot = at(&local[0]);
        let incoming_local = node.local_of(&incoming).unwrap();
        assert_eq!(
            node.canonical_of(&incoming_local).unwrap(),
            incoming,
            "realize/canon inverse before publication"
        );
        let realized_slot = at(&incoming_local);
        let incoming_slot = slot(&store.read_operation_view(&incoming).unwrap(), Ref::Origin);
        assert_eq!(
            (&realized_slot.l, &realized_slot.r, realized_slot.tr),
            (&incoming_slot.l, &incoming_slot.r, incoming_slot.tr),
            "the realization preserves the canonical input's shared ref fields"
        );
        let time = |local: &LocalOp| {
            block_on(node.loader().op_store().read_operation(&local.0))
                .unwrap()
                .metadata
                .time
                .end
                .timestamp
        };
        let first = time(&incoming_local) <= time(&local[0]);
        let three_target = RefTarget::normal(CommitId::try_from_hex(&three).unwrap());
        let two_target = RefTarget::normal(CommitId::try_from_hex(&two).unwrap());
        let op = block_on(node.loader().load_operation(&local[0].0)).unwrap();
        let mut model = RefsModel::new(block_on(node.loader().load_at(&op)).unwrap());
        let (boundary, expected_slot, expected_git) = model.abandon_beside(
            &json!({"par": graph.parents, "drops": [graph.id(node, dropped)],
                "heads": old_heads.iter().map(|h| graph.id(node, h)).collect::<Vec<_>>(),
                "incoming": graph.id(node, &incoming), "base": graph.id(node, &bases[0]), "first": first}),
            &[
                (graph.id(node, &bases[0]), base_slot, three_target.clone()),
                (graph.id(node, &old_heads[0]), local_slot, two_target.clone()),
                (graph.id(node, &incoming), incoming_slot, three_target.clone()),
            ],
            [&two_target, &two_target],
        );
        assert_eq!(expected_git, two_target);
        assert_eq!(boundary["bases"], json!([graph.id(node, &bases[0])]));
        let expected_model_parents: BTreeSet<usize> =
            serde_json::from_value(boundary["parents"].clone()).unwrap();
        assert_eq!(
            expected_parents
                .iter()
                .map(|p| graph.id(node, p))
                .collect::<BTreeSet<_>>(),
            expected_model_parents
        );
        // The Lean contraction is checked against every actual survivor, not just final heads.
        for (i, op) in graph.operations.iter().enumerate() {
            if op == dropped {
                continue;
            }
            let image = contraction.images(store, op).unwrap();
            assert_eq!(image.len(), 1);
            let actual: Vec<_> = store
                .parents(&image[0])
                .unwrap()
                .iter()
                .map(|p| graph.id(node, p))
                .collect();
            assert_eq!(json!(actual), boundary["contracted"][i], "survivor {i}");
        }
        Prediction {
            parents: expected_parents,
            slot: expected_slot,
            graph,
        }
    }

    /// The realization is published: it merges the renamed fetch with the incoming head, as
    /// predicted, leaves the fetch in `.git`, and keeps the dropped operation out of history.
    fn publish_the_realization(
        &mut self,
        known: &OperationId,
        dropped: &CanonicalOp,
        prediction: &Prediction,
    ) {
        self.f.hive.members[THERE].adapter.advance(known).unwrap();
        // Observe the returned raw heads before any subsequent jj command merges them.
        let node = self.f.node(THERE);
        let heads = node.local_heads().unwrap();
        assert_eq!(heads.len(), 1);
        let merged = block_on(node.loader().op_store().read_operation(&heads[0].0)).unwrap();
        let parents: BTreeSet<_> = merged
            .parents
            .iter()
            .map(|p| node.canonicalize(&LocalOp(p.clone())).unwrap())
            .collect();
        assert_eq!(parents, prediction.parents);
        let canonical = node.canonicalize(&heads[0]).unwrap();
        assert!(
            !node
                .canonical_store()
                .is_ancestor_of(dropped, &canonical)
                .unwrap()
        );
        let published = block_on(node.loader().load_operation(&heads[0].0)).unwrap();
        assert_eq!(
            slot(
                block_on(published.view()).unwrap().store_view(),
                Ref::Origin
            ),
            prediction.slot
        );
        prediction
            .graph
            .check_translation(node, &heads[0], &canonical);
        assert_eq!(self.git_y(), self.two, "the fetch in .git");
        // The fetch was moved onto the renamed history before the merge, which otherwise would
        // have merged it on the dropped operation, against an older common ancestor.
        let log = self.op_log(THERE);
        assert!(!log.contains("create bookmark dropped"), "{log}");
    }

    /// A neutral publication tip inherits this current fetch/expectation, rather than
    /// replaying the fix-up's earlier `three` snapshot. Exercise the primitive on this
    /// observed parent before any jj command can import or reconcile the fetch. Returns the
    /// URL of `origin` there, for the restart to keep.
    fn write_a_neutral_tip(&mut self) -> String {
        let before = read(&self.f.load(THERE), Ref::Origin);
        let before_url = self.f.repo(THERE).git(&["remote", "get-url", "origin"]);
        let node = self.f.node(THERE);
        let parent = node.canonical_heads().unwrap().swap_remove(0);
        let before_presence = node.presence(&parent).unwrap();
        let before_view = node
            .canonical_store()
            .read_operation(&parent)
            .unwrap()
            .view_id;
        let tip = node
            .write_drop_tip(&musubi_jj::records::HubOp(parent.clone()))
            .unwrap()
            .unwrap();
        let raw = node.canonical_store().read_operation(&tip.0).unwrap();
        assert_eq!(raw.parents, [parent.0]);
        assert_eq!(raw.view_id, before_view);
        assert_eq!(node.presence(&tip.0).unwrap(), before_presence);
        assert!(raw.metadata.workspace_name.is_none());
        for key in [
            "musubi.work",
            "musubi.forget",
            "musubi.forget-after",
            "musubi.expected",
        ] {
            assert!(!raw.metadata.attributes.contains_key(key), "replayed {key}");
        }
        assert_eq!(read(&self.f.load(THERE), Ref::Origin), before);
        assert_eq!(self.git_y(), self.two);
        before_url
    }

    /// Both machines converge on the fetch, across a restart, with no trace of the dropped
    /// operation.
    fn converge_on_the_fetch(&mut self, before_url: &str) {
        self.f.repo(THERE).jj(&["status"]);
        self.f.sync();
        self.f.assert_converged();
        self.f.reopen(THERE);
        self.f.sync();
        assert_eq!(
            self.f.repo(THERE).git(&["remote", "get-url", "origin"]),
            before_url
        );
        let two = RefTarget::normal(CommitId::try_from_hex(&self.two).unwrap());
        for index in [HERE, THERE] {
            let (slot, git) = read(&self.f.load(index), Ref::Origin);
            assert_eq!((&slot.r, &git), (&two, &two), "y@origin on {index}");
            let log = self.op_log(index);
            assert!(!log.contains("create bookmark dropped"), "{log}");
        }
    }
}

/// musubi must leave `two` in `.git`, and publish the realization merged with the fetch, which
/// keeps it, the fetch renamed first: written for the realization alone, `three` would be in
/// `.git`, and the next command would import it as a move made with git.
#[test]
fn realization_beside_a_fetch_keeps_the_fetch_while_taking_an_abandon() {
    let mut scene = Scene::new();
    scene.conflict_y_at_origin();
    let dropped = scene.abandon_an_operation();
    scene.assert_a_fixup_keeps_the_expectation();
    let known = scene.sync_up_to_the_realization();
    scene.fetch_two_beside();
    let prediction = scene.predict_the_realization(&known, &dropped);
    scene.publish_the_realization(&known, &dropped, &prediction);
    let before_url = scene.write_a_neutral_tip();
    scene.converge_on_the_fetch(&before_url);
}

/// Project observed histories into original-operation names. Prefer the old local history
/// when an incoming contracted version has the same original: its old parents are precisely
/// the ghost ancestry the contraction model retains. Fresh fix-up operations are originals
/// too; realization must not allocate any. This does not infer identity from descriptions.
struct OriginalGraph {
    ids: BTreeMap<OperationId, usize>,
    operations: Vec<CanonicalOp>,
    parents: Vec<Vec<usize>>,
    stored: BTreeSet<CanonicalOp>,
}

impl OriginalGraph {
    fn observe(node: &NodeRepo, old: &[CanonicalOp], incoming: &CanonicalOp) -> Self {
        let mut graph = Self {
            ids: BTreeMap::new(),
            operations: vec![],
            parents: vec![],
            stored: node
                .canonical_store()
                .operation_ids()
                .unwrap()
                .into_iter()
                .collect(),
        };
        let root = node.canonical_store().root_operation_id();
        graph.add(node, root);
        for head in old.iter().chain([incoming]) {
            graph.add(node, head);
        }
        graph
    }

    fn add(&mut self, node: &NodeRepo, op: &CanonicalOp) -> usize {
        let store = node.canonical_store();
        let origin = store.original_id(op).unwrap();
        if let Some(&id) = self.ids.get(&origin) {
            return id;
        }
        let parents = store
            .parents(op)
            .unwrap()
            .iter()
            .map(|p| self.add(node, p))
            .collect();
        let id = self.operations.len();
        self.ids.insert(origin, id);
        self.operations.push(op.clone());
        self.parents.push(parents);
        id
    }

    fn id(&self, node: &NodeRepo, op: &CanonicalOp) -> usize {
        self.ids[&node.canonical_store().original_id(op).unwrap()]
    }

    /// Translation's inverse, parent preservation, reachable injectivity and no new IDs
    /// immediately after publication, before another command or full convergence.
    fn check_translation(&self, node: &mut NodeRepo, head: &LocalOp, merged: &CanonicalOp) {
        let mut stack = vec![head.clone()];
        let mut seen = BTreeSet::new();
        let mut forms = BTreeSet::new();
        while let Some(local) = stack.pop() {
            if !seen.insert(local.clone())
                || local.0 == *node.loader().op_store().root_operation_id()
            {
                continue;
            }
            let canonical = node.canonicalize(&local).unwrap();
            assert!(
                forms.insert(canonical.clone()),
                "two reachable realizations of {canonical:?}"
            );
            let raw = block_on(node.loader().op_store().read_operation(&local.0)).unwrap();
            let parents = node.canonical_store().parents(&canonical).unwrap();
            if parents == [node.canonical_store().root_operation_id().clone()] {
                continue; // The joining machine's earlier operations aren't hive history.
            }
            let locals: Vec<_> = raw.parents.into_iter().map(LocalOp).collect();
            let translated: Vec<_> = locals
                .iter()
                .map(|p| node.canonicalize(p).unwrap())
                .collect();
            assert_eq!(translated, parents);
            stack.extend(locals);
        }
        let after: BTreeSet<_> = node
            .canonical_store()
            .operation_ids()
            .unwrap()
            .into_iter()
            .collect();
        assert_eq!(after.difference(&self.stored).collect::<Vec<_>>(), [merged]);
    }
}
