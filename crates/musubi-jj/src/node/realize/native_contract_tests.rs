//! Native inputs and effect prefixes consumed by the first adapter-lifecycle increment.
//!
//! These tests close E1/E2 and the recovery interval by running one actor at a time. The
//! one scheduled command completes before publication locks. They make no general native
//! writer-lock claim, and an ambiguous physical source is not a runtime refusal.

#![allow(clippy::unwrap_used)]

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::SystemTime;

use async_trait::async_trait;
use jj_lib::object_id::{HexPrefix, ObjectId as _, PrefixResolution};
use jj_lib::op_heads_store::{OpHeadsStore, OpHeadsStoreError, OpHeadsStoreLock};
use jj_lib::op_store::{
    OpStore, OpStoreResult, Operation as RawOperation, OperationId, View, ViewId,
};
use jj_lib::ref_name::WorkspaceName;
use jj_lib::repo::RepoLoader;
use musubi_testutil::{TestEnv, TestRepo};
use pollster::FutureExt as _;
use serde_json::Value;

use super::super::native_contract::{Event, Observe};
use super::super::{CANONICAL_ATTRIBUTE, NodeRepo};
use super::PerMachine;
use crate::canonical::Contraction;
use crate::op_id::{CanonicalOp, LocalOp};
use crate::records::{HubOp, Record, RecordPrefix};

fn open(repo: &TestRepo) -> NodeRepo {
    NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap()
}

fn head(node: &mut NodeRepo) -> CanonicalOp {
    let heads = node.canonical_heads().unwrap();
    assert_eq!(heads.len(), 1);
    heads[0].clone()
}

fn transfer(from: &NodeRepo, to: &mut NodeRepo, head: &CanonicalOp) {
    let dir = musubi_testutil::tempdir();
    let ops = from
        .canonical
        .ancestors_until(std::slice::from_ref(head), |_| false)
        .unwrap();
    let bundle = dir.path().join("operations");
    from.canonical.export_operations(&ops, &bundle).unwrap();
    to.canonical.import_operations(&bundle).unwrap();
    let commits: Vec<_> = from.required_commits(&ops).unwrap().into_iter().collect();
    let objects = dir.path().join("objects");
    from.object_store()
        .unwrap()
        .export(&commits, &[], &objects)
        .unwrap();
    to.object_store()
        .unwrap()
        .import(&objects, &commits, &[])
        .unwrap();
    to.reload().unwrap();
}

struct Fixture {
    _env: TestEnv,
    repo: TestRepo,
    node: NodeRepo,
    incoming: CanonicalOp,
    child: CanonicalOp,
    records: Vec<Record>,
}

impl Fixture {
    fn new() -> Self {
        let binary = std::env::current_exe().unwrap();
        let saved = std::env::var_os("MUSUBI_NATIVE_CONTRACT_FIXTURE")
            .map(PathBuf::from)
            .unwrap_or_else(|| musubi_testutil::recorded(binary.parent().unwrap(), "native-contract", |path| {
                let mut fixture = Self::record();
                fixture.node.settle().unwrap();
                fixture._env.save(path);
                let state = serde_json::json!({
                    "incoming": fixture.incoming.0.hex(),
                    "child": fixture.child.0.hex(),
                    "drops": fixture.records[0].ops().iter().map(|op| op.0.0.hex()).collect::<Vec<_>>()
                });
                fs::write(path.join("native.json"), serde_json::to_vec(&state).unwrap()).unwrap();
            }));
        let state: Value =
            serde_json::from_slice(&fs::read(saved.join("native.json")).unwrap()).unwrap();
        let operation = |value: &Value| {
            CanonicalOp(OperationId::try_from_hex(value.as_str().unwrap()).unwrap())
        };
        let env = TestEnv::restore(&saved);
        let repo = env.repo_handle("beta");
        let node = open(&repo);
        Self {
            _env: env,
            repo,
            node,
            incoming: operation(&state["incoming"]),
            child: operation(&state["child"]),
            records: vec![Record::new(
                state["drops"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|value| HubOp(operation(value))),
            )],
        }
    }

    fn record() -> Self {
        let env = TestEnv::new();
        let a = env.init_repo_with_workspace("alpha", "a");
        let b = env.init_repo_with_workspace("beta", "a");
        b.jj(&[
            "workspace",
            "add",
            "--name",
            "b",
            env.root().join("second").to_str().unwrap(),
        ]);
        b.jj(&["new", "-m", "private Git basis"]);
        b.jj(&["bookmark", "create", "x", "-r", "@"]);
        let mut source = open(&a);
        let mut node = open(&b);
        let initial = head(&mut source);
        transfer(&source, &mut node, &initial);
        node.advance(&initial).unwrap();
        let joined = head(&mut node);
        transfer(&node, &mut source, &joined);
        source.advance(&joined).unwrap();
        source.forget_copy(node.machine().key(), "beta").unwrap();
        a.jj(&["new", "--no-edit", "-m", "surviving remote work"]);
        let tip = head(&mut source);
        a.jj(&["bookmark", "create", "child", "-r", "@"]);
        let child = head(&mut source);
        let drops: Vec<_> = source
            .canonical
            .ancestors_until(std::slice::from_ref(&tip), |_| false)
            .unwrap()
            .into_iter()
            .filter(|id| *id != tip)
            .collect();
        let mut contraction = Contraction::new(&source.canonical, drops.clone()).unwrap();
        let incoming = contraction
            .images(&source.canonical, &tip)
            .unwrap()
            .pop()
            .unwrap();
        assert_eq!(
            source.canonical.parents(&incoming).unwrap(),
            [source.canonical.root_operation_id().clone()]
        );
        let child = contraction
            .images(&source.canonical, &child)
            .unwrap()
            .pop()
            .unwrap();
        // A receipt names original drops as well as contracted images. Ship that readable
        // record evidence too; a pruned prefix/digest cannot replace the bodies.
        transfer(&source, &mut node, &tip);
        transfer(&source, &mut node, &child);
        let presence = node.presence(&incoming).unwrap();
        assert!(presence.known().contains(node.machine().key()));
        assert!(!presence.is_present(node.machine().key()));
        Self {
            _env: env,
            repo: b,
            node,
            incoming,
            child,
            records: vec![Record::new(drops.into_iter().map(HubOp))],
        }
    }

    fn prepare(&mut self) {
        self.node.realize(&self.incoming).unwrap();
        self.node.settle().unwrap();
        self.node
            .prepare_records(&RecordPrefix::none(), &self.records)
            .unwrap();
    }
}

fn raw(node: &NodeRepo, id: &LocalOp) -> (RawOperation, View) {
    let store = node.loader.op_store();
    let op = store.read_operation(&id.0).block_on().unwrap();
    let view = store.read_view(&op.view_id).block_on().unwrap();
    if std::env::var_os("MUSUBI_NATIVE_CONTRACT_TRACE").is_some() {
        eprintln!("native input {id:?}: {op:?} {view:?}");
    }
    (op, view)
}

fn records(path: &std::path::Path) -> Value {
    fs::read(path.join("musubi/records.json"))
        .ok()
        .map_or(Value::Null, |bytes| serde_json::from_slice(&bytes).unwrap())
}

struct Stores {
    ops: Arc<dyn OpStore>,
    heads: Arc<dyn OpHeadsStore>,
    path: PathBuf,
    effects: Arc<Mutex<Vec<Event>>>,
    observer: Option<super::super::native_contract::Observer>,
}

impl std::fmt::Debug for Stores {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Stores")
            .field("path", &self.path)
            .finish_non_exhaustive()
    }
}

impl Stores {
    fn record(&self, event: Event) {
        super::super::native_contract::trace(&event);
        self.effects.lock().unwrap().push(event.clone());
        if let Some(observer) = &self.observer {
            observer(event);
        }
    }
}

#[async_trait]
impl OpStore for Stores {
    fn name(&self) -> &str {
        self.ops.name()
    }
    fn root_operation_id(&self) -> &OperationId {
        self.ops.root_operation_id()
    }
    async fn read_view(&self, id: &ViewId) -> OpStoreResult<View> {
        self.ops.read_view(id).await
    }
    async fn write_view(&self, view: &View) -> OpStoreResult<ViewId> {
        self.ops.write_view(view).await
    }
    async fn read_operation(&self, id: &OperationId) -> OpStoreResult<RawOperation> {
        self.ops.read_operation(id).await
    }
    async fn write_operation(&self, op: &RawOperation) -> OpStoreResult<OperationId> {
        let snapshot = records(&self.path);
        let id = self.ops.write_operation(op).await?;
        self.record(Event::Write {
            op: op.clone(),
            records: snapshot,
        });
        Ok(id)
    }
    async fn resolve_operation_id_prefix(
        &self,
        prefix: &HexPrefix,
    ) -> OpStoreResult<PrefixResolution<OperationId>> {
        self.ops.resolve_operation_id_prefix(prefix).await
    }
    async fn gc(&self, heads: &[OperationId], newer: SystemTime) -> OpStoreResult<()> {
        self.ops.gc(heads, newer).await
    }
}

#[async_trait]
impl OpHeadsStore for Stores {
    fn name(&self) -> &str {
        self.heads.name()
    }
    async fn get_op_heads(&self) -> Result<Vec<OperationId>, OpHeadsStoreError> {
        self.heads.get_op_heads().await
    }
    async fn lock(&self) -> Result<Box<dyn OpHeadsStoreLock + '_>, OpHeadsStoreError> {
        self.heads.lock().await
    }
    async fn update_op_heads(
        &self,
        old: &[OperationId],
        new: &OperationId,
    ) -> Result<(), OpHeadsStoreError> {
        let before = self.heads.get_op_heads().await?;
        let snapshot = records(&self.path);
        self.heads.update_op_heads(old, new).await?;
        let after = self.heads.get_op_heads().await?;
        self.record(Event::Heads {
            old: old.to_vec(),
            new: new.clone(),
            before,
            after,
            records: snapshot,
        });
        Ok(())
    }
}

fn record_stores(node: &mut NodeRepo) -> Arc<Mutex<Vec<Event>>> {
    let effects = Arc::new(Mutex::new(vec![]));
    let loader = &node.loader;
    let stores = Arc::new(Stores {
        ops: loader.op_store().clone(),
        heads: loader.op_heads_store().clone(),
        path: node.repo_path.clone(),
        effects: effects.clone(),
        observer: super::super::native_contract::observer(),
    });
    node.loader = RepoLoader::new(
        loader.settings().clone(),
        loader.store().clone(),
        loader.workspace_store().clone(),
        stores.clone(),
        stores,
        loader.index_store().clone(),
        loader.submodule_store().clone(),
    );
    effects
}

#[test]
fn second_owned_name_survives_complete_native_capture() {
    let mut fx = Fixture::new();
    let before = fx.node.local_heads().unwrap();
    let current = fx.node.own_at_heads(&before).unwrap();
    assert_eq!(
        current.keys().map(|name| name.as_str()).collect::<Vec<_>>(),
        ["a", "b"]
    );
    // Capture a real native source with only the second name. It is a binding observation,
    // not a supplied ownership/overlap answer for the future model.
    fx.repo.jj(&["workspace", "forget", "a"]);
    let target = fx.node.local_heads().unwrap();
    assert_eq!(target.len(), 1);
    let canonical = fx.node.canonicalize(&target[0]).unwrap();
    let (op, view) = raw(&fx.node, &target[0]);
    assert!(!view.wc_commit_ids.contains_key(WorkspaceName::new("a")));
    assert!(view.wc_commit_ids.contains_key(WorkspaceName::new("b")));
    let own = fx
        .node
        .own_of_view(view.wc_commit_ids, &canonical, &op)
        .unwrap();
    assert_eq!(
        own.keys().map(|name| name.as_str()).collect::<Vec<_>>(),
        ["b"]
    );
    assert_eq!(
        own.get(WorkspaceName::new("b")),
        current.get(WorkspaceName::new("b"))
    );
    assert_eq!(fx.node.own_at_heads(&target).unwrap(), own);
    fx.repo
        .jj(&["--ignore-working-copy", "workspace", "forget", "b"]);
    let empty = fx.node.local_heads().unwrap();
    assert!(
        fx.node.own_at_heads(&empty).unwrap().is_empty(),
        "observed empty is deletion, not missing evidence"
    );
}

#[test]
fn foreign_spelling_is_not_owned_overlap() {
    let mut fx = Fixture::new();
    let heads = fx.node.local_heads().unwrap();
    let canonical = fx.node.canonicalize(&heads[0]).unwrap();
    let (op, view) = raw(&fx.node, &heads[0]);
    let actual = view.wc_commit_ids.clone();
    assert!(actual.keys().any(|name| name.as_str().contains('/')));
    let own = fx
        .node
        .own_of_view(actual.clone(), &canonical, &op)
        .unwrap();
    assert_eq!(
        own.keys().map(|name| name.as_str()).collect::<Vec<_>>(),
        ["a", "b"]
    );
    assert!(actual.len() > own.len());
    // The complete native map, including foreign slots, remains available to the consumer.
    assert_eq!(raw(&fx.node, &heads[0]).1.wc_commit_ids, actual);
}

#[test]
fn native_command_before_validation_forces_refresh() {
    let mut fx = Fixture::new();
    fx.prepare();
    let command = fx.repo.another_copy(fx.repo.path());
    let ran = Arc::new(AtomicBool::new(false));
    let events = Arc::new(Mutex::new(vec![]));
    let seen = events.clone();
    let fired = ran.clone();
    let _observe = Observe::new(move |event| {
        if matches!(event, Event::Prepared) && !fired.swap(true, Ordering::SeqCst) {
            command.jj(&["new", "-m", "late native command"]);
            command.jj(&["bookmark", "set", "x", "-r", "@"]);
        }
        seen.lock().unwrap().push(event);
    });
    fx.node.advance(&fx.incoming).unwrap();
    assert!(ran.load(Ordering::SeqCst));
    let events = events.lock().unwrap();
    let reads: Vec<_> = events
        .iter()
        .filter_map(|event| match event {
            Event::Reread { captured, actual } => Some((captured, actual)),
            _ => None,
        })
        .collect();
    assert!(
        reads.iter().any(|(captured, actual)| captured != actual),
        "the command must invalidate captured H"
    );
    assert_eq!(reads.last().unwrap().0, reads.last().unwrap().1);
    assert!(
        events
            .iter()
            .filter(|event| matches!(event, Event::Captured(_)))
            .count()
            >= 2
    );
    let last_read = events
        .iter()
        .rposition(|event| matches!(event, Event::Reread { .. }))
        .unwrap();
    assert!(
        events[last_read + 1..]
            .iter()
            .any(|event| matches!(event, Event::Export(_)))
    );
    assert!(matches!(events.last(), Some(Event::Complete)));
    for event in events.iter() {
        match event {
            Event::Captured(heads) | Event::Sources(heads) => assert!(!heads.is_empty()),
            Event::Exported(id) | Event::Loaded(id) => {
                assert!(!id.0.as_bytes().is_empty());
            }
            Event::HelperBranch { locked, heads } => assert_eq!(*locked, heads.len() > 1),
            _ => {}
        }
    }
    let git_lock = events
        .iter()
        .position(|event| matches!(event, Event::GitLocked))
        .unwrap();
    let heads_lock = events
        .iter()
        .position(|event| matches!(event, Event::HeadsLocked))
        .unwrap();
    assert!(git_lock < heads_lock);
    assert!(events.iter().any(|event| matches!(event, Event::Cleanup)));
}

#[test]
fn current_git_merge_precedes_first_export() {
    let mut fx = Fixture::new();
    fx.prepare();
    fx.repo
        .jj(&["new", "-m", "new local head after preparation"]);
    fx.repo.jj(&["bookmark", "set", "x", "-r", "@"]);
    let physical = fx.repo.git(&["rev-parse", "refs/heads/x"]);
    let path = fx.repo.repo_path();
    let loader = fx.node.loader.clone();
    let inputs = Arc::new(Mutex::new(vec![]));
    let seen = inputs.clone();
    let timeline = Arc::new(Mutex::new(vec![]));
    let trace = timeline.clone();
    let _observe = Observe::new(move |event| {
        trace.lock().unwrap().push(event.clone());
        if let Event::Export(id) = event {
            let op = loader.op_store().read_operation(&id.0).block_on().unwrap();
            let view = loader.op_store().read_view(&op.view_id).block_on().unwrap();
            seen.lock()
                .unwrap()
                .push((op.parents, view, records(&path)));
        }
    });
    let _effects = record_stores(&mut fx.node);
    fx.node.advance(&fx.incoming).unwrap();
    let timeline = timeline.lock().unwrap();
    let first = |predicate: fn(&Event) -> bool| timeline.iter().position(predicate).unwrap();
    assert!(
        first(|event| matches!(event, Event::Exported(_)))
            < first(|event| matches!(event, Event::Heads { .. }))
    );
    assert!(
        first(|event| matches!(event, Event::HeadsUnlocked))
            < first(|event| matches!(event, Event::Cleanup))
    );
    assert!(
        first(|event| matches!(event, Event::GitUnlocked))
            < first(|event| matches!(event, Event::Cleanup))
    );
    let inputs = inputs.lock().unwrap();
    let (parents, view, _) = inputs
        .first()
        .expect("the actual export boundary must be reached");
    assert!(
        parents.len() > 1,
        "the first export is a shared merge, not the incoming tip"
    );
    assert_eq!(
        view.local_bookmarks[jj_lib::ref_name::RefName::new("x")]
            .as_normal()
            .unwrap()
            .hex(),
        physical.trim()
    );
    assert_eq!(fx.repo.git(&["rev-parse", "refs/heads/x"]), physical);
}

#[test]
fn custody_is_saved_before_named_write() {
    let mut fx = Fixture::new();
    fx.repo
        .jj(&["describe", "-m", "unpublished native survivor"]);
    head(&mut fx.node);
    let prefix = RecordPrefix::none();
    assert!(fx.records.iter().any(|record| record.ops().len() > 1));
    // Expected responsibility comes from the incoming receipt before the call, including
    // every dropped original and its exact preceding digest in the receipt chain.
    let mut before = prefix.digest.clone();
    let expected: Vec<_> = fx
        .records
        .iter()
        .map(|record| {
            let entry = (
                jj_lib::hex_util::encode_hex(before.bytes()),
                record
                    .ops()
                    .iter()
                    .map(|op| op.0.0.hex())
                    .collect::<Vec<_>>(),
            );
            before = before.then(record);
            entry
        })
        .collect();
    let expected = serde_json::to_value(expected).unwrap();
    let effects = record_stores(&mut fx.node);
    fx.node.prepare_records(&prefix, &fx.records).unwrap();
    fx.node.settle().unwrap();
    let effects = effects.lock().unwrap();
    let writes: Vec<_> = effects
        .iter()
        .filter_map(|effect| match effect {
            Event::Write { op, records } => Some((op, records)),
            _ => None,
        })
        .collect();
    assert!(
        !writes.is_empty(),
        "preparation must really write renamed native bodies"
    );
    for (op, saved) in writes {
        assert!(!op.parents.is_empty());
        assert_eq!(
            saved["custody"], expected,
            "the exact incoming responsibility must already be on disk at the native write"
        );
    }
}

#[test]
fn move_intent_precedes_old_head_removal() {
    let mut fx = Fixture::new();
    fx.prepare();
    let effects = record_stores(&mut fx.node);
    fx.node.crash_publishing_taken_heads();
    assert!(fx.node.advance(&fx.incoming).is_err());
    let saved = records(&fx.repo.repo_path());
    assert!(saved["realign"].is_object());
    let heads: BTreeSet<_> = fx
        .node
        .local_heads()
        .unwrap()
        .into_iter()
        .map(|id| id.0)
        .collect();
    let effects = effects.lock().unwrap();
    let updates: Vec<_> = effects
        .iter()
        .filter_map(|effect| match effect {
            Event::Heads {
                old,
                new,
                before,
                after,
                records,
            } => Some((old, new, before, after, records)),
            _ => None,
        })
        .collect();
    assert!(!updates.is_empty());
    for (old, new, before, after, saved) in updates {
        assert!(
            old.is_empty(),
            "the declared interruption is before removal"
        );
        assert!(
            saved["realign"].is_object(),
            "realign intent is already persistent at head addition"
        );
        assert!(before.iter().all(|id| after.contains(id)));
        assert!(after.contains(new));
        assert!(after.iter().all(|id| heads.contains(id)));
    }
    drop(effects);
    drop(fx.node);
    let mut resumed = open(&fx.repo);
    let recovered = resumed.canonical_heads().unwrap();
    assert!(!recovered.is_empty());
    assert_eq!(resumed.applied_records(), fx.records);
    assert!(records(&fx.repo.repo_path())["realign"].is_null());
}

/// Enumerate physical inputs from native bodies, without consulting the preferred map.
/// The role arguments here test the renderer's priority. Qualification of an arbitrary
/// receipt's entire prepared map remains a separate receive-path obligation.
fn aliases(fx: &mut Fixture) -> (LocalOp, LocalOp, LocalOp) {
    let first = fx.node.realize(&fx.incoming).unwrap();
    fx.node.settle().unwrap();
    let mut result = vec![first.clone()];
    for name in ["export-one", "export-two"] {
        fx.repo.jj(&["bookmark", "create", name, "-r", "@"]);
        let heads = fx.node.local_heads().unwrap();
        assert_eq!(heads.len(), 1);
        let (_, observed) = raw(&fx.node, &heads[0]);
        let local = fx
            .node
            .with_per_machine(&first, &PerMachine::of(&observed), &fx.incoming)
            .unwrap();
        result.push(local);
    }
    assert_eq!(result.iter().collect::<BTreeSet<_>>().len(), 3);
    let (template, mut shared) = raw(&fx.node, &first);
    PerMachine::default().apply_to(&mut shared);
    for local in &result {
        let (op, mut view) = raw(&fx.node, local);
        PerMachine::default().apply_to(&mut view);
        assert_eq!(view, shared);
        assert_eq!(op.metadata, template.metadata);
        assert_eq!(op.commit_predecessors, template.commit_predecessors);
        assert_eq!(
            op.metadata.attributes.get(CANONICAL_ATTRIBUTE),
            Some(&fx.incoming.0.hex())
        );
        assert_eq!(op.parents, raw(&fx.node, &first).0.parents);
    }
    (result[0].clone(), result[1].clone(), result[2].clone())
}

#[test]
fn receipt_parent_precedes_preferred_alias() {
    let mut fx = Fixture::new();
    fx.node.realize(&fx.child).unwrap();
    fx.node.settle().unwrap();
    let (prepared, published, preferred) = aliases(&mut fx);
    let roles = BTreeMap::from([
        ("prepared", BTreeSet::from([prepared.clone()])),
        ("published", BTreeSet::from([published.clone()])),
        ("local", BTreeSet::from([preferred.clone()])),
    ]);
    assert!(roles.values().all(|candidates| candidates.len() == 1));
    assert_eq!(roles.values().flatten().collect::<BTreeSet<_>>().len(), 3);
    fx.node.insert_map(preferred, fx.incoming.clone()).unwrap();
    let published = HashMap::from([(fx.incoming.clone(), published)]);
    let prepared_map = HashMap::from([(fx.incoming.clone(), prepared.clone())]);
    let own = fx
        .node
        .own_at_heads(&fx.node.local_heads().unwrap())
        .unwrap();
    let child = fx
        .node
        .current_realizations(
            std::slice::from_ref(&fx.child),
            &published,
            &prepared_map,
            &own,
        )
        .unwrap();
    let (actual, _) = raw(&fx.node, &child[0]);
    assert_eq!(actual.parents, [prepared.0]);
    // Keeping all candidates is essential: a single preferred alias would hide this state.
    assert_eq!(roles.values().flatten().collect::<BTreeSet<_>>().len(), 3);
}

#[test]
fn changed_physical_parent_refreshes_git_fields() {
    let mut fx = Fixture::new();
    let cached_child = fx.node.realize(&fx.child).unwrap();
    fx.node.settle().unwrap();
    let cached = raw(&fx.node, &cached_child);
    let (_, parent, preferred) = aliases(&mut fx);
    let (_, observed) = raw(&fx.node, &parent);
    assert_ne!(
        PerMachine::of(&cached.1),
        PerMachine::of(&observed),
        "I differs: this is a refresh case, not exact cache-loss agreement"
    );
    fx.node.insert_map(preferred, fx.incoming.clone()).unwrap();
    let published = HashMap::from([(fx.incoming.clone(), parent.clone())]);
    let own = fx
        .node
        .own_at_heads(&fx.node.local_heads().unwrap())
        .unwrap();
    let result = fx
        .node
        .current_realizations(
            std::slice::from_ref(&fx.child),
            &published,
            &HashMap::new(),
            &own,
        )
        .unwrap();
    let (actual, view) = raw(&fx.node, &result[0]);
    assert_ne!(result[0], cached_child);
    assert_eq!(actual.parents, [parent.0]);
    assert_eq!(PerMachine::of(&view), PerMachine::of(&observed));
}

/// Complete raw inputs, including operations not selected by a preferred translation.
/// Marker labels are observations, not independently validated source certificates. Keep
/// unmarked bodies too: a consumer must qualify them before asserting the U restriction.
#[derive(Debug)]
struct Inputs {
    heads: Vec<LocalOp>,
    native: BTreeMap<LocalOp, (RawOperation, View)>,
    canonical: BTreeMap<CanonicalOp, (RawOperation, View)>,
    receipt: Option<super::super::native_contract::Receipt>,
    expected: super::super::git::Expected,
    evidence: BTreeMap<PathBuf, Vec<u8>>,
}

fn capture(node: &NodeRepo) -> Inputs {
    let mut heads = node.local_heads().unwrap();
    heads.sort();
    let native = fs::read_dir(node.repo_path.join("op_store/operations"))
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .filter_map(|name| OperationId::try_from_hex(&name))
        .map(LocalOp)
        .chain([node.root_op_id().clone()])
        .map(|id| {
            let body = raw(node, &id);
            (id, body)
        })
        .collect();
    let canonical = node
        .canonical
        .operation_ids()
        .unwrap()
        .into_iter()
        .chain([node.canonical.root_operation_id().clone()])
        .map(|id| {
            let op = node.canonical.read_operation(&id).unwrap();
            let view = node.canonical.read_view(&op.view_id).unwrap();
            (id, (op, view))
        })
        .collect();
    Inputs {
        heads,
        native,
        canonical,
        receipt: node.native_receipt(),
        expected: node.colocation().unwrap().native_expected(),
        evidence: bytes(&node.repo_path.join("musubi")),
    }
}

fn bytes(path: &std::path::Path) -> BTreeMap<PathBuf, Vec<u8>> {
    fn visit(
        root: &std::path::Path,
        path: &std::path::Path,
        result: &mut BTreeMap<PathBuf, Vec<u8>>,
    ) {
        for entry in fs::read_dir(path).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            if entry.file_type().unwrap().is_dir() {
                visit(root, &path, result);
            } else if entry.file_type().unwrap().is_symlink() {
                result.insert(
                    path.strip_prefix(root).unwrap().to_owned(),
                    fs::read_link(&path)
                        .unwrap()
                        .as_os_str()
                        .as_encoded_bytes()
                        .to_vec(),
                );
            } else {
                result.insert(
                    path.strip_prefix(root).unwrap().to_owned(),
                    fs::read(&path).unwrap(),
                );
            }
        }
    }
    let mut result = BTreeMap::new();
    visit(path, path, &mut result);
    result
}

#[test]
fn complete_receipt_and_body_observation_is_pure() {
    let mut observed = Fixture::new();
    let mut control = Fixture::new();
    observed.prepare();
    control.prepare();
    let before = bytes(observed.repo.path());
    let clock = observed._env.clock().now();
    let first = capture(&observed.node);
    let second = capture(&observed.node);
    assert_eq!(first.heads, second.heads);
    assert_eq!(first.native, second.native);
    assert_eq!(first.canonical, second.canonical);
    assert_eq!(first.receipt, second.receipt);
    assert_eq!(first.expected, second.expected);
    assert_eq!(first.evidence, second.evidence);
    let receipt = first.receipt.as_ref().unwrap();
    assert_eq!(receipt.heads, first.heads);
    assert_eq!(receipt.prefix, RecordPrefix::none());
    assert_eq!(receipt.records, observed.records);
    assert!(!receipt.switched);
    // All receipt edges and every readable physical parent remain in the input; none
    // can be removed just because another alias has the same canonical marker.
    for (old, images) in &receipt.locals {
        assert!(first.native.contains_key(old));
        assert!(images.iter().all(|id| first.native.contains_key(id)));
    }
    for (op, _) in first.native.values() {
        assert!(
            op.parents
                .iter()
                .all(|id| first.native.contains_key(&LocalOp(id.clone())))
        );
    }
    assert_eq!(
        bytes(observed.repo.path()),
        before,
        "observation cannot change native/canonical/original/record/Git bytes or mint an identity"
    );
    assert_eq!(
        observed._env.clock().now(),
        clock,
        "observation cannot take an actor seed"
    );
    // Freshly restored actors have identical seeded histories. Comparing their next RNG
    // draw checks the actual actor generator, not an observer's separate seed counter.
    assert_eq!(
        observed.node.loader.settings().get_rng().new_change_id(16),
        control.node.loader.settings().get_rng().new_change_id(16)
    );
}

/// Role domains are sets of physical bodies. They do not authenticate a marker, choose an
/// alias, or decide ownership. Complete bodies/source rows stay alongside these domains.
fn role_domains(
    inputs: &Inputs,
) -> (
    BTreeSet<LocalOp>,
    Option<BTreeSet<LocalOp>>,
    BTreeSet<LocalOp>,
) {
    let mut published = BTreeSet::new();
    let mut pending = inputs.heads.clone();
    while let Some(id) = pending.pop() {
        if published.insert(id.clone()) {
            pending.extend(inputs.native[&id].0.parents.iter().cloned().map(LocalOp));
        }
    }
    let prepared = inputs
        .receipt
        .as_ref()
        .filter(|receipt| !receipt.switched && receipt.heads == inputs.heads)
        .map(|receipt| receipt.locals.values().flatten().cloned().collect());
    (published, prepared, inputs.native.keys().cloned().collect())
}

#[test]
fn complete_candidates_keep_ambiguous_published_aliases() {
    let mut fx = Fixture::new();
    fx.prepare();
    let before = capture(&fx.node);
    let (_, prepared, _) = role_domains(&before);
    let receipt = before.receipt.as_ref().unwrap();
    assert_eq!(
        prepared.unwrap(),
        receipt.locals.values().flatten().cloned().collect()
    );
    let (p, q, r) = aliases(&mut fx);
    // Recreate an interrupted add-before-remove frontier with real immutable shipping
    // bodies. This is an actor action, never an effect of observation or normalization.
    for id in [&p, &q] {
        fx.node
            .loader
            .op_heads_store()
            .update_op_heads(&[], &id.0)
            .block_on()
            .unwrap();
    }
    let inputs = capture(&fx.node);
    let (published, prepared, local) = role_domains(&inputs);
    assert!(
        prepared.is_none(),
        "changed H invalidates the old receipt role"
    );
    assert!(local.contains(&r));
    let declared: BTreeSet<_> = published
        .iter()
        .filter(|id| {
            inputs.native[*id]
                .0
                .metadata
                .attributes
                .get(CANONICAL_ATTRIBUTE)
                == Some(&fx.incoming.0.hex())
        })
        .cloned()
        .collect();
    assert_eq!(declared, BTreeSet::from([p.clone(), q.clone()]));
    assert_ne!(
        PerMachine::of(&inputs.native[&p].1),
        PerMachine::of(&inputs.native[&q].1),
        "same canonical label does not imply retained-input I"
    );
    // Unmarked source bodies are not silently omitted or reclassified by a preferred map.
    assert!(published.iter().any(|id| {
        !inputs.native[id]
            .0
            .metadata
            .attributes
            .contains_key(CANONICAL_ATTRIBUTE)
    }));
    assert!(
        inputs
            .receipt
            .as_ref()
            .unwrap()
            .sources
            .keys()
            .all(|id| inputs.native.contains_key(id))
    );
}

#[test]
fn second_owned_name_selects_current_git() {
    let mut fx = Fixture::new();
    fx.repo.jj(&["workspace", "forget", "b"]);
    fx.repo.jj(&["workspace", "rename", "b"]);
    // Publish the forgotten parent while b is the only actual owned slot. The child
    // subsequently inherits that published source, rather than the current root inputs.
    fx.node.advance(&fx.incoming).unwrap();
    let child = fx.node.realize(&fx.child).unwrap();
    fx.node.settle().unwrap();
    let (op, view) = raw(&fx.node, &child);
    let target = fx
        .node
        .own_of_view(view.wc_commit_ids, &fx.child, &op)
        .unwrap();
    assert_eq!(
        target.keys().map(|name| name.as_str()).collect::<Vec<_>>(),
        ["b"]
    );
    let path = fx._env.root().join("new-a");
    fx.repo.jj(&[
        "workspace",
        "add",
        "--name",
        "a",
        "-r",
        "b@",
        path.to_str().unwrap(),
    ]);
    fx.repo
        .jj(&["--ignore-working-copy", "bookmark", "set", "x", "-r", "a@"]);
    fx.repo.jj(&["--ignore-working-copy", "git", "export"]);
    let heads = fx.node.local_heads().unwrap();
    let current = fx.node.own_at_heads(&heads).unwrap();
    assert_eq!(
        current.keys().map(|name| name.as_str()).collect::<Vec<_>>(),
        ["a", "b"]
    );
    assert!(
        fx.node.native_receipt().is_none(),
        "this exercises non-root-base private selection"
    );
    let (_, current_view) = raw(&fx.node, &heads[0]);
    let expected = PerMachine::of(&current_view);
    assert_ne!(
        expected,
        PerMachine::of(&raw(&fx.node, &child).1),
        "the current Git observation must differ from the cached child's"
    );
    let physical = gix::open(fx.repo.path())
        .unwrap()
        .find_reference("refs/heads/x")
        .unwrap()
        .target()
        .try_id()
        .unwrap()
        .to_string();
    let loader = fx.node.loader.clone();
    let exported = Arc::new(Mutex::new(vec![]));
    let seen = exported.clone();
    let _observe = Observe::new(move |event| {
        if let Event::Export(id) = event {
            let op = loader.op_store().read_operation(&id.0).block_on().unwrap();
            let view = loader.op_store().read_view(&op.view_id).block_on().unwrap();
            seen.lock().unwrap().push((op, view));
        }
    });
    let published = fx.node.advance(&fx.child).unwrap();
    let inputs = exported.lock().unwrap();
    let (first, _) = inputs.first().unwrap();
    assert!(
        first.parents.len() > 1,
        "overlap at b must merge before the first export"
    );
    assert_eq!(PerMachine::of(&raw(&fx.node, &published).1), expected);
    assert_eq!(
        gix::open(fx.repo.path())
            .unwrap()
            .find_reference("refs/heads/x")
            .unwrap()
            .target()
            .try_id()
            .unwrap()
            .to_string(),
        physical
    );
}
