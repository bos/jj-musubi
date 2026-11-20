//! Independent, isolated native primitive observations for C's first preparation.
//! Captured caller vectors are comparison data. Lean derives its own vector before matching
//! these complete graph/context-keyed native observations.

use super::*;
use jj_lib::config::StackedConfig;
use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::settings::UserSettings;

fn byte_manifest(path: &std::path::Path) -> Value {
    json!(
        bytes(path)
            .into_iter()
            .map(|(path, data)| (
                path.to_string_lossy().into_owned(),
                jj_lib::hex_util::encode_hex(&data)
            ))
            .collect::<BTreeMap<_, _>>()
    )
}

fn dump(index: usize, phase: &str, value: &Value) {
    if let Some(path) = std::env::var_os("MUSUBI_NATIVE_LIFECYCLE_DUMP") {
        let path = std::path::Path::new(&path);
        fs::create_dir_all(path).unwrap();
        fs::write(
            path.join(format!("probe-{index}-{phase}.json")),
            serde_json::to_vec_pretty(value).unwrap(),
        )
        .unwrap();
    }
}

/// Operation bodies/views are a separate complete input, and the adapter's files are not
/// native primitive inputs. All other native backend, index, workspace and Git bytes remain.
pub(super) fn context(loader: &RepoLoader, repo: &TestRepo) -> Value {
    let files = bytes(&repo.repo_path())
        .into_iter()
        .filter(|(path, _)| {
            !["op_store", "op_heads", "musubi"]
                .iter()
                .any(|name| path.starts_with(name))
        })
        .map(|(path, data)| {
            (
                path.to_string_lossy().into_owned(),
                jj_lib::hex_util::encode_hex(&data),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let settings = loader.settings();
    let time = settings
        .operation_timestamp()
        .expect("C requires a fixed operation clock");
    let mut heads = loader.op_heads_store().get_op_heads().block_on().unwrap();
    heads.sort();
    json!({
        "configLayers": settings.config().layers().iter().map(|layer| json!({
            "source": format!("{:?}", layer.source), "path": layer.path,
            "data": layer.data.to_string()
        })).collect::<Vec<_>>(),
        "operationTimestamp": {"millis": time.timestamp.0, "offset": time.tz_offset},
        "api": {"workspaceName": null, "description": "reconcile divergent operations",
            "attributes": []},
        "nativeFiles": files, "physicalGitBytes": byte_manifest(&repo.path().join(".git")),
        "heads": heads.iter().map(|id| id.hex()).collect::<Vec<_>>()
    })
}

fn graph(loader: &RepoLoader, repo: &TestRepo) -> Value {
    let store = loader.op_store();
    let mut ids = BTreeSet::from([store.root_operation_id().clone()]);
    for entry in fs::read_dir(repo.repo_path().join("op_store/operations")).unwrap() {
        let name = entry.unwrap().file_name();
        if let Some(id) = OperationId::try_from_hex(name.to_str().unwrap()) {
            ids.insert(id);
        }
    }
    json!(
        ids.iter()
            .map(|id| {
                let op = store.read_operation(id).block_on().unwrap();
                if id != store.root_operation_id() {
                    assert_eq!(OperationId::new(blake2b_hash(&op).to_vec()), *id);
                }
                let view = store.read_view(&op.view_id).block_on().unwrap();
                raw_body(id, &op, &view, None)
            })
            .collect::<Vec<_>>()
    )
}

type ProbeObservation = (Value, Value, Result<(LocalOp, usize), String>);

pub(super) struct Capture {
    snapshot: tempfile::TempDir,
    relative_repo: PathBuf,
    machine: String,
    config: StackedConfig,
    inputs: Vec<LocalOp>,
    before_graph: Value,
    before_context: Value,
    after: Option<ProbeObservation>,
}

pub(super) fn before(
    node: &NodeRepo,
    repo: &TestRepo,
    env: &TestEnv,
    inputs: &[LocalOp],
) -> Capture {
    let snapshot = musubi_testutil::tempdir();
    env.save(snapshot.path());
    Capture {
        snapshot,
        relative_repo: repo.path().strip_prefix(env.root()).unwrap().to_owned(),
        machine: repo.machine().to_owned(),
        config: node.loader.settings().config().clone(),
        inputs: inputs.to_vec(),
        before_graph: graph(&node.loader, repo),
        before_context: context(&node.loader, repo),
        after: None,
    }
}

pub(super) fn after(
    capture: &mut Capture,
    node: &NodeRepo,
    repo: &TestRepo,
    inputs: &[LocalOp],
    outcome: &Result<(LocalOp, usize), String>,
) {
    assert_eq!(inputs, capture.inputs);
    assert!(capture.after.is_none());
    capture.after = Some((
        graph(&node.loader, repo),
        context(&node.loader, repo),
        outcome.clone(),
    ));
}

#[derive(Debug)]
struct RecordingStore {
    inner: Arc<dyn OpStore>,
    writes: Arc<Mutex<Vec<(OperationId, RawOperation)>>>,
}

#[async_trait]
impl OpStore for RecordingStore {
    fn name(&self) -> &str {
        self.inner.name()
    }
    fn root_operation_id(&self) -> &OperationId {
        self.inner.root_operation_id()
    }
    async fn read_view(&self, id: &ViewId) -> OpStoreResult<View> {
        self.inner.read_view(id).await
    }
    async fn write_view(&self, view: &View) -> OpStoreResult<ViewId> {
        self.inner.write_view(view).await
    }
    async fn read_operation(&self, id: &OperationId) -> OpStoreResult<RawOperation> {
        self.inner.read_operation(id).await
    }
    async fn write_operation(&self, op: &RawOperation) -> OpStoreResult<OperationId> {
        let id = self.inner.write_operation(op).await?;
        self.writes.lock().unwrap().push((id.clone(), op.clone()));
        Ok(id)
    }
    async fn resolve_operation_id_prefix(
        &self,
        prefix: &HexPrefix,
    ) -> OpStoreResult<PrefixResolution<OperationId>> {
        self.inner.resolve_operation_id_prefix(prefix).await
    }
    async fn gc(&self, heads: &[OperationId], newer: SystemTime) -> OpStoreResult<()> {
        self.inner.gc(heads, newer).await
    }
}

/// Replay uses fresh settings/RNG and stores from the full pre-call clone. The supported C
/// scope has fixed time and no rebasing or RNG consumption. A failed scope check is a failed
/// evidence gate, never a shipping refusal or an assumed native law.
pub(super) fn replay(capture: &Capture, index: usize) -> Value {
    let env = TestEnv::restore(capture.snapshot.path());
    let repo = env.repo_handle_at(&capture.machine, &env.root().join(&capture.relative_repo));
    if let Some(path) = std::env::var_os("MUSUBI_NATIVE_LIFECYCLE_DUMP") {
        env.save(&PathBuf::from(path).join(format!("probe-{index}-input-environment")));
    }
    let fresh_settings = || {
        UserSettings::from_config_and_home_dir(
            capture.config.clone(),
            Some(env.root().join("home")),
        )
        .unwrap()
    };
    let settings = fresh_settings();
    let control_settings = fresh_settings();
    let base = default_backend_factories()
        .load_repo(&settings, &repo.repo_path())
        .unwrap();
    let writes = Arc::new(Mutex::new(Vec::new()));
    let store = Arc::new(RecordingStore {
        inner: base.op_store().clone(),
        writes: writes.clone(),
    });
    let loader = RepoLoader::new(
        settings.clone(),
        base.store().clone(),
        base.workspace_store().clone(),
        store,
        base.op_heads_store().clone(),
        base.index_store().clone(),
        base.submodule_store().clone(),
    );
    let before_graph = graph(&loader, &repo);
    let before_context = context(&loader, &repo);
    dump(
        index,
        "inputs",
        &json!({"replayGraph": before_graph,
        "replayContext": before_context, "capturedGraph": capture.before_graph,
        "capturedContext": capture.before_context,
        "capturedInputs": capture.inputs.iter().map(|id| id.0.hex()).collect::<Vec<_>>()}),
    );
    assert_eq!(
        before_graph, capture.before_graph,
        "full replay input graph"
    );
    assert_eq!(
        before_context, capture.before_context,
        "full replay native context"
    );
    let operations = capture
        .inputs
        .iter()
        .map(|id| loader.load_operation(&id.0).block_on().unwrap())
        .collect::<Vec<_>>();
    let outcome = loader
        .merge_operations(operations, None, Some("reconcile divergent operations"), [])
        .block_on()
        .map(|(repo, rebased)| (LocalOp(repo.operation().id().clone()), rebased))
        .map_err(|error| format!("{error:#}"));
    let replay_next = settings.get_rng().new_change_id(16);
    let control_next = control_settings.get_rng().new_change_id(16);
    let after_graph = graph(&loader, &repo);
    let after_context = context(&loader, &repo);
    let (actual_graph, actual_context, actual_outcome) = capture.after.as_ref().unwrap();
    let written = writes
        .lock()
        .unwrap()
        .iter()
        .map(|(id, op)| {
            let view = loader.op_store().read_view(&op.view_id).block_on().unwrap();
            raw_body(id, op, &view, None)
        })
        .collect::<Vec<_>>();
    let result_json = |outcome: &Result<(LocalOp, usize), String>| match outcome {
        Ok((id, rebased)) => json!({"result": id.0.hex(), "rebased": rebased}),
        Err(error) => json!({"error": error}),
    };
    dump(
        index,
        "outputs",
        &json!({"replayGraph": after_graph,
        "replayContext": after_context, "capturedGraph": actual_graph,
        "capturedContext": actual_context, "replayOutcome": result_json(&outcome),
        "capturedOutcome": result_json(actual_outcome), "written": written,
        "replayNextRandom": replay_next.hex(), "controlNextRandom": control_next.hex()}),
    );
    assert_eq!(*actual_outcome, outcome, "actual primitive result");
    let (result_id, rebased) = outcome.unwrap();
    assert_eq!(rebased, 0, "C replay scope excludes rebasing");
    assert_eq!(
        replay_next, control_next,
        "C replay scope must consume no native RNG"
    );
    assert_eq!(*actual_graph, after_graph, "full replay output graph");
    assert_eq!(
        *actual_context, after_context,
        "full replay output native context"
    );
    assert_eq!(
        before_context["heads"], after_context["heads"],
        "unpublished replay"
    );
    json!({"reference": format!("C isolated merge primitive {index}"),
        "contextBefore": before_context, "nativeGraph": before_graph,
        "orderedInputs": capture.inputs.iter().map(|id| id.0.hex()).collect::<Vec<_>>(),
        "written": written, "result": result_id.0.hex(), "contextAfter": after_context})
}
