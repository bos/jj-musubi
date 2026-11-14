//! One authored native criss-cross, a contracted ancestor, and an unpublished cached suffix.
//! The fixed edge table and independently owned native replay supply the expected inputs.

use super::*;
use jj_lib::backend::CommitId;
use jj_lib::content_hash::blake2b_hash;
use jj_lib::op_store::{RefTarget, RemoteRef, RemoteRefState};
use jj_lib::ref_name::{GitRefName, RefName};
use jj_lib::repo::Repo as _;

fn write_native(
    node: &NodeRepo,
    template: &RawOperation,
    view: &View,
    parents: &[LocalOp],
    description: &str,
    offset: i64,
) -> LocalOp {
    let store = node.loader().op_store();
    let mut op = template.clone();
    op.parents = parents.iter().map(|id| id.0.clone()).collect();
    op.metadata.attributes.clear();
    op.metadata.workspace_name = Some("alpha".into());
    op.metadata.description = description.to_owned();
    op.metadata.time.end.timestamp.0 += offset;
    op.view_id = store.write_view(view).block_on().unwrap();
    LocalOp(store.write_operation(&op).block_on().unwrap())
}

fn native_merge(node: &NodeRepo, parents: &[LocalOp]) -> (LocalOp, View) {
    let operations = parents
        .iter()
        .map(|id| node.loader().load_operation(&id.0).block_on().unwrap())
        .collect();
    let (merged, rebased) = node
        .loader()
        .merge_operations(
            operations,
            Some(WorkspaceName::new("alpha")),
            Some("authored multi-base merge"),
            [],
        )
        .block_on()
        .unwrap();
    // Pinned native merge creates commits through rebase_descendants; transaction.write
    // otherwise hashes an operation/view from settings. This finite path must rebase none.
    assert_eq!(
        rebased, 0,
        "authored native replay may not mint RNG-dependent commits"
    );
    (
        LocalOp(merged.op_id().clone()),
        merged.view().store_view().clone(),
    )
}

fn slot(view: &View, local: &CommitId, recorded: &CommitId, workspace: &CommitId) -> View {
    let mut view = view.clone();
    view.wc_commit_ids.insert("alpha".into(), workspace.clone());
    view.local_bookmarks
        .insert("x".into(), RefTarget::normal(local.clone()));
    view.remote_views
        .entry(jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO.to_owned())
        .or_default()
        .bookmarks
        .insert(
            "x".into(),
            RemoteRef {
                target: RefTarget::normal(recorded.clone()),
                state: RemoteRefState::Tracked,
            },
        );
    view.git_refs
        .insert("refs/heads/x".into(), RefTarget::normal(recorded.clone()));
    view
}

#[test]
fn cached_suffix_after_contraction_uses_both_ordered_native_bases() {
    let env = TestEnv::new();
    // This fixture checks native Git bookkeeping, not physical export/HEAD writer laws.
    let repo = env.init_non_colocated_repo("alpha");
    let mut node = open(&repo);
    head(&mut node);
    let initial = node.local_heads().unwrap()[0].clone();
    let loaded = node
        .loader()
        .load_at(&node.loader().load_operation(&initial.0).block_on().unwrap())
        .block_on()
        .unwrap();
    let tree = loaded.store().empty_merged_tree();
    let mut tx = loaded.start_transaction();
    tx.set_workspace_name(WorkspaceName::new("alpha"));
    let mut commit = |parent: &CommitId, name: &str| {
        tx.repo_mut()
            .new_commit(vec![parent.clone()], tree.clone())
            .set_description(name)
            .write()
            .block_on()
            .unwrap()
            .id()
            .clone()
    };
    let one = commit(loaded.store().root_commit_id(), "base commit");
    let [two, three, four] = ["moved", "ours", "theirs"].map(|name| commit(&one, name));
    let pool = tx
        .commit("independent commits for the native merge")
        .block_on()
        .unwrap();
    let anchor = LocalOp(pool.op_id().clone());
    let anchor_canonical = node.canonicalize(&anchor).unwrap();
    let template = raw(&node, &anchor).0;
    let mut common = pool.view().store_view().clone();
    common
        .head_ids
        .extend([one.clone(), two.clone(), three.clone(), four.clone()]);
    let base_view = slot(&common, &one, &one, &one);
    let a = write_native(
        &node,
        &template,
        &base_view,
        std::slice::from_ref(&anchor),
        "drop A",
        1,
    );
    // The kept base ends later, so the first-base-only counterfactual must choose it.
    let kept = write_native(
        &node,
        &template,
        &base_view,
        std::slice::from_ref(&a),
        "kept base",
        3,
    );
    let moved = write_native(
        &node,
        &template,
        &slot(&common, &two, &two, &one),
        std::slice::from_ref(&a),
        "moved base",
        2,
    );
    let (_, left_view) = native_merge(&node, &[kept.clone(), moved.clone()]);
    let left = write_native(
        &node,
        &template,
        &left_view,
        &[kept.clone(), moved.clone()],
        "left merge",
        4,
    );
    let (_, right_view) = native_merge(&node, &[moved.clone(), kept.clone()]);
    let right = write_native(
        &node,
        &template,
        &right_view,
        &[moved.clone(), kept.clone()],
        "right merge",
        4,
    );
    let ours = write_native(
        &node,
        &template,
        &slot(&common, &three, &three, &three),
        std::slice::from_ref(&left),
        "ours",
        5,
    );
    let theirs = write_native(
        &node,
        &template,
        &slot(&common, &four, &two, &four),
        std::slice::from_ref(&right),
        "theirs",
        5,
    );
    node.loader()
        .op_heads_store()
        .update_op_heads(std::slice::from_ref(&anchor.0), &ours.0)
        .block_on()
        .unwrap();
    node.loader()
        .op_heads_store()
        .update_op_heads(&[], &theirs.0)
        .block_on()
        .unwrap();

    // The entire original native graph is captured before record preparation or rendering.
    // Rows: A, kept, moved, left, right, ours, theirs. Every later expected edge is literal.
    let original = [a, kept, moved, left, right, ours.clone(), theirs.clone()];
    let bodies = original.iter().map(|id| raw(&node, id)).collect::<Vec<_>>();
    let canonical = original
        .iter()
        .map(|id| node.canonicalize(id).unwrap())
        .collect::<Vec<_>>();
    let canonical_bodies = canonical
        .iter()
        .map(|id| node.canonical.read_operation(id).unwrap())
        .collect::<Vec<_>>();
    let saved = musubi_testutil::tempdir();
    env.save(saved.path());
    let replay_env = TestEnv::restore(saved.path());
    let replay_repo = replay_env.repo_handle("alpha");
    let before_replay = bytes(repo.path());
    let actor_clock = env.clock().now();
    assert_eq!(
        bytes(replay_repo.path()),
        before_replay,
        "copy the complete native source bytes"
    );
    assert_eq!(
        bytes(&replay_env.root().join("home")),
        bytes(&env.root().join("home"))
    );
    let replay_settings = jj_lib::settings::UserSettings::from_config_and_home_dir(
        node.loader().settings().config().clone(),
        Some(replay_env.root().join("home")),
    )
    .unwrap();
    let mut replay = NodeRepo::open(&replay_repo.repo_path(), &replay_settings).unwrap();
    assert_eq!(
        bytes(repo.path()),
        before_replay,
        "opening the replay changes no actor bytes"
    );
    assert_eq!(
        env.clock().now(),
        actor_clock,
        "replay opening consumes no actor seed"
    );
    let (source_suffix, source_view) = native_merge(&replay, &[ours.clone(), theirs.clone()]);
    let (_, reversed_view) = native_merge(&replay, &[theirs.clone(), ours.clone()]);
    assert_eq!(
        source_view.wc_commit_ids[WorkspaceName::new("alpha")],
        three
    );
    assert_eq!(
        reversed_view.wc_commit_ids[WorkspaceName::new("alpha")],
        four
    );
    assert_ne!(
        source_view, reversed_view,
        "ordered native inputs must distinguish full results"
    );
    let source_body = raw(&replay, &source_suffix).0;
    let suffix = replay.canonicalize(&source_suffix).unwrap();
    let suffix_body = replay.canonical.read_operation(&suffix).unwrap();
    transfer(&replay, &mut node, &suffix);
    let cached = node.realize(&suffix).unwrap();
    assert_eq!(raw(&node, &cached).1, source_view);
    assert_eq!(
        raw(&node, &cached).0.parents,
        [ours.0.clone(), theirs.0.clone()]
    );

    // Independent, fixed contraction blueprint: A disappears; its children point at the
    // anchor. All other ordered edges remain. This is not a copy of the contraction walk.
    // New row numbers: anchor=0, kept=1, moved=2, left=3, right=4, ours=5, theirs=6.
    let edges: [&[usize]; 6] = [&[0], &[0], &[1, 2], &[2, 1], &[3], &[4]];
    let mut expected_canonical = vec![anchor_canonical.clone()];
    let mut expected_physical = vec![anchor.clone()];
    let mut expected_bodies = vec![];
    for (index, parents) in edges.iter().enumerate() {
        let mut canonical_body = canonical_bodies[index + 1].clone();
        canonical_body.parents = parents
            .iter()
            .map(|i| expected_canonical[*i].0.clone())
            .collect();
        let id = CanonicalOp(OperationId::new(blake2b_hash(&canonical_body).to_vec()));
        let mut native = bodies[index + 1].0.clone();
        native.parents = parents
            .iter()
            .map(|i| expected_physical[*i].0.clone())
            .collect();
        native
            .metadata
            .attributes
            .insert(CANONICAL_ATTRIBUTE.to_owned(), id.0.hex());
        // These are authored native inputs in the independently owned replay repository.
        // Its full original view/index context is unchanged; labels do not authenticate U.
        let physical = LocalOp(
            replay
                .loader()
                .op_store()
                .write_operation(&native)
                .block_on()
                .unwrap(),
        );
        expected_canonical.push(id);
        expected_physical.push(physical);
        expected_bodies.push((canonical_body, native, bodies[index + 1].1.clone()));
    }
    let ordered = [expected_physical[5].clone(), expected_physical[6].clone()];
    let operations = ordered
        .iter()
        .map(|id| replay.loader().load_operation(&id.0).block_on().unwrap())
        .collect::<Vec<_>>();
    let bases =
        jj_lib::op_walk::closest_common_ancestors([operations[0].clone()], [operations[1].clone()])
            .block_on()
            .unwrap();
    assert_eq!(
        bases
            .iter()
            .map(|op| op.id().clone())
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([
            expected_physical[1].0.clone(),
            expected_physical[2].0.clone()
        ])
    );
    assert_eq!(
        bases[0].id(),
        &expected_physical[1].0,
        "first base must be the discriminating kept base"
    );
    let (_, expected_view) = native_merge(&replay, &ordered);
    let (_, reversed_contracted) = native_merge(&replay, &[ordered[1].clone(), ordered[0].clone()]);
    assert_eq!(
        reversed_contracted.wc_commit_ids[WorkspaceName::new("alpha")],
        four
    );
    assert_ne!(
        expected_view, reversed_contracted,
        "contracted native order remains discriminating"
    );
    let mut first_only = replay
        .loader()
        .load_at(&operations[0])
        .block_on()
        .unwrap()
        .start_transaction();
    first_only
        .merge_operation(&bases[0], &operations[1])
        .block_on()
        .unwrap();
    assert_ne!(
        first_only.repo().view().store_view(),
        &expected_view,
        "first-base-only native merge must disagree on full output"
    );
    let git = jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
    assert_ne!(
        first_only.repo().view().store_view().remote_views.get(git),
        expected_view.remote_views.get(git)
    );
    assert_eq!(
        expected_view, source_view,
        "contraction alone preserves this authored native result"
    );

    let mut expected_suffix = suffix_body.clone();
    expected_suffix.parents = [
        expected_canonical[5].0.clone(),
        expected_canonical[6].0.clone(),
    ]
    .into();
    let incoming = CanonicalOp(OperationId::new(blake2b_hash(&expected_suffix).to_vec()));
    // Production contraction constructs the arriving input; its complete body/ID must
    // match the independent literal blueprint before it can be used by the adapter.
    let mut contraction = Contraction::new(&replay.canonical, [canonical[0].clone()]).unwrap();
    assert_eq!(
        contraction.images(&replay.canonical, &suffix).unwrap(),
        [incoming.clone()]
    );
    assert_eq!(
        replay.canonical.read_operation(&incoming).unwrap(),
        expected_suffix
    );
    transfer(&replay, &mut node, &incoming);
    let records = [Record::new([HubOp(canonical[0].clone())])];
    node.prepare_records(&RecordPrefix::none(), &records)
        .unwrap();
    for (i, (canonical_body, native_body, view)) in expected_bodies.iter().enumerate() {
        assert_eq!(
            node.canonical
                .read_operation(&expected_canonical[i + 1])
                .unwrap(),
            *canonical_body
        );
        assert_eq!(
            raw(&node, &expected_physical[i + 1]),
            (native_body.clone(), view.clone())
        );
    }

    // A real native command finishes after preparation, before revalidation. It is actor
    // work, not passive observation. Cache loss/reopen keeps the original raw sources.
    repo.jj(&[
        "--ignore-working-copy",
        "--at-op",
        &ours.0.hex(),
        "bookmark",
        "create",
        "late",
        "-r",
        "root()",
    ]);
    let mut command_heads = node.local_heads().unwrap();
    command_heads.sort();
    let command = command_heads
        .iter()
        .find(|id| **id != ours && **id != theirs)
        .expect("the native command creates a new physical head");
    let (command_body, command_view) = raw(&node, command);
    assert_eq!(
        command_body.parents.as_slice(),
        std::slice::from_ref(&ours.0)
    );
    assert_eq!(
        command_view.local_bookmarks[RefName::new("late")]
            .as_normal()
            .unwrap(),
        loaded.store().root_commit_id()
    );
    // Independently capture the original command's canonical projection on its authored
    // old parent before any contracted publication. Supplying that actual source body is
    // an explicit mapped-original precondition, not a choice from the SUT's final heads.
    let command_view_id = replay
        .loader()
        .op_store()
        .write_view(&command_view)
        .block_on()
        .unwrap();
    assert_eq!(command_view_id, command_body.view_id);
    assert_eq!(
        replay
            .loader()
            .op_store()
            .write_operation(&command_body)
            .block_on()
            .unwrap(),
        command.0
    );
    assert_eq!(
        command_view
            .wc_commit_ids
            .keys()
            .map(|name| name.as_str())
            .collect::<Vec<_>>(),
        ["alpha"]
    );
    assert_eq!(
        command_body.metadata.workspace_name.as_deref(),
        Some(WorkspaceName::new("alpha"))
    );
    // This one-copy literal projection supplies no ownership/source-selection oracle.
    // All native command fields stay fixed; only the declared per-machine fields and
    // alpha's known canonical key differ in the canonical encoding.
    let key = format!("{}/alpha", replay.machine().key());
    let mut command_canonical_view = command_view.clone();
    command_canonical_view.git_refs.clear();
    command_canonical_view.git_heads.clear();
    command_canonical_view
        .remote_views
        .remove(jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO);
    command_canonical_view.wc_commit_ids = BTreeMap::from([(
        key.clone().into(),
        command_view.wc_commit_ids[WorkspaceName::new("alpha")].clone(),
    )]);
    let mut original_command = command_body.clone();
    original_command.parents = vec![canonical[5].0.clone()];
    original_command.view_id = replay
        .canonical
        .write_view(&command_canonical_view)
        .unwrap();
    original_command.metadata.workspace_name = Some(key.into());
    original_command
        .metadata
        .attributes
        .insert("musubi.original-parents".to_owned(), canonical[5].0.hex());
    let command_canonical = CanonicalOp(OperationId::new(blake2b_hash(&original_command).to_vec()));
    assert_eq!(replay.canonicalize(command).unwrap(), command_canonical);
    assert_eq!(
        replay.canonical.read_operation(&command_canonical).unwrap(),
        original_command
    );
    transfer(&replay, &mut node, &command_canonical);
    assert_eq!(
        node.canonicalize(command).unwrap(),
        command_canonical,
        "the native late leaf has its independently captured original projection"
    );
    let mut contracted_command = original_command.clone();
    contracted_command.parents = vec![expected_canonical[5].0.clone()];
    let late_canonical = CanonicalOp(OperationId::new(blake2b_hash(&contracted_command).to_vec()));
    let mut late_body = command_body.clone();
    late_body.parents = vec![expected_physical[5].0.clone()];
    late_body
        .metadata
        .attributes
        .insert(CANONICAL_ATTRIBUTE.to_owned(), late_canonical.0.hex());
    let late = LocalOp(
        replay
            .loader()
            .op_store()
            .write_operation(&late_body)
            .block_on()
            .unwrap(),
    );
    drop(node);
    fs::remove_file(repo.repo_path().join("musubi/translation")).unwrap();
    node = open(&repo);
    assert!(
        node.has_record_custody(),
        "restart retains the actual incoming responsibility"
    );
    assert!(
        node.native_receipt().is_none(),
        "the prepared receipt itself is volatile"
    );
    node.prepare_records(&RecordPrefix::none(), &records)
        .unwrap();
    let receipt = node
        .native_receipt()
        .expect("reprepare from retained record bodies");
    assert!(
        receipt
            .base
            .as_ref()
            .is_none_or(|base| base.0 != *node.canonical.root_operation_id()),
        "this is a non-root source graph, without current-Git root fallback"
    );
    assert_eq!(
        raw(&node, &late),
        (late_body.clone(), command_view.clone()),
        "the mapped late leaf is reparented on the fixed ours-prime edge"
    );
    // The suffix is an intermediate realization, not the final published head. Build its
    // entire expected body from the supplied immutable suffix input and declared edges.
    let mut metadata = suffix_body.metadata.clone();
    metadata.workspace_name = source_body.metadata.workspace_name.clone();
    metadata
        .attributes
        .insert(CANONICAL_ATTRIBUTE.to_owned(), incoming.0.hex());
    metadata.attributes.insert(
        "musubi.reserved-workspaces".to_owned(),
        "[\"alpha\"]".to_owned(),
    );
    let expected_suffix_native = RawOperation {
        view_id: ViewId::new(blake2b_hash(&expected_view).to_vec()),
        parents: ordered.iter().map(|id| id.0.clone()).collect(),
        metadata,
        commit_predecessors: source_body.commit_predecessors.clone(),
    };
    assert_eq!(
        replay
            .loader()
            .op_store()
            .write_view(&expected_view)
            .block_on()
            .unwrap(),
        expected_suffix_native.view_id
    );
    let suffix_prime = LocalOp(
        replay
            .loader()
            .op_store()
            .write_operation(&expected_suffix_native)
            .block_on()
            .unwrap(),
    );
    // Use the actual actor loader's full post-restart configuration and copied home, not
    // TestRepo::settings (which allocates a seed). The RNG is independent; the zero-rebase
    // result and pinned transaction-write path bound this fixture's RNG-sensitive effects.
    let actor_bytes = bytes(repo.path());
    let actor_seed = env.clock().now();
    let settings = jj_lib::settings::UserSettings::from_config_and_home_dir(
        node.loader().settings().config().clone(),
        Some(replay_env.root().join("home")),
    )
    .unwrap();
    replay.set_settings(settings);
    let mut final_inputs = [late.clone(), suffix_prime.clone()];
    let end = |id: &LocalOp| raw(&replay, id).0.metadata.time.end.timestamp;
    assert_ne!(
        end(&final_inputs[0]),
        end(&final_inputs[1]),
        "native cleanup order has no tie"
    );
    final_inputs.sort_by_key(end);
    let inputs = final_inputs
        .iter()
        .map(|id| replay.loader().load_operation(&id.0).block_on().unwrap())
        .collect();
    // Match RepoLoader::load_at_head(None)'s native resolver, not native_merge's authoring
    // workspace/description. The caller filters covered heads and sorts by end time.
    let (final_replay, rebased) = replay
        .loader()
        .merge_operations(inputs, None, Some("reconcile divergent operations"), [])
        .block_on()
        .unwrap();
    assert_eq!(
        rebased, 0,
        "final replay must create no RNG-dependent rebased commits"
    );
    let expected_final_id = LocalOp(final_replay.op_id().clone());
    let expected_final = raw(&replay, &expected_final_id);
    // These existing visible heads need no hidden-working-copy repair after the merge.
    // Alongside native rebased=0 and the operation-only transaction.write path, this is
    // the scoped no-new-commit witness; no general RNG-state equivalence is asserted.
    for binding in expected_final.1.wc_commit_ids.values() {
        assert!(expected_final.1.head_ids.contains(binding));
    }
    assert_eq!(
        expected_final.0.parents,
        final_inputs
            .iter()
            .map(|id| id.0.clone())
            .collect::<Vec<_>>()
    );
    assert_eq!(
        expected_final.1.local_bookmarks[RefName::new("late")]
            .as_normal()
            .unwrap(),
        loaded.store().root_commit_id()
    );
    assert_eq!(
        bytes(repo.path()),
        actor_bytes,
        "final replay cannot write actor source bytes"
    );
    assert_eq!(
        env.clock().now(),
        actor_seed,
        "final replay cannot consume an actor seed"
    );
    let events = Arc::new(Mutex::new(vec![]));
    let seen = events.clone();
    let _observe = Observe::new(move |event| seen.lock().unwrap().push(event));
    let _stores = record_stores(&mut node);
    let actual = node.advance(&incoming).unwrap();
    let events = events.lock().unwrap();
    assert!(events.iter().any(|event| matches!(event,
        Event::Reread { captured, actual } if captured == &command_heads && actual == &command_heads)));
    assert!(!events.iter().any(|event| matches!(event,
        Event::CurrentGit { canonical, .. } if canonical == &incoming)));
    assert!(matches!(events.last(), Some(Event::Complete)));
    assert!(
        events.iter().any(|event| matches!(event,
        Event::Write { op, .. } if op == &expected_suffix_native)),
        "the SUT must actually write this new suffix on the witnessed two-base inputs"
    );
    let (actual_body, actual_view) = raw(&node, &actual);
    assert_eq!(
        actual_body.parents,
        ordered.iter().map(|id| id.0.clone()).collect::<Vec<_>>()
    );
    assert_eq!(
        actual_view, expected_view,
        "full native replay, including bindings and Git fields"
    );
    assert_eq!(
        actual_body, expected_suffix_native,
        "returned primary suffix is intermediate"
    );
    // Release the observer and its mutex before inspecting final history. Reading the
    // raw frontier must not call a helper which silently performs another native merge.
    drop(events);
    drop(_observe);
    let final_heads = node.local_heads().unwrap();
    assert_eq!(final_heads, [expected_final_id]);
    let actual_final = raw(&node, &final_heads[0]);
    assert_eq!(
        actual_final, expected_final,
        "full final native inputs retain the late leaf"
    );
    assert!(actual_final.0.parents.contains(&late.0));
    assert!(actual_final.0.parents.contains(&suffix_prime.0));
    assert_eq!(
        actual_final.1.local_bookmarks[RefName::new("late")]
            .as_normal()
            .unwrap(),
        loaded.store().root_commit_id()
    );
    assert!(actual_view.local_bookmarks.contains_key(RefName::new("x")));
    assert!(
        actual_view
            .git_refs
            .contains_key(GitRefName::new("refs/heads/x"))
    );
    // No equality with the old cached ID and no marker-derived/general U/I claim. The
    // independently authored input body, metadata and ordered edge table judge this trace.
}
