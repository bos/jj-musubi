//! Fixed native schedules outside the first lifecycle theorem's E1/E2 restrictions.
//!
//! The abandon schedules characterize native behavior. The helper schedule checks that
//! musubi exports the native merge even if another head arrives during the load.

use super::lifecycle_conformance::bounded_native_command;
use super::*;

fn dumping() -> bool {
    std::env::var_os("MUSUBI_CONCURRENCY_DUMP").is_some()
}

fn dump(name: &str, value: impl FnOnce() -> String) {
    if let Some(path) = std::env::var_os("MUSUBI_CONCURRENCY_DUMP") {
        let path = PathBuf::from(path);
        fs::create_dir_all(&path).unwrap();
        fs::write(path.join(format!("{name}.txt")), value()).unwrap();
    }
}

fn reachable(node: &NodeRepo) -> BTreeSet<LocalOp> {
    reachable_from(node, node.local_heads().unwrap())
}

fn reachable_from(node: &NodeRepo, mut todo: Vec<LocalOp>) -> BTreeSet<LocalOp> {
    let mut seen = BTreeSet::new();
    while let Some(id) = todo.pop() {
        if seen.insert(id.clone()) {
            todo.extend(raw(node, &id).0.parents.into_iter().map(LocalOp));
        }
    }
    seen
}

#[test]
fn abandon_after_equal_reread_characterization() {
    let mut fx = Fixture::new();
    fx.node.advance(&fx.incoming).unwrap();
    fx.repo.jj(&[
        "--ignore-working-copy",
        "bookmark",
        "create",
        "window-parent",
        "-r",
        "@",
    ]);
    let abandoned = fx.node.local_heads().unwrap()[0].clone();
    assert_eq!(raw(&fx.node, &abandoned).0.parents.len(), 1);
    fx.repo.jj(&[
        "--ignore-working-copy",
        "bookmark",
        "create",
        "window-leaf",
        "-r",
        "@",
    ]);
    head(&mut fx.node);
    fx.node.settle().unwrap();
    let before_heads = fx.node.local_heads().unwrap();
    assert_eq!(before_heads.len(), 1);
    let before_view = raw(&fx.node, &before_heads[0]).1;
    let before = dumping().then(|| capture(&fx.node));
    assert_eq!(
        raw(&fx.node, &before_heads[0]).0.parents.as_slice(),
        std::slice::from_ref(&abandoned.0)
    );

    let command = fx.repo.another_copy(fx.repo.path());
    let loader = fx.node.loader.clone();
    let fired = Arc::new(AtomicBool::new(false));
    let ran = fired.clone();
    let events = Arc::new(Mutex::new(vec![]));
    let seen = events.clone();
    let native = Arc::new(Mutex::new(None));
    let result = native.clone();
    let id = abandoned.0.hex();
    let _observer = Observe::new(move |event| {
        seen.lock().unwrap().push(event.clone());
        if matches!(&event, Event::Reread { captured, actual } if captured == actual)
            && !ran.swap(true, Ordering::SeqCst)
        {
            let output =
                bounded_native_command(&command, &["--ignore-working-copy", "op", "abandon", &id]);
            let heads = loader.op_heads_store().get_op_heads().block_on().unwrap();
            *result.lock().unwrap() = Some((output, heads));
        }
    });
    record_stores(&mut fx.node);
    let outcome = fx.node.advance(&fx.child);
    let after_heads = fx.node.local_heads().unwrap();
    assert_eq!(after_heads.len(), 1);
    let after = dumping().then(|| capture(&fx.node));
    let (command, changed) = native
        .lock()
        .unwrap()
        .clone()
        .expect("reach the final equal reread");
    let events = events.lock().unwrap().clone();
    dump("after-reread", || {
        format!(
            "command={command}\nchanged={changed:?}\noutcome={outcome:?}\nabandoned={abandoned:?}\nreachable={:?}\nevents={events:#?}\nbefore={before:#?}\nafter={after:#?}",
            reachable(&fx.node)
        )
    });
    eprintln!(
        "R1 command={command}, changed={changed:?}, outcome={outcome:?}, abandoned_reachable={}",
        reachable(&fx.node).contains(&abandoned)
    );
    assert_eq!(command["success"], true, "{command}");
    assert!(fired.load(Ordering::SeqCst));
    assert_ne!(
        &changed,
        &before_heads
            .iter()
            .map(|id| id.0.clone())
            .collect::<Vec<_>>()
    );
    assert!(
        !reachable_from(&fx.node, changed.iter().cloned().map(LocalOp).collect())
            .contains(&abandoned)
    );
    assert!(outcome.is_ok(), "{outcome:?}");
    // Native abandon changes no immutable body. An already prepared publication can make
    // its old ancestor reachable again, as the plain-jj transaction control below does.
    assert!(reachable(&fx.node).contains(&abandoned));
    let final_view = raw(&fx.node, &after_heads[0]).1;
    for name in ["window-parent", "window-leaf"] {
        let name = jj_lib::ref_name::RefName::new(name);
        assert_eq!(
            final_view.local_bookmarks[name],
            before_view.local_bookmarks[name]
        );
    }
    assert!(
        !events
            .iter()
            .any(|event| matches!(event, Event::RevalidationRetry { .. }))
    );
    drop(_observer);
    let followup = fx.node.merge_heads();
    assert!(followup.is_ok(), "{followup:?}");
    let still_reachable = reachable(&fx.node).contains(&abandoned);
    assert!(still_reachable);
    eprintln!("R1 followup={followup:?}, abandoned_still_reachable={still_reachable}");
    dump("after-reread-followup", || {
        format!(
            "outcome={followup:?}\nabandoned_still_reachable={still_reachable}\nafter={:#?}",
            capture(&fx.node)
        )
    });
}

#[test]
fn helper_exports_when_a_second_head_arrives() {
    helper_schedule(true);
    helper_schedule(false);
}

fn helper_schedule(interleave: bool) {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    repo.jj(&["describe", "-m", "base"]);
    let base = repo.jj(&["log", "--no-graph", "-r", "@", "-T", "commit_id"]);
    let old = repo.jj(&["op", "log", "--no-graph", "-n", "1", "-T", "id"]);
    repo.jj(&["new", "-m", "topic"]);
    repo.jj(&["bookmark", "create", "topic", "-r", "@"]);
    let mut node = open(&repo);
    head(&mut node);
    node.settle().unwrap();
    let before = dumping().then(|| capture(&node));
    let physical_before = repo
        .git(&["rev-parse", "refs/heads/topic"])
        .trim()
        .to_owned();
    let command = repo.another_copy(repo.path());
    let loader = node.loader.clone();
    let fired = Arc::new(AtomicBool::new(false));
    let ran = fired.clone();
    let events = Arc::new(Mutex::new(vec![]));
    let seen = events.clone();
    let native = Arc::new(Mutex::new(None));
    let result = native.clone();
    let execute = move || {
        if !ran.swap(true, Ordering::SeqCst) {
            let output = bounded_native_command(
                &command,
                &[
                    "--ignore-working-copy",
                    "--at-op",
                    old.trim(),
                    "describe",
                    "-r",
                    base.trim(),
                    "-m",
                    "base rewritten",
                ],
            );
            let heads = loader.op_heads_store().get_op_heads().block_on().unwrap();
            *result.lock().unwrap() = Some((output, heads));
        }
    };
    if !interleave {
        execute();
    }
    let _observer = Observe::new(move |event| {
        seen.lock().unwrap().push(event.clone());
        if interleave && matches!(&event, Event::HelperHeads(heads) if heads.len() == 1) {
            execute();
        }
    });
    record_stores(&mut node);
    let outcome = node.merge_heads();
    let after = dumping().then(|| capture(&node));
    let physical_after = repo
        .git(&["rev-parse", "refs/heads/topic"])
        .trim()
        .to_owned();
    let (command, changed) = native
        .lock()
        .unwrap()
        .clone()
        .expect("run the historical describe");
    let events = events.lock().unwrap().clone();
    let heads = node.local_heads().unwrap();
    assert_eq!(heads.len(), 1);
    let view = raw(&node, &heads[0]).1;
    dump(
        if interleave {
            "helper-window"
        } else {
            "helper-closed-control"
        },
        || {
            format!(
                "command={command}\nchanged={changed:?}\noutcome={outcome:?}\nphysical_before={physical_before}\nphysical_after={physical_after}\nview={view:#?}\nevents={events:#?}\nbefore={before:#?}\nafter={after:#?}"
            )
        },
    );
    eprintln!(
        "R2 interleave={interleave}, command={command}, changed={changed:?}, outcome={outcome:?}, physical={physical_after}, bookmark={:?}",
        view.local_bookmarks
            .get(jj_lib::ref_name::RefName::new("topic"))
    );
    assert_eq!(command["success"], true, "{command}");
    assert_eq!(changed.len(), 2, "reach the actual one-to-two-head window");
    assert_eq!(outcome.unwrap(), heads[0]);
    let target = view.local_bookmarks[jj_lib::ref_name::RefName::new("topic")]
        .as_normal()
        .unwrap()
        .hex();
    assert_ne!(
        target, physical_before,
        "the merge really rebases the bookmark"
    );
    assert_eq!(
        physical_after, target,
        "the helper exports the rebased bookmark before another jj command"
    );
    let record = &view.git_refs[jj_lib::ref_name::GitRefName::new("refs/heads/topic")];
    assert_eq!(record.as_normal().unwrap().hex(), target);
    assert!(events.iter().any(|event| matches!(event, Event::Export(_))));
    let initial_head_count = if interleave { 1 } else { 2 };
    assert!(events.iter().any(
        |event| matches!(event, Event::HelperHeads(heads) if heads.len() == initial_head_count)
    ));
}

#[test]
fn native_inflight_transaction_also_restores_abandoned_ancestry() {
    use jj_lib::default_backend_factories::default_backend_factories;
    let env = TestEnv::new();
    let repo = env.init_repo("native");
    repo.jj(&["bookmark", "create", "parent", "-r", "@"]);
    let abandoned = repo.jj(&["op", "log", "--no-graph", "-n", "1", "-T", "id"]);
    repo.jj(&["bookmark", "create", "leaf", "-r", "@"]);
    let loader = default_backend_factories()
        .load_repo(&repo.settings(), &repo.repo_path())
        .unwrap();
    let loaded = loader.load_at_head(None).block_on().unwrap();
    let old_head = loaded.op_id().clone();
    let mut tx = loaded.start_transaction();
    let target = loaded.view().store_view().wc_commit_ids[WorkspaceName::new("native")].clone();
    tx.repo_mut().set_local_bookmark_target(
        jj_lib::ref_name::RefName::new("late"),
        jj_lib::op_store::RefTarget::normal(target),
    );
    let command = bounded_native_command(
        &repo,
        &["--ignore-working-copy", "op", "abandon", abandoned.trim()],
    );
    assert_eq!(command["success"], true, "{command}");
    let rewritten = loader.op_heads_store().get_op_heads().block_on().unwrap();
    assert_eq!(rewritten.len(), 1);
    assert_ne!(rewritten[0], old_head);
    let committed = tx
        .commit("finish the already loaded native command")
        .block_on()
        .unwrap();
    assert_eq!(committed.operation().parent_ids(), [old_head]);
    let heads = loader.op_heads_store().get_op_heads().block_on().unwrap();
    assert_eq!(heads.len(), 2);
    let mut seen = BTreeSet::new();
    let mut todo = heads;
    while let Some(id) = todo.pop() {
        if seen.insert(id.clone()) {
            todo.extend(
                loader
                    .op_store()
                    .read_operation(&id)
                    .block_on()
                    .unwrap()
                    .parents,
            );
        }
    }
    assert!(seen.contains(&OperationId::try_from_hex(abandoned.trim()).unwrap()));
    dump("native-inflight-control", || {
        format!(
            "command={command}\ncommitted={:?}\nreachable={seen:#?}",
            committed.op_id()
        )
    });
}
