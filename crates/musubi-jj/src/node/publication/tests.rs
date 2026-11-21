#![allow(clippy::unwrap_used)]

use super::cleanup::CleanupEffect;
use super::intent::automatic_git_bookkeeping;
use super::*;
use crate::op_id::LocalOp;
use crate::oracle::Oracle;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;
use pollster::FutureExt as _;
use serde_json::json;
use std::collections::HashMap;
use std::fs;

#[test]
fn default_publication_limits_allow_typical_work_and_hold_above_each_boundary() {
    let settings = jj_lib::settings::UserSettings::from_config_and_home_dir(
        jj_lib::config::StackedConfig::with_defaults(),
        None,
    )
    .unwrap();
    let limits = PublicationLimits::load(&settings).unwrap();
    assert!(limits.fits(120, 9_000_000));
    assert!(limits.fits(1000, 64 * 1024 * 1024));
    assert!(!limits.fits(1001, 0));
    assert!(!limits.fits(1, 64 * 1024 * 1024 + 1));
}

#[test]
fn import_invocations_follow_jjs_argument_rendering_and_option_boundaries() {
    for args in [
        "jj git import",
        "jj --no-pager git --ignore-working-copy import",
        "jj -R '/path with spaces' --config 'name=a value' git import",
        "jj '--repository=/path with spaces' git init",
        "jj -R/path git clone url",
    ] {
        assert!(explicit_git_import(args), "{args}");
    }
    for args in [
        "jj --config 'value=git import' status",
        "jj -R 'git import' status",
        "jj --config git import",
        "jj --unknown git import",
        "jj git fetch",
        "jj --config 'unterminated git import",
        "jj -R 'path\\' status ' git import path'",
        "jj -R '/path with spaces' --config 'name=it\\'s a value' git import",
    ] {
        assert!(!explicit_git_import(args), "{args}");
    }
}

fn open(repo: &TestRepo) -> NodeRepo {
    NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap()
}

fn start(repo: &TestRepo) -> NodeRepo {
    let mut node = open(repo);
    node.create_join_operation("musubi: test joins").unwrap();
    node
}

fn report(node: &mut NodeRepo) -> PublicationReport {
    node.outgoing_publication(&mut PublicationCache::default())
        .unwrap()
}

fn commit_id(repo: &TestRepo, revision: &str) -> String {
    repo.jj(&[
        "--ignore-working-copy",
        "log",
        "--no-graph",
        "-r",
        revision,
        "-T",
        "commit_id",
    ])
}

/// Input contains actual jj flags, creation records, selections and complete file closures.
/// Lean independently classifies the outputs, deduplicates content and predicts cleanup.
fn context(node: &NodeRepo, head: &CanonicalOp) -> Vec<u8> {
    let local = node.local_of(head).unwrap();
    let repo = node.repo_at(&local).unwrap();
    serde_json::to_vec(&(
        node.canonical.read_operation(head).unwrap().view_id.hex(),
        node.publication_state_attributes(&repo, head).unwrap(),
        node.publication_foreign_presence(head).unwrap(),
    ))
    .unwrap()
}

struct ModelCleanup {
    content: BTreeSet<FileVersion>,
    intentional: BTreeSet<CommitId>,
    request: serde_json::Value,
    reply: serde_json::Value,
    commits: Vec<CommitId>,
    labels: HashMap<LocalOp, usize>,
    canonical_labels: HashMap<OperationId, usize>,
}

impl ModelCleanup {
    fn assert_applied(
        self,
        node: &mut NodeRepo,
        images: &HashMap<LocalOp, Vec<LocalOp>>,
        checkpoint: &LocalOp,
    ) {
        let actual = report(node);
        assert_eq!(
            actual.content, self.content,
            "applied native content must match Lean"
        );
        let (_, ops) = node.publication_pending().unwrap();
        assert_eq!(
            node.publication_kept_versions(&ops).unwrap(),
            self.intentional,
            "applied native intent must match Lean"
        );
        let index = |id: &CommitId| self.commits.iter().position(|c| c == id).unwrap();
        let heads = node.canonical_heads().unwrap();
        let current = node.canonical.read_operation_view(&heads[0]).unwrap();
        let operations: Vec<_> = ops.iter().enumerate().map(|(i, id)| {
            let op = node.canonical.read_operation(id).unwrap();
            let view = node.canonical.read_view(&op.view_id).unwrap();
            json!({"id":i + 1, "parents":[], "snapshot":op.metadata.is_snapshot,
                "frozen":node.publication_intentional(id, &op, &view).unwrap().iter().map(&index).collect::<Vec<_>>(),
                "writes":[], "selections":[], "required":node.publication_commit_closure(node.required_commits(std::slice::from_ref(id)).unwrap()).unwrap().iter().map(&index).collect::<Vec<_>>()})
        }).collect();
        let mut request = self.request.clone();
        request["actual"] = json!({"heads":[1], "view":view_roots(&current).iter().map(&index).collect::<Vec<_>>(),
            "context":context(node, &heads[0]), "operations":operations});
        let mut oracle = Oracle::spawn();
        assert_eq!(
            request["context"], request["actual"]["context"],
            "native context differs after application"
        );
        assert_eq!(
            oracle.call(&request)["applies"],
            true,
            "native prepared effects must pass the model gate"
        );
        let mut changed_context = request.clone();
        changed_context["actual"]["context"] = json!([999]);
        assert_eq!(oracle.call(&changed_context)["applies"], false);
        let mut changed_content = request;
        changed_content["actual"]["operations"] = json!([]);
        assert_eq!(oracle.call(&changed_content)["applies"], false);

        // Decode physical native images back to distinct source labels; shared boundary
        // parents retain their own labels, rather than all collapsing to root 0.
        let mut labels = self.canonical_labels.clone();
        for (source, targets) in images {
            if !self.request_selected(self.labels[source])
                && let [target] = targets.as_slice()
            {
                labels.insert(node.canonical_of(target).unwrap().0, self.labels[source]);
            }
        }
        let label = |id: &OperationId| labels[id];
        let parents = &self.reply["parents"];
        let fresh = self.reply["parents"].as_array().unwrap().last().unwrap()[0]
            .as_u64()
            .unwrap() as usize;
        for (source, targets) in images {
            if !self.request_selected(self.labels[source]) {
                let [target] = targets.as_slice() else {
                    panic!("survivor has no unique image")
                };
                let op = node
                    .canonical
                    .read_operation(&node.canonical_of(target).unwrap())
                    .unwrap();
                let expected = parents
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|row| row[0] == self.labels[source])
                    .unwrap();
                assert_eq!(
                    json!(op.parents.iter().map(&label).collect::<Vec<_>>()),
                    expected[1]
                );
            }
        }
        let op = node
            .canonical
            .read_operation(&node.canonical_of(checkpoint).unwrap())
            .unwrap();
        let expected = parents
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row[0] == fresh)
            .unwrap();
        assert_eq!(
            json!(op.parents.iter().map(label).collect::<Vec<_>>()),
            expected[1],
            "checkpoint frontier must match Contract.exp"
        );
    }

    fn request_selected(&self, label: usize) -> bool {
        self.reply["selected"]
            .as_array()
            .unwrap()
            .contains(&json!(label))
    }
}

fn compare_model(node: &mut NodeRepo, selected: &[String]) -> ModelCleanup {
    let heads = node.canonical_heads().unwrap();
    let base = node
        .stored_base()
        .unwrap_or_else(|| node.canonical.root_operation_id().clone());
    let known_ops = node
        .canonical
        .ancestors_until(std::slice::from_ref(&base), |_| false)
        .unwrap();
    let known_set: HashSet<_> = known_ops.iter().cloned().collect();
    let ops = node
        .canonical
        .ancestors_until(&heads, |id| known_set.contains(id))
        .unwrap();
    let all_ops = node.canonical.ancestors_until(&heads, |_| false).unwrap();
    let op_index = |id: &CanonicalOp| all_ops.iter().position(|op| op == id).map_or(0, |i| i + 1);
    let known = node.required_commits(&known_ops).unwrap();
    let mut commits = node.required_commits(&ops).unwrap();
    commits.extend(known.iter().cloned());
    let current = node.canonical.read_operation_view(&heads[0]).unwrap();
    let view = view_roots(&current);
    commits.extend(view.iter().cloned());
    let mut facts = vec![];
    for id in &ops {
        let op = node.canonical.read_operation(id).unwrap();
        let view = node.canonical.read_view(&op.view_id).unwrap();
        let frozen = retained_publication_intent(&op).unwrap();
        if let Some(roots) = &frozen {
            commits.extend(roots.iter().cloned());
        }
        let checkpoint = op.metadata.attributes.contains_key(CHECKPOINT_ATTRIBUTE);
        let initial = node.joins.is_join(id);
        let automatic = !initial
            && (op.metadata.is_snapshot
                || op.metadata.description == "reconcile divergent operations"
                || automatic_git_bookkeeping(&op)
                || (op.metadata.description.starts_with("musubi:") && !checkpoint));
        let mut history: Vec<_> = if initial {
            node.publication_initial_intentional(id)
                .unwrap()
                .into_iter()
                .collect()
        } else if checkpoint {
            vec![]
        } else {
            node.publication_selections(&op, &view)
                .unwrap()
                .0
                .into_iter()
                .collect()
        };
        if !checkpoint && !initial {
            for (commit, previous) in op.commit_predecessors.iter().flatten() {
                if previous.is_empty() && view.wc_commit_ids.values().any(|wc| wc == commit) {
                    history.extend(
                        node.loader
                            .store()
                            .get_commit(commit)
                            .unwrap()
                            .parent_ids()
                            .iter()
                            .cloned(),
                    );
                }
            }
        }
        let writes: Vec<_> = op
            .commit_predecessors
            .iter()
            .flatten()
            .map(|(id, previous)| {
                (
                    id.clone(),
                    !checkpoint && view.wc_commit_ids.values().any(|wc| wc == id),
                    !previous.is_empty(),
                )
            })
            .collect();
        let required = node
            .publication_commit_closure(node.required_commits(std::slice::from_ref(id)).unwrap())
            .unwrap();
        commits.extend(required.iter().cloned());
        commits.extend(history.iter().cloned());
        commits.extend(writes.iter().map(|w| w.0.clone()));
        let parents: Vec<_> = op
            .parents
            .iter()
            .map(|p| op_index(&CanonicalOp(p.clone())))
            .collect();
        facts.push((automatic, frozen, history, writes, required, parents));
    }
    let commits: Vec<_> = commits.into_iter().collect();
    let index = |id: &CommitId| commits.iter().position(|c| c == id).unwrap();
    let closures: Vec<_> = commits
        .iter()
        .map(|id| {
            node.publication_files([id.clone()], &Closure::default(), &Closure::default())
                .unwrap()
        })
        .collect();
    let objects: Vec<_> = closures
        .iter()
        .flatten()
        .map(|file| file.id.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let paths: Vec<_> = closures
        .iter()
        .flatten()
        .map(|file| file.path.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let mut sizes = vec![0; objects.len()];
    for (i, id) in objects.iter().enumerate() {
        let file = closures
            .iter()
            .flatten()
            .find(|file| file.id == *id)
            .unwrap();
        sizes[i] = node.publication_content_bytes(file).unwrap();
    }
    let file_json = |file: &FileVersion| {
        json!({
            "path": paths.iter().position(|p| p == &file.path).unwrap(),
            "object": objects.iter().position(|id| id == &file.id).unwrap(),
        })
    };
    let operations: Vec<_> = facts.into_iter().enumerate().map(|(i, (snapshot, frozen, history, writes, required, parents))| json!({
        "id": op_index(&ops[i]),
        "parents": parents,
        "frozen": frozen.map(|roots| roots.iter().map(&index).collect::<Vec<_>>()),
        "snapshot": snapshot,
        "writes": writes.iter().map(|(id, tip, rewritten)| json!({"commit": index(id), "workspaceTip": tip, "rewritten": rewritten})).collect::<Vec<_>>(),
        "selections": history.iter().map(&index).collect::<Vec<_>>(),
        "required": required.iter().map(&index).collect::<Vec<_>>(),
    })).collect();
    let selected_ids: Vec<_> = ops
        .iter()
        .enumerate()
        .filter(|(_, id)| {
            node.local_of(id).is_some_and(|local| {
                selected
                    .iter()
                    .any(|prefix| local.0.hex().starts_with(prefix))
            })
        })
        .map(|(_, id)| op_index(id))
        .collect();
    let actual = report(node);
    let model_heads: Vec<_> = heads.iter().map(&op_index).collect();
    let intent_known = ops.iter().all(|id| {
        !node
            .publication_intent_is_uncertain(id, &node.canonical.read_operation(id).unwrap())
            .unwrap()
    });
    let request = json!({
        "op":"publication", "commits": closures.iter().map(|files| files.iter().map(&file_json).collect::<Vec<_>>()).collect::<Vec<_>>(),
        "sizes":sizes, "operations":operations, "known":known.iter().map(&index).collect::<Vec<_>>(),
        "view": view.iter().map(&index).collect::<Vec<_>>(), "selected":selected_ids,
        "maxFiles":actual.limits.files, "maxBytes":actual.limits.bytes,
        "heads": model_heads, "expectedHeads": model_heads, "context":context(node, &heads[0]),
        "planIdentity": actual.token.as_bytes(), "approval":null, "actual":null, "intentKnown":intent_known,
    });
    let mut oracle = Oracle::spawn();
    let mut reply = oracle.call(&request);
    reply["selected"] = json!(selected_ids);
    assert_eq!(reply["ok"], true, "{reply}");
    assert_eq!(reply["fileCount"], actual.files.len());
    assert_eq!(reply["bytes"], actual.bytes);
    assert_eq!(reply["fits"], !actual.held());
    assert_eq!(reply["maySend"], !actual.held());
    assert_eq!(reply["applies"], intent_known);
    let decode_files = |value: &serde_json::Value| {
        value
            .as_array()
            .unwrap()
            .iter()
            .map(|f| FileVersion {
                path: paths[f["path"].as_u64().unwrap() as usize].clone(),
                id: objects[f["object"].as_u64().unwrap() as usize].clone(),
            })
            .collect::<BTreeSet<_>>()
    };
    assert_eq!(decode_files(&reply["files"]), actual.content);
    let intentional: BTreeSet<_> = reply["intentional"]
        .as_array()
        .unwrap()
        .iter()
        .map(|id| commits[id.as_u64().unwrap() as usize].clone())
        .collect();
    let accounting: BTreeSet<_> = ops
        .iter()
        .flat_map(|id| {
            let op = node.canonical.read_operation(id).unwrap();
            node.publication_intentional(id, &op, &node.canonical.read_view(&op.view_id).unwrap())
                .unwrap()
        })
        .collect();
    assert_eq!(intentional, accounting);
    if !intent_known {
        assert!(node.publication_kept_versions(&ops).is_err());
    }
    let mut approved = request.clone();
    approved["approval"] = json!({"identity":actual.token.as_bytes(), "extra":reply["files"]});
    assert_eq!(oracle.call(&approved)["maySend"], true);
    let mut old_approval = approved.clone();
    old_approval["approval"]["identity"] = json!([999]);
    assert_eq!(oracle.call(&old_approval)["maySend"], !actual.held());
    let mut stale = request.clone();
    stale["expectedHeads"] = json!([ops.len() + 99]);
    assert_eq!(oracle.call(&stale)["applies"], false);
    let content = decode_files(&reply["afterFiles"]);
    if !selected.is_empty() {
        let after = node
            .preview_publication_cleanup(selected, &mut PublicationCache::default())
            .unwrap()
            .after;
        assert_eq!(reply["afterFileCount"], after.files.len());
        assert_eq!(reply["afterBytes"], after.bytes);
        assert_eq!(reply["afterFits"], !after.held());
        assert_eq!(content, after.content);
    }
    let mut labels: HashMap<_, _> = all_ops
        .iter()
        .filter_map(|id| node.local_of(id).map(|local| (local, op_index(id))))
        .collect();
    labels.insert(
        LocalOp(node.loader.op_store().root_operation_id().clone()),
        0,
    );
    let mut canonical_labels: HashMap<_, _> = all_ops
        .iter()
        .map(|id| (id.0.clone(), op_index(id)))
        .collect();
    canonical_labels.insert(node.canonical.root_operation_id().0.clone(), 0);
    ModelCleanup {
        content,
        intentional,
        request,
        reply,
        commits,
        labels,
        canonical_labels,
    }
}

#[test]
fn partial_commit_cleanup_keeps_committed_and_uncommitted_work() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = start(&repo);
    repo.write_file("README.txt", "intended README\n");
    repo.write_file("AGENTS.md", "first instructions\n");
    for i in 0..12 {
        repo.write_file(&format!("junk/{i}"), &format!("accident {i}\n"));
    }
    repo.jj(&["status"]);
    repo.jj(&["commit", "README.txt", "-m", "Keep README"]);
    let readme = commit_id(&repo, "@-");
    repo.write_file("AGENTS.md", "current instructions\n");
    fs::remove_dir_all(repo.path().join("junk")).unwrap();
    repo.jj(&["status"]);
    let current = commit_id(&repo, "@");
    let before = report(&mut node);
    assert!(!before.files.iter().any(|file| file.path == "README.txt"));
    assert_eq!(before.files.len(), 13);
    let selected: Vec<_> = before
        .operations
        .iter()
        .map(|operation| operation.id.clone())
        .collect();
    let model = compare_model(&mut node, &selected);
    let mut cache = PublicationCache::default();
    let plan = node
        .preview_publication_cleanup(&selected, &mut cache)
        .unwrap();
    assert_eq!(plan.after.files.len(), 1);
    assert_eq!(plan.after.files[0].path, "AGENTS.md");
    assert_eq!(plan.after.bytes, "current instructions\n".len() as u64);
    let _lock = publication_lock(&repo.repo_path()).unwrap();
    let CleanupEffect {
        pruned: count,
        images,
        checkpoint,
    } = node
        .apply_publication_cleanup_mapped(&selected, &plan.token, &mut cache)
        .unwrap();
    assert_eq!(count, selected.len());
    assert_eq!(commit_id(&repo, "@-"), readme);
    assert_eq!(commit_id(&repo, "@"), current);
    assert_eq!(
        fs::read_to_string(repo.path().join("AGENTS.md")).unwrap(),
        "current instructions\n"
    );
    assert!(!repo.path().join("junk").exists());
    let after = report(&mut open(&repo));
    assert_eq!(after.files.len(), 1);
    assert_eq!(after.bytes, plan.after.bytes);
    model.assert_applied(&mut open(&repo), &images, &checkpoint);
    compare_model(&mut open(&repo), &[]);
}

#[test]
fn snapshot_bytes_are_unique_and_intentional_commits_are_exempt() {
    let env = TestEnv::new();
    let repo = env.init_simple_repo("alpha");
    let mut node = start(&repo);
    repo.write_file("a", "same contents");
    repo.write_file("b", "same contents");
    repo.jj(&["status"]);
    let before = report(&mut node);
    assert_eq!(before.files.len(), 2);
    assert_eq!(before.bytes, "same contents".len() as u64);
    compare_model(&mut node, &[]);
    repo.jj(&["commit", "-m", "Keep both"]);
    assert_eq!(report(&mut node).bytes, 0);
    compare_model(&mut node, &[]);
    repo.write_file("another-path", "same contents");
    repo.jj(&["status"]);
    let aliases = report(&mut node);
    assert_eq!(aliases.files.len(), 1);
    assert_eq!(
        aliases.bytes, 0,
        "a new path reuses intentional content bytes"
    );
    compare_model(&mut node, &[]);
    repo.jj(&["bookmark", "create", "saved", "-r", "@"]);
    assert!(
        report(&mut node).files.is_empty(),
        "explicitly naming a WC version retains it intentionally"
    );
    repo.write_file("later", "still only a snapshot");
    repo.jj(&["status"]);
    let later = report(&mut node);
    assert_eq!(later.files.len(), 1);
    assert_eq!(
        later.files[0].path, "later",
        "automatically moving that bookmark does not approve later content"
    );
    compare_model(&mut node, &[]);
}

#[test]
fn a_small_number_of_large_transient_files_hits_the_byte_budget() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut config = repo.settings().config().clone();
    config.add_layer(
        jj_lib::config::ConfigLayer::parse(
            jj_lib::config::ConfigSource::CommandArg,
            "musubi.publication.max-bytes = '8 MiB'",
        )
        .unwrap(),
    );
    let settings = repo.settings().with_new_config(config).unwrap();
    let mut node = NodeRepo::open(&repo.repo_path(), &settings).unwrap();
    node.create_join_operation("musubi: test joins").unwrap();
    for i in 0..10 {
        let contents = char::from(b'a' + i).to_string().repeat(900_000);
        repo.write_file(&format!("junk/{i}"), &contents);
    }
    repo.jj(&["status"]);
    fs::remove_dir_all(repo.path().join("junk")).unwrap();
    repo.jj(&["status"]);
    let report = report(&mut node);
    assert_eq!(report.files.len(), 10);
    assert_eq!(report.bytes, 9_000_000);
    assert!(report.held());
    compare_model(&mut node, &[]);
}

// Exercise cleanup directly, without a CLI preflight snapshot, then let jj recover
// the workspace as it normally would after a history rewrite.
fn cleanup_without_snapshot(stale: bool, secondary: bool, same_tree: bool) {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = start(&repo);
    let join = node.local_heads().unwrap()[0].clone();
    let second_path = env.root().join("second");
    repo.jj(&[
        "workspace",
        "add",
        "--name",
        "second",
        second_path.to_str().unwrap(),
    ]);
    let second = repo.another_copy(&second_path);
    let (actor, other, name) = if secondary {
        (&second, &repo, "second@")
    } else {
        (&repo, &second, "alpha@")
    };
    actor.write_file("accident", "unwanted history");
    actor.jj(&["status"]);
    fs::remove_file(actor.path().join("accident")).unwrap();
    actor.jj(&["status"]);
    actor.write_file("local", "unsnapshotted work");
    if stale {
        if same_tree {
            other.jj(&["describe", "-r", name, "-m", "rewritten elsewhere"]);
        } else {
            other.write_file("upstream", "recorded elsewhere");
            other.jj(&["commit", "-m", "upstream"]);
            other.jj(&["restore", "--from", "@-", "--into", name]);
        }
    }
    let select = |node: &mut NodeRepo| {
        let (_, pending) = node.publication_pending().unwrap();
        pending
            .iter()
            .filter_map(|id| node.local_of(id))
            .filter(|id| *id != join)
            .map(|id| id.0.hex())
            .collect::<Vec<_>>()
    };
    if stale {
        let selected = select(&mut node);
        let heads = node.local_heads().unwrap();
        let mut cache = PublicationCache::default();
        let plan = node
            .preview_publication_cleanup(&selected, &mut cache)
            .unwrap();
        let err = node
            .apply_publication_cleanup(&selected, &plan.token, &mut cache)
            .unwrap_err();
        assert!(
            err.to_string().contains("must be updated before pruning"),
            "{err}"
        );
        assert_eq!(
            node.local_heads().unwrap(),
            heads,
            "refusal must not prune history"
        );
        assert_eq!(
            fs::read_to_string(actor.path().join("local")).unwrap(),
            "unsnapshotted work"
        );
        assert!(!actor.path().join("upstream").exists());
        actor.jj(&["status"]);
        node = open(&repo);
    }
    let before = report(&mut node);
    assert!(before.files.iter().any(|file| file.path == "accident"));
    let selected = select(&mut node);
    let recorded = actor.jj(&[
        "--ignore-working-copy",
        "op",
        "log",
        "--no-graph",
        "-n",
        "1",
        "-T",
        "id",
    ]);
    let files = || {
        (
            fs::read(actor.path().join("local")).ok(),
            fs::read(actor.path().join("upstream")).ok(),
        )
    };
    let disk = files();
    let mut cache = PublicationCache::default();
    let plan = node
        .preview_publication_cleanup(&selected, &mut cache)
        .unwrap();
    node.apply_publication_cleanup(&selected, &plan.token, &mut cache)
        .unwrap();
    assert_eq!(
        files(),
        disk,
        "cleanup must leave checked-out files untouched"
    );
    assert!(
        !report(&mut open(&repo))
            .files
            .iter()
            .any(|file| file.path == "accident")
    );
    let history = actor.jj(&[
        "--ignore-working-copy",
        "op",
        "log",
        "--no-graph",
        "-T",
        "id ++ \"\\n\"",
    ]);
    assert!(
        !history.lines().any(|id| id == recorded),
        "the recorded basis must actually be pruned"
    );
    repo.jj(&["--ignore-working-copy", "util", "gc", "--expire", "now"]);
    actor.jj(&["status"]);
    assert_eq!(
        actor.jj(&[
            "--ignore-working-copy",
            "file",
            "show",
            "local",
            "-r",
            "heads(all() & files(local))"
        ]),
        "unsnapshotted work"
    );
    assert!(
        !report(&mut open(&repo))
            .files
            .iter()
            .any(|file| file.path == "accident"),
        "jj recovery must not resurrect pruned history"
    );
}

#[test]
fn cleanup_without_snapshot_preserves_fresh_workspace_edits() {
    cleanup_without_snapshot(false, false, false);
}

#[test]
fn cleanup_without_snapshot_preserves_stale_invoking_workspace_edits() {
    cleanup_without_snapshot(true, false, false);
}

#[test]
fn cleanup_without_snapshot_preserves_stale_secondary_workspace_edits() {
    cleanup_without_snapshot(true, true, false);
}

#[test]
fn cleanup_without_snapshot_checks_commit_identity_even_when_trees_match() {
    cleanup_without_snapshot(true, true, true);
}

#[test]
fn cleanup_refuses_unavailable_or_reassigned_workspace_paths() {
    let env = TestEnv::new();
    let repo = env.init_simple_repo("alpha");
    let mut node = start(&repo);
    let join = node.local_heads().unwrap()[0].clone();
    let second = env.root().join("second");
    repo.jj(&[
        "workspace",
        "add",
        "--name",
        "feat/x",
        second.to_str().unwrap(),
    ]);
    repo.write_file("accident", "unwanted history");
    repo.jj(&["status"]);
    fs::remove_file(repo.path().join("accident")).unwrap();
    repo.jj(&["status"]);
    let before = report(&mut node);
    let selected: Vec<_> = before.operations.iter().map(|op| op.id.clone()).collect();
    let mut cache = PublicationCache::default();
    let plan = node
        .preview_publication_cleanup(&selected, &mut cache)
        .unwrap();
    let heads = node.local_heads().unwrap();
    let saved = env.root().join("saved-second");
    fs::rename(&second, &saved).unwrap();
    let err = node
        .apply_publication_cleanup(&selected, &plan.token, &mut cache)
        .unwrap_err();
    assert!(
        err.to_string().contains("cannot read workspace feat/x"),
        "{err}"
    );
    assert_eq!(node.local_heads().unwrap(), heads);

    let foreign = env.init_repo_with_workspace("second", "feat/x");
    foreign.write_file("private", "another repo's pending work");
    let foreign_head = || {
        foreign.jj(&[
            "--ignore-working-copy",
            "op",
            "log",
            "--no-graph",
            "-n",
            "1",
            "-T",
            "id",
        ])
    };
    let old = foreign_head();
    let err = node
        .apply_publication_cleanup(&selected, &plan.token, &mut cache)
        .unwrap_err();
    assert!(
        err.to_string().contains("no longer identifies this repo"),
        "{err}"
    );
    assert_eq!(node.local_heads().unwrap(), heads);
    assert_eq!(foreign_head(), old);
    assert_eq!(
        fs::read_to_string(second.join("private")).unwrap(),
        "another repo's pending work"
    );
    fs::rename(&second, env.root().join("foreign-repo")).unwrap();
    fs::rename(&saved, &second).unwrap();
    let name = jj_lib::ref_name::WorkspaceName::new("feat/x");
    // A workspace can predate jj's path registry. Exercise that supported store state
    // through the public store API, without inventing any checked-out file state.
    node.loader.workspace_store().forget(&[name]).unwrap();
    let err = node
        .apply_publication_cleanup(&selected, &plan.token, &mut cache)
        .unwrap_err();
    assert!(
        err.to_string().contains("cannot locate workspace feat/x"),
        "{err}"
    );
    assert_eq!(node.local_heads().unwrap(), heads);
    node.loader.workspace_store().add(name, &second).unwrap();

    // Native jj permits a moved workspace's old path to be reused by another.
    // The earlier name must not be silently overwritten when collecting the paths.
    let reused = env.root().join("reused");
    repo.jj(&[
        "workspace",
        "add",
        "--name",
        "aaa",
        reused.to_str().unwrap(),
    ]);
    let moved = env.root().join("moved-aaa");
    fs::rename(&reused, &moved).unwrap();
    fs::write(moved.join("pending"), "moved workspace's edit").unwrap();
    repo.jj(&[
        "workspace",
        "add",
        "--name",
        "zzz",
        reused.to_str().unwrap(),
    ]);
    node = open(&repo);
    let (_, pending) = node.publication_pending().unwrap();
    let selected: Vec<_> = pending
        .iter()
        .filter_map(|id| node.local_of(id))
        .filter(|id| *id != join)
        .map(|id| id.0.hex())
        .collect();
    let mut cache = PublicationCache::default();
    let plan = node
        .preview_publication_cleanup(&selected, &mut cache)
        .unwrap();
    let heads = node.local_heads().unwrap();
    let err = node
        .apply_publication_cleanup(&selected, &plan.token, &mut cache)
        .unwrap_err();
    assert!(err.to_string().contains("share a registered path"), "{err}");
    assert_eq!(node.local_heads().unwrap(), heads);
    node.loader
        .workspace_store()
        .add(jj_lib::ref_name::WorkspaceName::new("aaa"), &moved)
        .unwrap();

    node.apply_publication_cleanup(&selected, &plan.token, &mut cache)
        .unwrap();
    assert_eq!(
        fs::read_to_string(moved.join("pending")).unwrap(),
        "moved workspace's edit"
    );
    assert!(
        !report(&mut open(&repo))
            .files
            .iter()
            .any(|file| file.path == "accident")
    );
}

#[test]
fn cleanup_includes_only_its_own_preflight_snapshots() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = start(&repo);
    // An unselected snapshot keeps an older version even though its file is now gone.
    repo.write_file("unselected", "keep this recovery version");
    repo.jj(&["status"]);
    fs::remove_file(repo.path().join("unselected")).unwrap();
    repo.jj(&["status"]);
    repo.write_file("accident", "remove this version");
    repo.jj(&["status"]);
    let selected = repo.jj(&[
        "--ignore-working-copy",
        "op",
        "log",
        "--no-graph",
        "-n1",
        "-T",
        "id",
    ]);
    fs::remove_file(repo.path().join("accident")).unwrap();
    let invocation = "5d0e52764e834f55a86ad193beaf1820";
    repo.jj(&[
        "--config=musubi.prune-snapshot=5d0e52764e834f55a86ad193beaf1820",
        "util",
        "snapshot",
    ]);
    // A later native command must not be mistaken for the preflight capture.
    repo.write_file("later", "keep later work");
    repo.jj(&["status"]);
    let mut selected = vec![selected];
    let captures = node.publication_snapshots_from(invocation).unwrap();
    assert_eq!(captures.len(), 1);
    selected.extend(captures);
    let mut cache = PublicationCache::default();
    let plan = node
        .preview_publication_cleanup(&selected, &mut cache)
        .unwrap();
    node.apply_publication_cleanup(&selected, &plan.token, &mut cache)
        .unwrap();
    let outgoing = report(&mut open(&repo));
    assert!(outgoing.files.iter().any(|file| file.path == "unselected"));
    assert!(!outgoing.files.iter().any(|file| file.path == "accident"));
    assert_eq!(
        repo.jj(&["--ignore-working-copy", "file", "show", "later"]),
        "keep later work"
    );
    repo.jj(&["status"]);
    assert!(
        !report(&mut open(&repo))
            .files
            .iter()
            .any(|file| file.path == "accident")
    );
}

#[test]
fn cleanup_requires_jj_to_record_file_removals() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = start(&repo);
    let join = node.local_heads().unwrap()[0].clone();
    repo.write_file("accident", "unwanted history");
    repo.jj(&["status"]);
    fs::remove_file(repo.path().join("accident")).unwrap();
    for recorded_removal in [false, true] {
        if recorded_removal {
            repo.jj(&["status"]);
            node = open(&repo);
        }
        let (_, pending) = node.publication_pending().unwrap();
        let selected: Vec<_> = pending
            .iter()
            .filter_map(|id| node.local_of(id))
            .filter(|id| *id != join)
            .map(|id| id.0.hex())
            .collect();
        let mut cache = PublicationCache::default();
        let plan = node
            .preview_publication_cleanup(&selected, &mut cache)
            .unwrap();
        assert_eq!(
            plan.after.files.iter().any(|file| file.path == "accident"),
            !recorded_removal
        );
        node.apply_publication_cleanup(&selected, &plan.token, &mut cache)
            .unwrap();
        assert!(!repo.path().join("accident").exists());
        assert_eq!(
            report(&mut open(&repo))
                .files
                .iter()
                .any(|file| file.path == "accident"),
            !recorded_removal
        );
    }
}

#[test]
fn cleanup_and_approval_are_bound_to_the_inspected_history() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = start(&repo);
    repo.write_file("accident", "unwanted");
    repo.jj(&["status"]);
    fs::remove_file(repo.path().join("accident")).unwrap();
    repo.jj(&["status"]);
    let before = report(&mut node);
    let selected: Vec<_> = before.operations.iter().map(|op| op.id.clone()).collect();
    let mut cache = PublicationCache::default();
    let plan = node
        .preview_publication_cleanup(&selected, &mut cache)
        .unwrap();
    approve_publication(&repo.repo_path(), &before, &before.token).unwrap();
    assert!(publication_approved(&repo.repo_path(), &before));
    let mut config = repo.settings().config().clone();
    config.add_layer(
        jj_lib::config::ConfigLayer::parse(
            jj_lib::config::ConfigSource::CommandArg,
            "musubi.publication.max-bytes = 1",
        )
        .unwrap(),
    );
    let settings = repo.settings().with_new_config(config).unwrap();
    let mut limited = NodeRepo::open(&repo.repo_path(), &settings).unwrap();
    let changed_limits = report(&mut limited);
    assert_ne!(before.token, changed_limits.token);
    assert!(!publication_approved(&repo.repo_path(), &changed_limits));
    compare_model(&mut limited, &[]);
    repo.write_file("wanted", "new unsent work");
    repo.jj(&["status"]);
    assert!(!publication_approved(&repo.repo_path(), &report(&mut node)));
    assert!(
        node.apply_publication_cleanup(&selected, &plan.token, &mut cache)
            .is_err()
    );
    assert_eq!(
        fs::read_to_string(repo.path().join("wanted")).unwrap(),
        "new unsent work"
    );
    assert!(
        report(&mut node)
            .files
            .iter()
            .any(|file| file.path == "accident")
    );
}

#[test]
fn unrelated_explicit_work_does_not_bless_automatic_descendant_rewrites() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = start(&repo);
    repo.write_file("base", "base");
    repo.jj(&["commit", "-m", "base"]);
    let base = commit_id(&repo, "@-");
    repo.write_file("source", "source");
    repo.jj(&["commit", "-m", "source"]);
    let source = commit_id(&repo, "@-");
    repo.write_file("child", "child");
    repo.jj(&["commit", "-m", "child"]);
    repo.jj(&["edit", source.trim()]);
    repo.write_file("junk", "not intended");
    repo.jj(&["status"]);
    repo.jj(&["bookmark", "set", "unrelated", "-r", base.trim()]);
    assert!(
        report(&mut node)
            .files
            .iter()
            .any(|file| file.path == "junk")
    );
    compare_model(&mut node, &[]);
}

#[test]
fn automatic_operation_reconciliation_does_not_bless_snapshot_contents() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = start(&repo);
    let basis = repo.jj(&[
        "--ignore-working-copy",
        "op",
        "log",
        "--no-graph",
        "-n1",
        "-T",
        "id",
    ]);
    repo.write_file("junk", "not intended");
    repo.jj(&["status"]);
    repo.jj(&[
        "--at-op",
        basis.trim(),
        "describe",
        "-m",
        "Describe the empty change",
    ]);
    repo.jj(&["status"]);
    let heads = node.canonical_heads().unwrap();
    let ops = node.canonical.ancestors_until(&heads, |_| false).unwrap();
    assert!(ops.iter().any(|id| {
        node.canonical
            .read_operation(id)
            .unwrap()
            .metadata
            .description
            == "reconcile divergent operations"
    }));
    assert!(
        report(&mut node)
            .files
            .iter()
            .any(|file| file.path == "junk")
    );
    compare_model(&mut node, &[]);
    let selected = vec![
        report(&mut node)
            .operations
            .into_iter()
            .find(|op| op.snapshot)
            .unwrap()
            .id,
    ];
    fs::remove_file(repo.path().join("junk")).unwrap();
    repo.jj(&["status"]);
    let model = compare_model(&mut node, &selected);
    let mut cache = PublicationCache::default();
    let plan = node
        .preview_publication_cleanup(&selected, &mut cache)
        .unwrap();
    let CleanupEffect {
        images, checkpoint, ..
    } = node
        .apply_publication_cleanup_mapped(&selected, &plan.token, &mut cache)
        .unwrap();
    model.assert_applied(&mut open(&repo), &images, &checkpoint);
}

#[test]
fn a_first_join_exempts_existing_commits_but_not_uncommitted_additions() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    repo.write_file("committed", "intentional contents");
    repo.jj(&["commit", "-m", "Keep committed"]);
    repo.write_file("uncommitted", "still provisional");
    repo.jj(&["status"]);
    let mut node = start(&repo);
    let report = report(&mut node);
    assert_eq!(report.files.len(), 1);
    assert_eq!(report.files[0].path, "uncommitted");
    compare_model(&mut node, &[]);
}

#[test]
fn removing_a_snapshots_parent_does_not_turn_unrelated_work_into_intent() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = start(&repo);
    node.initialize_publication_offers().unwrap();
    repo.write_file("junk", "unwanted content");
    repo.jj(&["status"]);
    let before = report(&mut node);
    let selected = vec![before.operations.last().unwrap().id.clone()];
    repo.jj(&["bookmark", "create", "unrelated", "-r", "root()"]);
    fs::remove_file(repo.path().join("junk")).unwrap();
    repo.jj(&["status"]);
    let model = compare_model(&mut node, &selected);
    let mut cache = PublicationCache::default();
    let plan = node
        .preview_publication_cleanup(&selected, &mut cache)
        .unwrap();
    // Reproduce a crash after one prepared survivor was canonicalized, before head install.
    let store = node.loader.op_store().clone();
    let source_head = node.local_heads().unwrap()[0].clone();
    let head_body = store.read_operation(&source_head.0).block_on().unwrap();
    let bookmark = LocalOp(head_body.parents[0].clone());
    let canonical = node.canonical_of(&bookmark).unwrap();
    let op = node.canonical.read_operation(&canonical).unwrap();
    let view = node.canonical.read_view(&op.view_id).unwrap();
    let frozen = node
        .publication_intentional(&canonical, &op, &view)
        .unwrap();
    let mut prepared = store.read_operation(&bookmark.0).block_on().unwrap();
    let snapshot = store
        .read_operation(&prepared.parents[0])
        .block_on()
        .unwrap();
    prepared.parents = snapshot.parents;
    prepared.metadata.attributes.insert(
        INTENT_ATTRIBUTE.to_owned(),
        serde_json::to_string(&frozen.iter().map(CommitId::hex).collect::<Vec<_>>()).unwrap(),
    );
    prepared
        .metadata
        .attributes
        .extend(node.publication_namespace_facts(&canonical).unwrap());
    for id in frozen {
        prepared
            .commit_predecessors
            .get_or_insert_with(BTreeMap::new)
            .entry(id)
            .or_default();
    }
    let orphan = store.write_operation(&prepared).block_on().unwrap();
    node.canonicalize_unchecked(&LocalOp(orphan)).unwrap();
    assert!(
        plan.after.files.iter().any(|f| f.path == "junk"),
        "the unselected bookmark operation still retains the old working copy"
    );
    let CleanupEffect {
        images, checkpoint, ..
    } = node
        .apply_publication_cleanup_mapped(&selected, &plan.token, &mut cache)
        .unwrap();
    model.assert_applied(&mut open(&repo), &images, &checkpoint);
}

#[test]
fn attempted_publications_remain_unprunable_after_a_lost_reply_and_restart() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = start(&repo);
    node.initialize_publication_offers().unwrap();
    repo.write_file("junk", "possibly shared");
    repo.jj(&["status"]);
    let before = report(&mut node);
    let first = node.canonical_heads().unwrap()[0].clone();
    node.record_publication_offer(&first).unwrap();
    // The request can have reached the hub even if no pushed/accepted marker was saved.
    drop(node);
    fs::remove_file(repo.path().join("junk")).unwrap();
    repo.jj(&["status"]);
    let mut node = open(&repo);
    let selected: Vec<_> = before.operations.iter().map(|op| op.id.clone()).collect();
    let err = node
        .preview_publication_cleanup(&selected, &mut PublicationCache::default())
        .unwrap_err();
    assert!(err.to_string().contains("was offered"), "{err}");
    let latest = node.canonical_heads().unwrap()[0].clone();
    node.record_publication_offer(&latest).unwrap();
    let mut contraction =
        crate::canonical::Contraction::new(&node.canonical, [first.clone()]).unwrap();
    let compacted = contraction.images(&node.canonical, &latest).unwrap();
    assert_eq!(compacted.len(), 1);
    assert_eq!(
        node.canonical.original_id(&latest).unwrap(),
        node.canonical.original_id(&compacted[0]).unwrap()
    );
    node.record_publication_offer(&compacted[0]).unwrap();
    assert_eq!(
        node.read_publication_offers().unwrap().len(),
        2,
        "a contracted offer cannot subsume an older offer with more ancestors"
    );
    let origins = node.publication_offered_origins().unwrap();
    assert!(origins.contains(&node.canonical.original_id(&first).unwrap()));
    let path = repo.repo_path().join("musubi").join(OFFERS_FILE);
    let mut valid: serde_json::Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
    valid["heads"] = json!([]);
    fs::write(&path, serde_json::to_vec(&valid).unwrap()).unwrap();
    assert!(
        node.publication_offered_origins()
            .unwrap_err()
            .to_string()
            .contains("checksum")
    );
    fs::write(repo.repo_path().join("musubi").join(OFFERS_FILE), "[").unwrap();
    assert!(
        node.preview_publication_cleanup(&selected, &mut PublicationCache::default())
            .is_err(),
        "damaged provenance cannot silently become an empty frontier"
    );
}

#[test]
fn activating_tracking_cannot_declare_legacy_history_unpublished() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = start(&repo);
    repo.write_file("junk", "may already have been sent");
    repo.jj(&["status"]);
    let before = report(&mut node);
    let first = node.canonical_heads().unwrap()[0].clone();
    // A persisted push marker is exactly what an older copy leaves behind.
    fs::remove_file(repo.repo_path().join("musubi").join(OFFERS_FILE)).unwrap();
    fs::write(repo.repo_path().join("musubi/pushed"), first.0.hex()).unwrap();
    let selected: Vec<_> = before.operations.iter().map(|op| op.id.clone()).collect();
    assert!(
        node.preview_publication_cleanup(&selected, &mut PublicationCache::default())
            .unwrap_err()
            .to_string()
            .contains("predates publication tracking")
    );
}

#[cfg(unix)]
#[test]
fn symlink_targets_are_snapshot_content_too() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = start(&repo);
    std::os::unix::fs::symlink("a-long-accidental-target", repo.path().join("link")).unwrap();
    repo.jj(&["status"]);
    fs::remove_file(repo.path().join("link")).unwrap();
    repo.jj(&["status"]);
    let before = report(&mut node);
    assert_eq!(before.files.len(), 1);
    assert_eq!(before.bytes, "a-long-accidental-target".len() as u64);
    compare_model(&mut node, &[]);
}

#[test]
fn cleanup_preserves_private_slash_workspace_names_and_explicit_old_versions() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = start(&repo);
    let path = env.root().join("second");
    repo.jj(&[
        "workspace",
        "add",
        "--name",
        "feat/x",
        path.to_str().unwrap(),
    ]);
    repo.write_file("wanted", "version one");
    repo.jj(&["commit", "-m", "first"]);
    let first = commit_id(&repo, "@-");
    repo.jj(&["describe", "-r", "@-", "-m", "edited description"]);
    let second = commit_id(&repo, "@-");
    repo.write_file("junk", "unwanted");
    repo.jj(&["status"]);
    fs::remove_file(repo.path().join("junk")).unwrap();
    repo.jj(&["status"]);
    let before = report(&mut node);
    let selected: Vec<_> = before.operations.iter().map(|op| op.id.clone()).collect();
    let head = node.canonical_heads().unwrap()[0].clone();
    let old_view = node.canonical.read_operation_view(&head).unwrap();
    let mut cache = PublicationCache::default();
    let plan = node
        .preview_publication_cleanup(&selected, &mut cache)
        .unwrap();
    node.apply_publication_cleanup(&selected, &plan.token, &mut cache)
        .unwrap();
    let mut node = open(&repo);
    let head = node.canonical_heads().unwrap()[0].clone();
    assert_eq!(node.canonical.read_operation_view(&head).unwrap(), old_view);
    let (_, ops) = node.publication_pending().unwrap();
    let kept = node.publication_kept_versions(&ops).unwrap();
    assert!(kept.contains(&CommitId::try_from_hex(first.trim()).unwrap()));
    assert!(kept.contains(&CommitId::try_from_hex(second.trim()).unwrap()));
    let names = repo.jj(&[
        "--ignore-working-copy",
        "workspace",
        "list",
        "-T",
        "name ++ \"\\n\"",
    ]);
    assert!(names.lines().any(|name| name == "feat/x"), "{names}");
}

#[test]
fn raw_tree_walk_includes_directory_sides_of_file_directory_conflicts() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    repo.write_file("p", "file side");
    repo.jj(&["commit", "-m", "file"]);
    let file = commit_id(&repo, "@-");
    repo.jj(&["new", "root()"]);
    repo.write_file("p/inside", "directory side");
    repo.jj(&["commit", "-m", "directory"]);
    let dir = commit_id(&repo, "@-");
    repo.jj(&["new", file.trim(), dir.trim()]);
    let node = start(&repo);
    let current = CommitId::try_from_hex(commit_id(&repo, "@").trim()).unwrap();
    let files = node
        .publication_files([current], &Closure::default(), &Closure::default())
        .unwrap();
    assert!(
        files
            .iter()
            .any(|file| file.path.as_internal_file_string() == "p")
    );
    assert!(
        files
            .iter()
            .any(|file| file.path.as_internal_file_string() == "p/inside")
    );
}

#[test]
fn retained_intent_is_referenced_and_its_encoding_is_pinned() {
    let commit = CommitId::from_bytes(&[0xab; 20]);
    let mut op = Operation::make_root(jj_lib::op_store::ViewId::from_bytes(&[0; 64]));
    crate::op_attrs::OpAttrs(&mut op.metadata.attributes)
        .set_intent([&commit])
        .unwrap();
    assert_eq!(
        op.metadata.attributes[INTENT_ATTRIBUTE],
        r#"["abababababababababababababababababababab"]"#
    );
    assert!(retained_publication_intent(&op).is_err());
    op.commit_predecessors = Some(BTreeMap::from([(commit.clone(), vec![])]));
    assert_eq!(
        retained_publication_intent(&op).unwrap(),
        Some(BTreeSet::from([commit]))
    );
    for bad in ["[", "null", "[1]", r#"["not hex"]"#] {
        op.metadata
            .attributes
            .insert(INTENT_ATTRIBUTE.to_owned(), bad.to_owned());
        assert!(retained_publication_intent(&op).is_err(), "{bad}");
    }
}

#[test]
fn manual_unpublished_abandon_cannot_approve_snapshot_content() {
    let env = TestEnv::new();
    for order in 0..3 {
        let repo = env.init_repo(&format!("order{order}"));
        let mut node = start(&repo);
        repo.write_file("junk", "not intentional");
        repo.jj(&["status"]);
        let snapshot = repo.jj(&[
            "--ignore-working-copy",
            "op",
            "log",
            "--no-graph",
            "-n1",
            "-T",
            "id",
        ]);
        repo.jj(&["bookmark", "create", "unrelated", "-r", "root()"]);
        fs::remove_file(repo.path().join("junk")).unwrap();
        repo.jj(&["status"]);
        if order == 0 {
            assert_eq!(report(&mut node).files.len(), 1);
        }
        repo.jj(&["op", "abandon", snapshot.trim()]);
        if order != 2 {
            assert_eq!(report(&mut node).files.len(), 1);
        }
        // Include GC before the first inspection: original parent views need not exist.
        repo.jj(&["util", "gc", "--expire", "now"]);
        drop(node);
        let translation = repo.repo_path().join("musubi/translation");
        if translation.exists() {
            fs::remove_file(translation).unwrap();
        }
        let mut node = open(&repo);
        let after = report(&mut node);
        assert_eq!(after.files.len(), 1);
        assert_eq!(after.files[0].path, "junk");
        let selected: Vec<_> = after.operations.iter().map(|op| op.id.clone()).collect();
        let model = compare_model(&mut node, &selected);
        let mut cache = PublicationCache::default();
        let plan = node
            .preview_publication_cleanup(&selected, &mut cache)
            .unwrap();
        assert_eq!(plan.after.bytes, 0);
        let CleanupEffect {
            images, checkpoint, ..
        } = node
            .apply_publication_cleanup_mapped(&selected, &plan.token, &mut cache)
            .unwrap();
        model.assert_applied(&mut open(&repo), &images, &checkpoint);
    }
}

#[test]
fn unrecognized_command_records_require_approval_and_cannot_be_pruned() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = start(&repo);
    repo.write_file("provisional", "keep unknown intent conservative");
    repo.jj(&["status"]);
    let head = node.local_heads().unwrap()[0].clone();
    let native = node.repo_at(&head).unwrap();
    native
        .start_transaction()
        .commit("custom command selects existing history")
        .block_on()
        .unwrap();
    fs::remove_file(repo.path().join("provisional")).unwrap();
    repo.jj(&["status"]);
    let outgoing = report(&mut node);
    let selected: Vec<_> = outgoing.operations.iter().map(|op| op.id.clone()).collect();
    compare_model(&mut node, &[]);
    let error = node
        .preview_publication_cleanup(&selected, &mut PublicationCache::default())
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("did not record enough information"),
        "{error}"
    );
    assert!(approve_publication(&repo.repo_path(), &outgoing, &outgoing.token).unwrap());

    // A first join must not lose uncertainty hidden in its pre-join native ancestry.
    let repo = env.init_repo("bootstrap");
    repo.write_file("provisional", "unknown selected version");
    repo.jj(&["status"]);
    let node = open(&repo);
    let head = node.local_heads().unwrap()[0].clone();
    node.repo_at(&head)
        .unwrap()
        .start_transaction()
        .commit("custom command selects existing history")
        .block_on()
        .unwrap();
    let mut node = start(&repo);
    let outgoing = report(&mut node);
    assert!(!outgoing.cleanup_available);
    compare_model(&mut node, &[]);
}

#[test]
fn diffedit_protects_its_rewrite_without_approving_the_automatic_input_version() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = start(&repo);
    repo.write_file("selected", "automatic old contents");
    repo.jj(&["status"]);
    let old = commit_id(&repo, "@");
    repo.jj(&[
        "--config",
        r#"ui.diff-editor=['sh', '-c', 'printf edited > "$1/selected"', 'sh', '$right']"#,
        "diffedit",
    ]);
    let current = commit_id(&repo, "@");
    assert_ne!(current, old);
    let outgoing = report(&mut node);
    assert!(outgoing.cleanup_available);
    assert_eq!(outgoing.bytes, "automatic old contents".len() as u64);
    let selected: Vec<_> = outgoing.operations.iter().map(|op| op.id.clone()).collect();
    let model = compare_model(&mut node, &selected);
    let mut cache = PublicationCache::default();
    let plan = node
        .preview_publication_cleanup(&selected, &mut cache)
        .unwrap();
    assert!(plan.after.files.is_empty());
    let CleanupEffect {
        images, checkpoint, ..
    } = node
        .apply_publication_cleanup_mapped(&selected, &plan.token, &mut cache)
        .unwrap();
    assert_eq!(commit_id(&repo, "@"), current);
    model.assert_applied(&mut open(&repo), &images, &checkpoint);
}

#[test]
fn explicit_revision_selections_survive_without_original_parent_views() {
    let env = TestEnv::new();
    for command in ["edit", "new", "bookmark-create", "bookmark-set", "tag"] {
        let repo = env.init_repo(command);
        let mut node = start(&repo);
        repo.write_file("selected", "explicitly selected existing contents");
        repo.jj(&["status"]);
        let selected = commit_id(&repo, "@");
        repo.jj(&["new", "root()"]);
        match command {
            "edit" => {
                repo.jj(&["edit", selected.trim()]);
            }
            "new" => {
                repo.jj(&["new", selected.trim()]);
            }
            "bookmark-create" => {
                repo.jj(&["bookmark", "create", "chosen", "-r", selected.trim()]);
            }
            "bookmark-set" => {
                repo.jj(&["bookmark", "create", "chosen", "-r", "root()"]);
                repo.jj(&["bookmark", "set", "chosen", "-r", selected.trim()]);
            }
            "tag" => {
                repo.jj(&["tag", "set", "chosen", "-r", selected.trim()]);
            }
            _ => unreachable!(),
        }
        // The explicit target must come from this command's own record, not a diff
        // against its parent (which native operation contraction may replace).
        let source = node.local_heads().unwrap()[0].clone();
        let native = node.repo_at(&source).unwrap();
        let op = native.operation().store_operation();
        let (roots, known) = node
            .publication_command_intent(op, native.view().store_view())
            .unwrap();
        assert!(known, "{}", op.metadata.description);
        assert!(
            roots.contains(&CommitId::try_from_hex(selected.trim()).unwrap()),
            "{}",
            op.metadata.description
        );
        assert!(report(&mut node).files.is_empty(), "{command}");
        assert!(report(&mut node).cleanup_available, "{command}");
        compare_model(&mut node, &[]);
    }
}

#[test]
fn untracking_accidental_files_keeps_the_partial_commit_and_current_work() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = start(&repo);
    repo.write_file("README.txt", "keep this commit");
    repo.write_file("AGENTS.md", "keep current instructions");
    repo.write_file("junk/a", "unwanted history");
    repo.jj(&["status"]);
    repo.jj(&["commit", "README.txt", "-m", "Keep README"]);
    let readme = commit_id(&repo, "@-");
    repo.write_file(".gitignore", "junk/\n");
    repo.jj(&["file", "untrack", "junk"]);
    fs::remove_dir_all(repo.path().join("junk")).unwrap();
    repo.jj(&["status"]);
    let current = commit_id(&repo, "@");
    let outgoing = report(&mut node);
    assert!(outgoing.cleanup_available);
    assert_eq!(
        outgoing
            .files
            .iter()
            .map(|f| f.path.as_str())
            .collect::<Vec<_>>(),
        ["junk/a"]
    );
    let selected: Vec<_> = outgoing.operations.iter().map(|op| op.id.clone()).collect();
    let model = compare_model(&mut node, &selected);
    let mut cache = PublicationCache::default();
    let plan = node
        .preview_publication_cleanup(&selected, &mut cache)
        .unwrap();
    assert!(plan.after.files.is_empty());
    let CleanupEffect {
        images, checkpoint, ..
    } = node
        .apply_publication_cleanup_mapped(&selected, &plan.token, &mut cache)
        .unwrap();
    assert_eq!(commit_id(&repo, "@-"), readme);
    assert_eq!(commit_id(&repo, "@"), current);
    assert_eq!(
        fs::read_to_string(repo.path().join("AGENTS.md")).unwrap(),
        "keep current instructions"
    );
    model.assert_applied(&mut open(&repo), &images, &checkpoint);
}

#[test]
fn explicit_fetch_and_import_select_git_history_without_approving_snapshot_contents() {
    let env = TestEnv::new();
    let upstream = env.init_repo("upstream");
    upstream.write_file("upstream", "intentional remote content");
    upstream.jj(&["commit", "-m", "Remote change"]);
    upstream.jj(&["bookmark", "create", "main", "-r", "@-"]);
    let remote_commit = commit_id(&upstream, "@-");
    let fresh = env.init_repo("fresh-import");
    let mut fresh_node = start(&fresh);
    fresh.git(&["fetch", upstream.path().to_str().unwrap(), "main"]);
    fresh.git(&["update-ref", "refs/heads/imported", remote_commit.trim()]);
    fresh.jj(&["--no-pager", "git", "import"]);
    let fresh_report = report(&mut fresh_node);
    assert!(fresh_report.cleanup_available);
    assert!(fresh_report.files.is_empty());
    compare_model(&mut fresh_node, &[]);
    // A Git-only snapshot left by an interrupted export is newly indexed too. Fresh
    // import keys alone cannot prove intent: a read-only command grants no exemption.
    let automatic = env.init_repo("automatic-import");
    let mut automatic_node = start(&automatic);
    automatic.git(&["fetch", upstream.path().to_str().unwrap(), "main"]);
    automatic.git(&["update-ref", "refs/heads/imported", remote_commit.trim()]);
    automatic.jj(&["status"]);
    let automatic_report = report(&mut automatic_node);
    assert!(!automatic_report.cleanup_available);
    assert_eq!(
        automatic_report
            .files
            .iter()
            .map(|f| f.path.as_str())
            .collect::<Vec<_>>(),
        ["upstream"]
    );
    compare_model(&mut automatic_node, &[]);
    let repo = env.init_repo("alpha");
    let mut node = start(&repo);
    repo.write_file("junk", "only a snapshot");
    repo.jj(&["status"]);
    fs::remove_file(repo.path().join("junk")).unwrap();
    repo.jj(&["status"]);
    repo.jj(&[
        "git",
        "remote",
        "add",
        "origin",
        upstream.path().to_str().unwrap(),
    ]);
    repo.jj(&["git", "fetch"]);
    let fetched = report(&mut node);
    assert!(fetched.cleanup_available);
    assert_eq!(
        fetched
            .files
            .iter()
            .map(|f| f.path.as_str())
            .collect::<Vec<_>>(),
        ["junk"]
    );
    compare_model(&mut node, &[]);
    repo.git(&["update-ref", "refs/heads/imported", remote_commit.trim()]);
    repo.jj(&[
        "--no-pager",
        "--ignore-working-copy",
        "-R",
        repo.path().to_str().unwrap(),
        "git",
        "import",
    ]);
    let imported = report(&mut node);
    assert!(!imported.cleanup_available);
    assert_eq!(imported.content, fetched.content);
    compare_model(&mut node, &[]);

    // An unrelated import must not approve an automatically moved local bookmark.
    repo.jj(&["bookmark", "create", "work", "-r", "@"]);
    repo.write_file("selected-existing", "still an automatic version");
    repo.jj(&["status"]);
    let existing = commit_id(&repo, "@");
    let old_snapshot = node.local_heads().unwrap()[0].0.hex();
    repo.git(&[
        "update-ref",
        "refs/heads/unrelated-import",
        remote_commit.trim(),
    ]);
    repo.jj(&["git", "import"]);
    assert!(
        report(&mut node)
            .files
            .iter()
            .any(|file| file.path == "selected-existing")
    );
    fs::remove_file(repo.path().join("selected-existing")).unwrap();
    repo.jj(&["status"]);
    repo.git(&["update-ref", "refs/heads/existing", existing.trim()]);
    repo.jj(&["--config", "ui.color=never", "--no-pager", "git", "import"]);
    repo.jj(&["bookmark", "forget", "existing", "work", "unrelated-import"]);
    let outgoing = report(&mut node);
    assert!(!outgoing.cleanup_available);
    assert!(
        outgoing
            .files
            .iter()
            .any(|file| file.path == "selected-existing")
    );
    let mut selected: Vec<_> = outgoing.operations.iter().map(|op| op.id.clone()).collect();
    selected.push(old_snapshot);
    assert!(
        node.preview_publication_cleanup(&selected, &mut PublicationCache::default())
            .unwrap_err()
            .to_string()
            .contains("did not record enough information")
    );
    compare_model(&mut node, &[]);
}

#[test]
fn retrying_an_automatic_git_export_does_not_approve_snapshot_contents() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = start(&repo);
    repo.jj(&["bookmark", "create", "work", "-r", "@"]);
    let lock = repo.path().join(".git/refs/heads/work.lock");
    fs::create_dir_all(lock.parent().unwrap()).unwrap();
    fs::write(&lock, "locked").unwrap();
    repo.write_file("junk", "automatic snapshot, even with a bookmark");
    repo.jj(&["status"]);
    assert_eq!(report(&mut node).files.len(), 1);
    fs::remove_file(lock).unwrap();
    repo.jj(&["status"]);
    let outgoing = report(&mut node);
    assert_eq!(outgoing.files.len(), 1);
    assert!(!outgoing.cleanup_available);
    let (_, ops) = node.publication_pending().unwrap();
    assert!(ops.iter().any(|id| {
        node.canonical
            .read_operation(id)
            .unwrap()
            .metadata
            .description
            == "export git refs"
    }));
    compare_model(&mut node, &[]);
}

#[test]
fn automatic_git_import_rebases_do_not_approve_snapshot_contents() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = start(&repo);
    repo.write_file("file", "first");
    repo.jj(&["commit", "-m", "First"]);
    let first = commit_id(&repo, "@-");
    repo.write_file("file", "second");
    repo.jj(&["bookmark", "create", "master", "-r", "@"]);
    repo.jj(&["commit", "-m", "Second"]);
    repo.jj(&["status"]);
    repo.write_file("junk", "automatic working-copy contents");
    repo.jj(&["status"]);
    assert_eq!(report(&mut node).files.len(), 1);
    repo.git(&["update-ref", "refs/heads/master", first.trim()]);
    let before = commit_id(&repo, "@");
    repo.jj(&["status"]);
    assert_ne!(commit_id(&repo, "@"), before);
    let outgoing = report(&mut node);
    assert_eq!(outgoing.files.len(), 1);
    assert_eq!(outgoing.files[0].path, "junk");
    assert_eq!(
        outgoing.bytes,
        "automatic working-copy contents".len() as u64
    );
    assert!(!outgoing.cleanup_available);
    compare_model(&mut node, &[]);
}
