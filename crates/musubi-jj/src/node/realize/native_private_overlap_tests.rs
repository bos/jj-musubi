//! A cached non-root target's old private name must overlap the current owned namespace
//! before it can borrow current Git fields. Root fallback would hide this rejecting case.

use super::*;

#[test]
fn disjoint_owned_names_do_not_select_current_git() {
    for lose_cache in [false, true] {
        let mut fx = Fixture::new();
        fx.repo.jj(&["workspace", "forget", "b"]);
        fx.repo.jj(&["workspace", "rename", "b"]);
        let parent = fx.node.advance(&fx.incoming).unwrap();
        let (_, parent_view) = raw(&fx.node, &parent);
        let binding = parent_view.wc_commit_ids[WorkspaceName::new("b")].clone();
        let mut foreign = parent_view.wc_commit_ids.clone();
        foreign.remove(WorkspaceName::new("b"));
        assert_eq!(
            foreign.keys().map(|name| name.as_str()).collect::<Vec<_>>(),
            ["alpha/a"],
            "the fixture has one independently owned foreign slot"
        );
        let inherited = PerMachine::of(&parent_view);
        let child = fx.node.realize(&fx.child).unwrap();
        let (cached_op, cached_view) = raw(&fx.node, &child);
        assert_eq!(cached_op.parents, [parent.0.clone()]);
        assert_eq!(cached_view.wc_commit_ids, parent_view.wc_commit_ids);
        assert_eq!(PerMachine::of(&cached_view), inherited);
        assert_eq!(
            fx.node.canonical.parents(&fx.child).unwrap(),
            [fx.incoming.clone()]
        );
        let presence = fx.node.presence(&fx.child).unwrap();
        assert!(presence.known().contains(fx.node.machine().key()));
        assert!(!presence.is_present(fx.node.machine().key()));
        drop(presence);

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
        let added = fx.node.local_heads().unwrap();
        assert_eq!(added.len(), 1);
        let (_, added_view) = raw(&fx.node, &added[0]);
        let added_binding = added_view.wc_commit_ids[WorkspaceName::new("a")].clone();
        let mut expected = foreign;
        expected.insert("a".into(), added_binding);
        expected.insert("b".into(), binding.clone());
        assert_eq!(added_view.wc_commit_ids, expected);

        // These are actual native edits to the current namespace and Git, after caching
        // the child's target {b}. They finish before advance's capture and locks (E1/E2).
        fx.repo.jj(&["workspace", "rename", "c"]);
        fx.repo
            .jj(&["--ignore-working-copy", "bookmark", "set", "x", "-r", "a@"]);
        fx.repo.jj(&["--ignore-working-copy", "git", "export"]);
        expected.remove(WorkspaceName::new("b"));
        expected.insert("c".into(), binding);
        let heads = fx.node.local_heads().unwrap();
        assert_eq!(heads.len(), 1);
        let (_, current) = raw(&fx.node, &heads[0]);
        assert_eq!(current.wc_commit_ids, expected);
        assert!(current.wc_commit_ids.contains_key(WorkspaceName::new("a")));
        assert!(current.wc_commit_ids.contains_key(WorkspaceName::new("c")));
        assert!(!current.wc_commit_ids.contains_key(WorkspaceName::new("b")));
        assert_ne!(PerMachine::of(&current), inherited);
        let x = jj_lib::ref_name::GitRefName::new("refs/heads/x");
        assert_ne!(current.git_refs.get(x), parent_view.git_refs.get(x));
        let physical_x = gix::open(fx.repo.path())
            .unwrap()
            .find_reference("refs/heads/x")
            .unwrap()
            .target()
            .try_id()
            .unwrap()
            .to_string();
        assert_eq!(current.git_refs[x].as_normal().unwrap().hex(), physical_x);

        assert!(
            fx.node.native_receipt().is_none(),
            "root-base fallback is off"
        );
        if lose_cache {
            let before = capture(&fx.node);
            // This fixture has no retained conflicted-export observations to lose. A
            // general warm/cold equality law would also need authenticated U and equal I.
            assert!(before.expected.is_empty());
            drop(fx.node);
            fs::remove_file(fx.repo.repo_path().join("musubi/translation")).unwrap();
            fx.node = open(&fx.repo);
            let after = capture(&fx.node);
            assert_eq!(after.heads, before.heads);
            assert_eq!(after.native, before.native);
            assert_eq!(after.canonical, before.canonical);
            assert_eq!(after.receipt, before.receipt);
            assert_eq!(after.expected, before.expected);
        }

        let loader = fx.node.loader.clone();
        let events = Arc::new(Mutex::new(vec![]));
        let seen = events.clone();
        let exports = Arc::new(Mutex::new(vec![]));
        let observed = exports.clone();
        let _observe = Observe::new(move |event| {
            if let Event::Export(id) = &event {
                let op = loader.op_store().read_operation(&id.0).block_on().unwrap();
                let view = loader.op_store().read_view(&op.view_id).block_on().unwrap();
                observed.lock().unwrap().push((op, view));
            }
            seen.lock().unwrap().push(event);
        });
        fx.node.advance(&fx.child).unwrap();
        let exports = exports.lock().unwrap();
        let (first, view) = exports.first().expect("reach the actual first export");
        // The expected ordered input is the captured, published parent, not the result's
        // chosen source. A known-forgotten-only selector instead merges before this export
        // and/or carries the independently different current Git fields into the child.
        assert_eq!(
            first.parents,
            [parent.0],
            "cached child exports before the merge"
        );
        assert_eq!(
            PerMachine::of(view),
            inherited,
            "disjoint names cannot carry current Git"
        );
        assert_eq!(view.wc_commit_ids, cached_view.wc_commit_ids);
        let events = events.lock().unwrap();
        assert!(events.iter().any(|event| matches!(event,
            Event::Sources(actual) if actual == &heads)));
        assert!(events.iter().any(|event| matches!(event,
            Event::Reread { captured, actual } if captured == &heads && actual == &heads)));
        assert!(!events.iter().any(|event| matches!(event,
            Event::CurrentGit { canonical, .. } if canonical == &fx.child)));
        assert!(matches!(events.last(), Some(Event::Complete)));
        // Each trace checks its declared native inputs. There is no cross-run local-ID
        // equality assertion or claim that raw marker domains authenticate arbitrary U.
    }
}
