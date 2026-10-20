//! The format guard accepts everything jj-lib writes, and rejects anything with a field it
//! does not know.

#![allow(clippy::unwrap_used)]

use std::collections::BTreeMap;
use std::collections::HashSet;

use hegel::TestCase;
use hegel::generators as gs;
use jj_lib::backend::CommitId;
use jj_lib::backend::MillisSinceEpoch;
use jj_lib::backend::Timestamp;
use jj_lib::merge::Merge;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OpStore as _;
use jj_lib::op_store::Operation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::OperationMetadata;
use jj_lib::op_store::RefTarget;
use jj_lib::op_store::RemoteRef;
use jj_lib::op_store::RemoteRefState;
use jj_lib::op_store::RemoteView;
use jj_lib::op_store::RootOperationData;
use jj_lib::op_store::TimestampRange;
use jj_lib::op_store::View;
use jj_lib::op_store::ViewId;
use jj_lib::simple_op_store::SimpleOpStore;
use musubi_jj::format_guard;
use pollster::FutureExt as _;

fn bytes(tc: &TestCase, len: usize) -> Vec<u8> {
    (0..len).map(|_| tc.draw(gs::integers::<u8>())).collect()
}

fn small(tc: &TestCase, max: usize) -> usize {
    tc.draw(gs::integers::<usize>().max_value(max))
}

fn name(tc: &TestCase, prefix: &str) -> String {
    format!("{prefix}{}", small(tc, 4))
}

fn commit_id(tc: &TestCase) -> CommitId {
    CommitId::new(bytes(tc, 20))
}

fn ref_target(tc: &TestCase) -> RefTarget {
    let terms = 1 + 2 * small(tc, 2);
    Merge::from_vec(
        (0..terms)
            .map(|_| tc.draw(gs::booleans()).then(|| commit_id(tc)))
            .collect::<Vec<_>>(),
    )
}

fn targets<K: Ord>(tc: &TestCase, key: impl Fn(&TestCase) -> K) -> BTreeMap<K, RefTarget> {
    (0..small(tc, 3))
        .map(|_| (key(tc), ref_target(tc)))
        .collect()
}

fn remote_refs(tc: &TestCase) -> BTreeMap<jj_lib::ref_name::RefNameBuf, RemoteRef> {
    (0..small(tc, 3))
        .map(|_| {
            let state = if tc.draw(gs::booleans()) {
                RemoteRefState::Tracked
            } else {
                RemoteRefState::New
            };
            let target = ref_target(tc);
            (name(tc, "b").into(), RemoteRef { target, state })
        })
        .collect()
}

fn view(tc: &TestCase) -> View {
    View {
        head_ids: (0..small(tc, 3))
            .map(|_| commit_id(tc))
            .collect::<HashSet<_>>(),
        local_bookmarks: targets(tc, |tc| name(tc, "b").into()),
        local_tags: targets(tc, |tc| name(tc, "t").into()),
        remote_views: (0..small(tc, 2))
            .map(|_| {
                let remote = ["origin", "git", "upstream"][small(tc, 2)];
                let remote_view = RemoteView {
                    bookmarks: remote_refs(tc),
                    tags: remote_refs(tc),
                };
                (remote.into(), remote_view)
            })
            .collect(),
        git_refs: targets(tc, |tc| format!("refs/heads/{}", name(tc, "b")).into()),
        git_heads: targets(tc, |tc| name(tc, "ws").into()),
        wc_commit_ids: (0..small(tc, 2))
            .map(|_| (name(tc, "ws").into(), commit_id(tc)))
            .collect(),
    }
}

fn timestamp(tc: &TestCase) -> Timestamp {
    Timestamp {
        timestamp: MillisSinceEpoch(tc.draw(gs::integers::<i64>())),
        tz_offset: tc.draw(gs::integers::<i32>().min_value(-720).max_value(840)),
    }
}

fn operation(tc: &TestCase) -> Operation {
    let predecessors = tc.draw(gs::booleans()).then(|| {
        (0..small(tc, 3))
            .map(|_| {
                (
                    commit_id(tc),
                    (0..small(tc, 2)).map(|_| commit_id(tc)).collect(),
                )
            })
            .collect()
    });
    Operation {
        view_id: ViewId::new(bytes(tc, 64)),
        parents: (0..1 + small(tc, 2))
            .map(|_| OperationId::new(bytes(tc, 64)))
            .collect(),
        metadata: OperationMetadata {
            time: TimestampRange {
                start: timestamp(tc),
                end: timestamp(tc),
            },
            description: tc.draw(gs::text()),
            hostname: tc.draw(gs::text()),
            username: tc.draw(gs::text()),
            is_snapshot: tc.draw(gs::booleans()),
            workspace_name: tc.draw(gs::booleans()).then(|| name(tc, "ws").into()),
            attributes: (0..small(tc, 2))
                .map(|_| (name(tc, "k"), tc.draw(gs::text())))
                .collect(),
        },
        commit_predecessors: predecessors,
    }
}

fn store() -> (tempfile::TempDir, SimpleOpStore) {
    let dir = tempfile::tempdir().unwrap();
    let root_commit_id = CommitId::new(vec![0; 20]);
    let store = SimpleOpStore::init(dir.path(), RootOperationData { root_commit_id }).unwrap();
    (dir, store)
}

/// Appends a field numbered beyond anything in the schema: a length-delimited field 99.
fn with_unknown_field(mut encoded: Vec<u8>) -> Vec<u8> {
    encoded.extend_from_slice(&[0x9a, 0x06, 0x01, 0x00]);
    encoded
}

#[hegel::test(test_cases = 200)]
fn guard_accepts_jj_views_and_rejects_unknown_fields(tc: TestCase) {
    let (dir, store) = store();
    let id = store.write_view(&view(&tc)).block_on().unwrap();
    let encoded = std::fs::read(dir.path().join("views").join(id.hex())).unwrap();
    assert_eq!(format_guard::check_view(&encoded), Ok(()));
    assert!(format_guard::check_view(&with_unknown_field(encoded)).is_err());
}

#[hegel::test(test_cases = 200)]
fn guard_accepts_jj_operations_and_rejects_unknown_fields(tc: TestCase) {
    let (dir, store) = store();
    let id = store.write_operation(&operation(&tc)).block_on().unwrap();
    let encoded = std::fs::read(dir.path().join("operations").join(id.hex())).unwrap();
    assert_eq!(format_guard::check_operation(&encoded), Ok(()));
    assert!(format_guard::check_operation(&with_unknown_field(encoded)).is_err());
}
