//! The format guard accepts everything jj-lib writes, and rejects anything with a field it
//! does not know.

#![allow(clippy::unwrap_used)]

use std::collections::HashSet;

use hegel::Generator as _;
use hegel::PrintableGenerator;
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

// Each generator below is a composite, or built from generators, so that a failing case prints
// the view or operation once as a value, not the hundreds of draws that made it.

/// `len` arbitrary bytes, as one draw.
fn bytes(len: usize) -> impl PrintableGenerator<Vec<u8>> {
    gs::binary().min_size(len).max_size(len)
}

/// One of five names with the prefix, so that keys of different maps collide.
fn name(prefix: &'static str) -> impl PrintableGenerator<String> {
    gs::integers::<usize>()
        .max_value(4)
        .map(move |n| format!("{prefix}{n}"))
}

fn commit_id() -> impl PrintableGenerator<CommitId> {
    bytes(20).map(CommitId::new)
}

/// A conflict of one, three or five terms, any of them absent.
#[hegel::composite]
fn ref_target(tc: &TestCase) -> RefTarget {
    let terms = 1 + 2 * tc.draw(gs::integers::<usize>().max_value(2));
    let terms = tc.draw(
        gs::vecs(gs::optional(commit_id()))
            .min_size(terms)
            .max_size(terms),
    );
    Merge::from_vec(terms)
}

#[hegel::composite]
fn remote_ref(tc: &TestCase) -> RemoteRef {
    // Tracked, the shrink target, is the ordinary state: jj tracks every tag and `@git` bookmark.
    let state = if tc.draw(gs::booleans()) {
        RemoteRefState::New
    } else {
        RemoteRefState::Tracked
    };
    RemoteRef {
        target: tc.draw(ref_target()),
        state,
    }
}

#[hegel::composite]
fn remote_view(tc: &TestCase) -> RemoteView {
    let refs = || gs::btree_maps(name("b").map(Into::into), remote_ref()).max_size(3);
    RemoteView {
        bookmarks: tc.draw(refs()),
        tags: tc.draw(refs()),
    }
}

#[hegel::composite]
fn view(tc: &TestCase) -> View {
    let targets = || gs::btree_maps(name("b").map(Into::into), ref_target()).max_size(3);
    let heads = tc.draw(gs::vecs(commit_id()).max_size(3));
    View {
        head_ids: heads.into_iter().collect::<HashSet<_>>(),
        local_bookmarks: tc.draw(targets()),
        local_tags: tc.draw(gs::btree_maps(name("t").map(Into::into), ref_target()).max_size(3)),
        remote_views: tc.draw(
            gs::btree_maps(
                gs::sampled_from(vec!["origin", "git", "upstream"]).map(Into::into),
                remote_view(),
            )
            .max_size(2),
        ),
        git_refs: tc.draw(
            gs::btree_maps(
                name("b").map(|name| format!("refs/heads/{name}").into()),
                ref_target(),
            )
            .max_size(3),
        ),
        git_heads: tc.draw(gs::btree_maps(name("ws").map(Into::into), ref_target()).max_size(3)),
        wc_commit_ids: tc.draw(gs::btree_maps(name("ws").map(Into::into), commit_id()).max_size(2)),
    }
}

#[hegel::composite]
fn timestamp(tc: &TestCase) -> Timestamp {
    Timestamp {
        timestamp: MillisSinceEpoch(tc.draw(gs::integers::<i64>())),
        tz_offset: tc.draw(gs::integers::<i32>().min_value(-720).max_value(840)),
    }
}

#[hegel::composite]
fn operation(tc: &TestCase) -> Operation {
    let predecessors = tc.draw(gs::optional(
        gs::btree_maps(commit_id(), gs::vecs(commit_id()).max_size(2)).max_size(3),
    ));
    Operation {
        view_id: ViewId::new(tc.draw(bytes(64))),
        parents: tc
            .draw(gs::vecs(bytes(64)).min_size(1).max_size(3))
            .into_iter()
            .map(OperationId::new)
            .collect(),
        metadata: OperationMetadata {
            time: TimestampRange {
                start: tc.draw(timestamp()),
                end: tc.draw(timestamp()),
            },
            description: tc.draw(gs::text()),
            hostname: tc.draw(gs::text()),
            username: tc.draw(gs::text()),
            is_snapshot: tc.draw(gs::booleans()),
            workspace_name: tc.draw(gs::optional(name("ws").map(Into::into))),
            attributes: tc.draw(gs::btree_maps(name("k"), gs::text()).max_size(2)),
        },
        commit_predecessors: predecessors,
    }
}

fn store() -> (tempfile::TempDir, SimpleOpStore) {
    let dir = musubi_testutil::tempdir();
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
    let view = tc.draw(view());
    let id = store.write_view(&view).block_on().unwrap();
    let encoded = std::fs::read(dir.path().join("views").join(id.hex())).unwrap();
    assert_eq!(format_guard::check_view(&encoded), Ok(()));
    assert!(format_guard::check_view(&with_unknown_field(encoded)).is_err());
}

#[hegel::test(test_cases = 200)]
fn guard_accepts_jj_operations_and_rejects_unknown_fields(tc: TestCase) {
    let (dir, store) = store();
    let operation = tc.draw(operation());
    let id = store.write_operation(&operation).block_on().unwrap();
    let encoded = std::fs::read(dir.path().join("operations").join(id.hex())).unwrap();
    assert_eq!(format_guard::check_operation(&encoded), Ok(()));
    assert!(format_guard::check_operation(&with_unknown_field(encoded)).is_err());
}
