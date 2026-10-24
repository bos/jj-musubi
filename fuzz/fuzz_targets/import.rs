//! Bundles of operations and views imported into a canonical store, as a peer could make
//! them (`musubi_jj::canonical::CanonicalStore::import_operations`): each view of a small
//! history in one of three encodings that decode to it, or in bytes of the fuzzer's, whole
//! or as a delta against any encoding of any view before it, some sent twice, some with a
//! byte changed, most followed by their operation, compressed or not. Whatever the import
//! makes of a bundle, refusing it or not, the store holds nothing that isn't what its id
//! says, in normal form; and it takes a bundle as musubi makes one whole, storing each
//! operation and view as sent. The fuzzer's first input, of no bytes, is such a bundle. A
//! panic in jj-lib or jj-core, which panic on some malformed input, counts as a refusal, as
//! it does on the hub.

#![no_main]

use std::fs;
use std::sync::OnceLock;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::Operation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::View;
use jj_lib::op_store::ViewId;
use jj_lib::protos::simple_op_store as proto;
use libfuzzer_sys::fuzz_target;
use musubi_fuzz::refusing_jj_lib_panics;
use musubi_fuzz::scratch;
use musubi_jj::canonical::CanonicalStore;
use musubi_jj::objects::bundle;
use musubi_jj::objects::bundle::BundleWriter;
use prost::Message as _;

/// How many operations, each with a view of its own, the history has.
const LENGTH: usize = 6;

/// The sender's history: each view's id and bytes, and each operation's.
struct History {
    views: Vec<(ViewId, Vec<u8>)>,
    ops: Vec<(OperationId, Vec<u8>)>,
}

fn root_commit() -> CommitId {
    CommitId::from_bytes(&[0; 20])
}

fn history() -> &'static History {
    static HISTORY: OnceLock<History> = OnceLock::new();
    HISTORY.get_or_init(|| {
        let dir = scratch().join("import-sender");
        fs::remove_dir_all(&dir).ok();
        let store = CanonicalStore::open(&dir, root_commit()).unwrap();
        let mut parent = store.root_operation_id().clone();
        let (mut views, mut ops) = (vec![], vec![]);
        for i in 0..LENGTH as u8 {
            let mut view = View::make_root(root_commit());
            view.head_ids = (1 + i..8 + 2 * i)
                .map(|b| CommitId::from_bytes(&[b; 20]))
                .collect();
            let view_id = store.write_view(&view).unwrap();
            let mut op = Operation::make_root(view_id.clone());
            op.parents = vec![parent];
            op.metadata.description = format!("operation {i}");
            let op_id = store.write_operation(&op).unwrap();
            views.push((view_id.clone(), store.view_bytes(&view_id).unwrap()));
            ops.push((op_id.clone(), store.operation_bytes(&op_id).unwrap()));
            parent = op_id;
        }
        History { views, ops }
    })
}

/// The fuzzer's bytes, taken a few at a time; zeros once they run out.
struct Input<'a>(&'a [u8]);

impl<'a> Input<'a> {
    fn byte(&mut self) -> u8 {
        let Some((&first, rest)) = self.0.split_first() else {
            return 0;
        };
        self.0 = rest;
        first
    }

    fn bytes(&mut self) -> &'a [u8] {
        let len = usize::from(self.byte()).min(self.0.len());
        let (taken, rest) = self.0.split_at(len);
        self.0 = rest;
        taken
    }
}

/// An encoding of the view whose sender's bytes are `normal`: those; its heads reversed; or
/// with a field jj's schema doesn't have after them, which is still in normal form.
fn encode(normal: &[u8], how: u8) -> Vec<u8> {
    match how % 3 {
        0 => normal.to_vec(),
        1 => {
            let mut view = proto::View::decode(normal).unwrap();
            view.head_ids.reverse();
            view.encode_to_vec()
        }
        _ => [normal, &[0x9a, 0x06, 0x01, 0x00]].concat(),
    }
}

fuzz_target!(|data: &[u8]| {
    let history = history();
    let mut input = Input(data);
    let path = scratch().join("import-bundle");
    let mut writer = BundleWriter::create(&path).unwrap();
    // Whether the bundle is one musubi could have made: compressed, the sender's bytes, each
    // view as a delta against the one before, every operation, nothing changed. Zeros make
    // one.
    let compressed = input.byte() & 1 == 0;
    if compressed {
        writer.begin_compressed().unwrap();
    }
    let mut honest = compressed;
    for i in 0..LENGTH {
        let (view_id, normal) = &history.views[i];
        let control = input.byte();
        for _ in 0..=(control & 1) {
            let how = input.byte() % 4;
            let mut contents = match how {
                3 => input.bytes().to_vec(),
                _ => encode(normal, how),
            };
            let against = match (i, input.byte() % 3) {
                (0, _) | (_, 1) => None,
                (_, 0) => Some(i - 1),
                (_, _) => Some(usize::from(input.byte()) % i),
            };
            let change = input.byte();
            let base_how = input.byte();
            honest &= control & 1 == 0
                && how == 0
                && against == i.checked_sub(1)
                && (against.is_none() || base_how % 3 == 0)
                && change < 0x80;
            match against {
                Some(at) => {
                    let (base_id, base_normal) = &history.views[at];
                    let mut delta =
                        bundle::view_delta(&encode(base_normal, base_how), &contents).unwrap();
                    if change >= 0x80 && !delta.is_empty() {
                        let at = usize::from(input.byte()) % delta.len();
                        delta[at] ^= change;
                    }
                    writer
                        .view_delta_made(view_id.as_bytes(), base_id.as_bytes(), &delta)
                        .unwrap();
                }
                None => {
                    if change >= 0x80 && !contents.is_empty() {
                        let at = usize::from(input.byte()) % contents.len();
                        contents[at] ^= change;
                    }
                    writer.view(view_id.as_bytes(), &contents).unwrap();
                }
            }
        }
        if control & 0x30 != 0x30 {
            let (op_id, op) = &history.ops[i];
            writer.operation(op_id.as_bytes(), op).unwrap();
        } else {
            honest = false;
        }
    }
    writer.finish().unwrap();

    let dir = scratch().join("import-receiver");
    fs::remove_dir_all(&dir).ok();
    let receiver = CanonicalStore::open(&dir, root_commit()).unwrap();
    let imported = refusing_jj_lib_panics(|| receiver.import_operations(&path));
    if honest {
        assert!(matches!(imported, Some(Ok(_))), "{imported:?}");
    }
    drop(receiver);
    let reopened = CanonicalStore::open(&dir, root_commit()).unwrap();
    assert_eq!(reopened.torn().unwrap(), Vec::<String>::new());
    if honest {
        for ((view_id, view), (op_id, op)) in history.views.iter().zip(&history.ops) {
            assert_eq!(&reopened.view_bytes(view_id).unwrap(), view);
            assert_eq!(&reopened.operation_bytes(op_id).unwrap(), op);
        }
    }
});
