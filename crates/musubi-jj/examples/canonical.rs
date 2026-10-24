//! How the canonical store keeps up with a long operation log: builds a store of OPS
//! operations, each a snapshot of a working copy in a busy repository (400 heads and 200
//! bookmarks, one head replaced each time), then times what a hub and a joining machine do
//! with it. See "The canonical store" in bench/README.md.
//!
//! Usage: `cargo run --release -p musubi-jj --example canonical -- DIR OPS [--import-only]`
//!
//! A store DIR holds already, built to the end, is used as it is, whatever OPS says.
//! `--import-only` times only the import, of the bundle an earlier run left in DIR, for
//! profiling it.

use std::collections::BTreeMap;
use std::error::Error;
use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::Operation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::RefTarget;
use jj_lib::op_store::View;
use musubi_jj::canonical::CanonicalStore;

fn commit(i: u64) -> CommitId {
    let mut bytes = [0u8; 20];
    bytes[..8].copy_from_slice(&i.to_le_bytes());
    bytes[19] = 1;
    CommitId::from_bytes(&bytes)
}

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (dir, ops, import_only) = match args.as_slice() {
        [dir, ops] => (dir, ops, false),
        [dir, ops, flag] if flag == "--import-only" => (dir, ops, true),
        _ => return Err("usage: canonical DIR OPS [--import-only]".into()),
    };
    let dir = PathBuf::from(dir);
    let ops: u64 = ops.parse()?;
    let root_commit = CommitId::from_bytes(&[0; 20]);
    let head_file = dir.join("bench-head");
    let bundle = dir.join("bench-bundle");
    let receiver_dir = dir.join("bench-receiver");

    if import_only {
        fs::remove_dir_all(&receiver_dir).ok();
        let receiver = CanonicalStore::open(&receiver_dir, root_commit)?;
        let t = Instant::now();
        receiver.import_operations(&bundle)?;
        println!("import: {:?}", t.elapsed());
        return Ok(());
    }

    // A build cut short leaves no head, and is built again over what it wrote.
    let build = !head_file.exists();
    let t = Instant::now();
    let store = CanonicalStore::open(&dir, root_commit.clone())?;
    println!("open: {:?}", t.elapsed());
    if build {
        let mut view = View::make_root(root_commit.clone());
        view.head_ids = (0..400).map(commit).collect();
        view.local_bookmarks = (0..200)
            .map(|i| {
                (
                    format!("bookmark-{i}").into(),
                    RefTarget::normal(commit(1000 + i)),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let mut parent = store.root_operation_id().clone();
        let t = Instant::now();
        for (i, at) in (0..ops).zip(1_700_000_000_000_i64..) {
            view.head_ids.remove(&commit(i));
            view.head_ids.insert(commit(400 + i));
            view.wc_commit_ids.insert("default".into(), commit(400 + i));
            let view_id = store.write_view(&view)?;
            let mut op = Operation::make_root(view_id);
            op.parents = vec![parent];
            op.metadata.description = format!("snapshot working copy {i}");
            op.metadata.hostname = "machine".into();
            op.metadata.username = "agent".into();
            op.metadata.time.start.timestamp.0 = at;
            op.metadata.time.end.timestamp.0 = at + 100;
            parent = store.write_operation(&op)?;
        }
        // Whole or not at all, so that a build cut short while writing it is built again.
        let partial = dir.join("bench-head.partial");
        fs::write(&partial, parent.hex())?;
        fs::rename(&partial, &head_file)?;
        println!("build {ops}: {:?}", t.elapsed());
        let view_id = store.read_operation(&parent)?.view_id;
        println!("one view: {} bytes", store.view_bytes(&view_id)?.len());
    }
    println!("log: {} bytes", fs::metadata(dir.join("log"))?.len());
    let head = OperationId::try_from_hex(fs::read_to_string(&head_file)?.trim())
        .ok_or("bench-head isn't an operation id")?;

    // What a hub does on opening a store: walks every operation's parents.
    let t = Instant::now();
    let mut walked = 0;
    let mut at = head.clone();
    while at != *store.root_operation_id() {
        at = store.parents(&at)?[0].clone();
        walked += 1;
    }
    println!("walk {walked} operations: {:?}", t.elapsed());

    // What a join does: exports every operation, works out which commits they need, and
    // imports them into an empty store.
    let all = store.ancestors_until(&[head], |_| false)?;
    let t = Instant::now();
    store.export_operations(&all, &bundle)?;
    println!(
        "export {}: {:?}, {} bytes",
        all.len(),
        t.elapsed(),
        fs::metadata(&bundle)?.len()
    );
    let t = Instant::now();
    let commits = store.required_commits(&all)?;
    println!("required commits ({}): {:?}", commits.len(), t.elapsed());
    fs::remove_dir_all(&receiver_dir).ok();
    let receiver = CanonicalStore::open(&receiver_dir, root_commit)?;
    let t = Instant::now();
    receiver.import_operations(&bundle)?;
    println!("import: {:?}", t.elapsed());
    Ok(())
}
