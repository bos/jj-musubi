//! Operations and views received from peers (`musubi_jj::canonical`): importing one never
//! panics, but in jj-lib, which the hub allows, opening its store again
//! (`musubi_sync::server`); one admitted reads back as what it hashes to; and none, admitted
//! or not, leaves the store torn.

#![no_main]

use std::cell::RefCell;
use std::fs;
use std::panic;
use std::panic::AssertUnwindSafe;
use std::sync::Once;

use jj_lib::backend::CommitId;
use jj_lib::content_hash::blake2b_hash;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::ViewId;
use libfuzzer_sys::fuzz_target;
use musubi_fuzz::scratch;
use musubi_jj::canonical::CanonicalError;
use musubi_jj::canonical::CanonicalStore;

thread_local! {
    static STORE: RefCell<CanonicalStore> = RefCell::new(open());
}

/// The store, empty but for what a store starts with if `fresh`, or as it was if not.
fn open_store(fresh: bool) -> CanonicalStore {
    let path = scratch().join("canonical");
    if fresh {
        fs::remove_dir_all(&path).ok();
    }
    CanonicalStore::open(&path, CommitId::from_bytes(&[0; 20])).unwrap()
}

fn open() -> CanonicalStore {
    open_store(true)
}

/// What importing an input came to.
enum Outcome {
    Refused,
    /// jj-lib panicked: the hub serving the import would open its store again.
    Panicked,
    /// Stored, and read back as what it hashes to: the next input needs a store without it.
    Admitted,
}

fuzz_target!(|data: &[u8]| {
    let Some((&choice, bytes)) = data.split_first() else {
        return;
    };
    let is_view = choice & 1 != 0;
    let import = |store: &CanonicalStore, id: &[u8]| {
        refusing_jj_lib_panics(|| {
            if is_view {
                store.import_view(&ViewId::from_bytes(id), bytes)
            } else {
                store.import_operation(&OperationId::from_bytes(id), bytes)
            }
        })
    };
    STORE.with_borrow_mut(|store| {
        let outcome = admit(store, choice, is_view, bytes, import);
        // Accepted or refused, it leaves nothing stored that isn't what its name says.
        assert_eq!(store.torn().unwrap(), Vec::<String>::new());
        match outcome {
            Outcome::Refused => {}
            Outcome::Panicked => *store = open_store(false),
            Outcome::Admitted => *store = open(),
        }
    });
});

/// Imports `bytes` first under an id they almost never hash to, then under the one they
/// do, which reaches the checks after the hash's.
fn admit(
    store: &CanonicalStore,
    choice: u8,
    is_view: bool,
    bytes: &[u8],
    import: impl Fn(&CanonicalStore, &[u8]) -> Option<Result<(), CanonicalError>>,
) -> Outcome {
    let actual = match import(store, &[choice; 64]) {
        None => return Outcome::Panicked,
        Some(Err(CanonicalError::HashMismatch { actual, .. })) => actual,
        Some(_) => return Outcome::Refused,
    };
    let id = OperationId::try_from_hex(&actual).unwrap();
    match import(store, id.as_bytes()) {
        None => return Outcome::Panicked,
        Some(Err(_)) => return Outcome::Refused,
        Some(Ok(())) => {}
    }
    if is_view {
        let id = ViewId::from_bytes(id.as_bytes());
        let view = store.read_view(&id).unwrap();
        assert_eq!(blake2b_hash(&view).as_slice(), id.as_bytes());
        // Stored in normal form, which may order fields differently from `bytes`.
        assert_eq!(store.view_bytes(&id).unwrap().len(), bytes.len());
    } else {
        let op = store.read_operation(&id).unwrap();
        assert_eq!(blake2b_hash(&op).as_slice(), id.as_bytes());
        assert_eq!(store.operation_bytes(&id).unwrap(), bytes);
    }
    Outcome::Admitted
}

/// What `import` returns, or `None` if it panicked in jj-lib, which panics on some malformed
/// input. A panic anywhere else is passed on to the fuzzer.
fn refusing_jj_lib_panics<T>(import: impl FnOnce() -> T) -> Option<T> {
    static HOOK: Once = Once::new();
    HOOK.call_once(|| {
        let fuzzer_hook = panic::take_hook();
        panic::set_hook(Box::new(move |info| {
            let in_jj_lib = info
                .location()
                .is_some_and(|at| at.file().contains("/jj-lib-"));
            if !in_jj_lib {
                fuzzer_hook(info);
            }
        }));
    });
    panic::catch_unwind(AssertUnwindSafe(import)).ok()
}
