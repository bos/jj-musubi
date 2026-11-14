//! Private observation points for native correspondence tests. Observers never answer queries.

use std::cell::RefCell;
use std::sync::Arc;

use crate::op_id::LocalOp;

#[derive(Clone, Debug)]
pub(super) enum Event {
    Captured(Vec<LocalOp>),
    Prepared,
    GitLocked,
    HeadsLocked,
    HeadsUnlocked,
    GitUnlocked,
    Sources(Vec<LocalOp>),
    Reread {
        captured: Vec<LocalOp>,
        actual: Vec<LocalOp>,
    },
    HelperBranch {
        locked: bool,
        heads: Vec<LocalOp>,
    },
    Loaded(LocalOp),
    HelperComplete,
    Export(LocalOp),
    Exported(LocalOp),
    Cleanup,
    Complete,
    Write {
        op: jj_lib::op_store::Operation,
        records: serde_json::Value,
    },
    Heads {
        old: Vec<jj_lib::op_store::OperationId>,
        new: jj_lib::op_store::OperationId,
        before: Vec<jj_lib::op_store::OperationId>,
        after: Vec<jj_lib::op_store::OperationId>,
        records: serde_json::Value,
    },
}

pub(super) type Observer = Arc<dyn Fn(Event) + Send + Sync>;

thread_local! {
    static OBSERVER: RefCell<Option<Observer>> = const { RefCell::new(None) };
}

pub(super) fn observer() -> Option<Observer> {
    OBSERVER.with(|slot| slot.borrow().clone())
}

pub(super) fn trace(event: &Event) {
    if std::env::var_os("MUSUBI_NATIVE_CONTRACT_TRACE").is_some() {
        eprintln!("native event: {event:?}");
    }
}

pub(super) fn emit(event: Event) {
    trace(&event);
    let observer = observer();
    if let Some(observer) = observer {
        observer(event);
    }
}

pub(super) struct Observe(Option<Observer>);

impl Observe {
    pub(super) fn new(observer: impl Fn(Event) + Send + Sync + 'static) -> Self {
        Self(OBSERVER.with(|slot| slot.replace(Some(Arc::new(observer)))))
    }
}

impl Drop for Observe {
    fn drop(&mut self) {
        OBSERVER.with(|slot| slot.replace(self.0.take()));
    }
}

/// Raw receipt state, before a source-role selector consumes it. No chosen counterpart or
/// prequalified owned map is supplied as an expected answer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Receipt {
    pub heads: Vec<LocalOp>,
    pub locals: std::collections::HashMap<LocalOp, Vec<LocalOp>>,
    pub sources: std::collections::HashMap<LocalOp, crate::op_id::CanonicalOp>,
    pub prefix: crate::records::RecordPrefix,
    pub records: Vec<crate::records::Record>,
    pub base: Option<crate::records::HubOp>,
    pub switched: bool,
}
