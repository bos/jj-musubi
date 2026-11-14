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
    CurrentGit {
        canonical: crate::op_id::CanonicalOp,
        input: LocalOp,
        output: LocalOp,
        mapped: Option<crate::op_id::CanonicalOp>,
        preferred: Option<LocalOp>,
        source_before: serde_json::Value,
        source_after: serde_json::Value,
    },
    Reread {
        captured: Vec<LocalOp>,
        actual: Vec<LocalOp>,
    },
    RevalidationRetry {
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

type PreparationObserver =
    Arc<dyn Fn(&super::NodeRepo, &[crate::op_id::CanonicalOp], &[LocalOp]) + Send + Sync>;

thread_local! {
    static PREPARATION_OBSERVER: RefCell<Option<PreparationObserver>> =
        const { RefCell::new(None) };
}

/// This boundary is after preparation and before either publication lock or the head reread.
/// The borrowed actor permits complete raw memory observations without copying a stale actor
/// or exposing a query-answer callback. An observer may schedule the next real native actor.
pub(super) fn prepared(
    node: &super::NodeRepo,
    canonicals: &[crate::op_id::CanonicalOp],
    realized: &[LocalOp],
) {
    emit(Event::Prepared);
    let observer = PREPARATION_OBSERVER.with(|slot| slot.borrow().clone());
    if let Some(observer) = observer {
        observer(node, canonicals, realized);
    }
}

pub(super) struct ObservePreparation(Option<PreparationObserver>);

impl ObservePreparation {
    pub(super) fn new(
        observer: impl Fn(&super::NodeRepo, &[crate::op_id::CanonicalOp], &[LocalOp])
        + Send
        + Sync
        + 'static,
    ) -> Self {
        Self(PREPARATION_OBSERVER.with(|slot| slot.replace(Some(Arc::new(observer)))))
    }
}

impl Drop for ObservePreparation {
    fn drop(&mut self) {
        PREPARATION_OBSERVER.with(|slot| slot.replace(self.0.take()));
    }
}

type ProbeObserver = Arc<
    dyn Fn(&super::NodeRepo, &[LocalOp], Option<&Result<(LocalOp, usize), String>>) + Send + Sync,
>;

thread_local! {
    static PROBE_OBSERVER: RefCell<Option<ProbeObserver>> = const { RefCell::new(None) };
}

pub(super) fn probe_before(
    node: &super::NodeRepo,
    operands: &[jj_lib::operation::Operation],
) -> Option<Vec<LocalOp>> {
    let observer = PROBE_OBSERVER.with(|slot| slot.borrow().clone())?;
    let inputs = operands
        .iter()
        .map(|op| LocalOp(op.id().clone()))
        .collect::<Vec<_>>();
    observer(node, &inputs, None);
    Some(inputs)
}

pub(super) fn probe_after(
    node: &super::NodeRepo,
    inputs: &[LocalOp],
    outcome: &Result<(LocalOp, usize), String>,
) {
    if let Some(observer) = PROBE_OBSERVER.with(|slot| slot.borrow().clone()) {
        observer(node, inputs, Some(outcome));
    }
}

pub(super) struct ObserveProbes(Option<ProbeObserver>);

impl ObserveProbes {
    pub(super) fn new(
        observer: impl Fn(&super::NodeRepo, &[LocalOp], Option<&Result<(LocalOp, usize), String>>)
        + Send
        + Sync
        + 'static,
    ) -> Self {
        Self(PROBE_OBSERVER.with(|slot| slot.replace(Some(Arc::new(observer)))))
    }
}

impl Drop for ObserveProbes {
    fn drop(&mut self) {
        PROBE_OBSERVER.with(|slot| slot.replace(self.0.take()));
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
