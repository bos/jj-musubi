//! Storage-call faults over the same abstract stores as ordinary conformance. These are
//! logical effects of the production adapters, not simulated file corruption.

use std::cell::RefCell;
use std::convert::Infallible;
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

use musubi_core::hub::HubStorage;
use musubi_core::message::{OpEntry, RecordState, Records};
use musubi_core::node::LocalRepo;
use serde_json::{Value, json};

use super::model::{FakeHub, FakeRepo, Obj, Op};

/// Fail before the call, after a complete logical effect, or after an import's prefix.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Timing {
    Before,
    After,
    Prefix,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StorageError {
    pub call: &'static str,
    pub timing: Timing,
}

#[derive(Default)]
pub struct Faults {
    remaining: Option<usize>,
    timing: Option<Timing>,
    pub calls: Vec<&'static str>,
    pub failed: Option<StorageError>,
    observed: bool,
    /// Model actions performed by this core entry point before it failed.
    pub effects: Vec<Value>,
    /// A storage prefix for which the oracle has no action with the real network unchanged.
    pub outside_model: bool,
}

pub type SharedFaults = Rc<RefCell<Faults>>;

impl Faults {
    pub fn arm(&mut self, at: usize, timing: Timing) {
        assert!(at > 0);
        *self = Self {
            remaining: Some(at),
            timing: Some(timing),
            ..Self::default()
        };
    }

    pub fn observe(&mut self, error: &StorageError) {
        assert_eq!(
            self.failed.as_ref(),
            Some(error),
            "unexpected storage error"
        );
        assert!(
            !self.observed,
            "one injected error reached the caller twice"
        );
        self.observed = true;
    }

    pub fn check_observed(&self) {
        assert!(
            self.failed.is_none() || self.observed,
            "core swallowed injected storage error: {:?}",
            self.failed
        );
    }

    pub fn disarm(&mut self) {
        self.check_observed();
        self.remaining = None;
        self.timing = None;
    }

    pub fn active(&self) -> bool {
        self.timing.is_some()
    }

    pub fn begin(&mut self) {
        self.effects.clear();
        self.outside_model = false;
    }

    fn enter(
        &mut self,
        call: &'static str,
        after: bool,
        prefix: bool,
    ) -> Result<Option<Timing>, StorageError> {
        let eligible = match self.timing {
            Some(Timing::Before) => true,
            Some(Timing::After) => after,
            Some(Timing::Prefix) => prefix,
            None => false,
        };
        if !eligible {
            return Ok(None);
        }
        self.calls.push(call);
        let Some(left) = &mut self.remaining else {
            return Ok(None);
        };
        *left -= 1;
        if *left != 0 {
            return Ok(None);
        }
        self.remaining = None;
        let timing = self.timing.expect("armed");
        self.failed = Some(StorageError { call, timing });
        if timing == Timing::Before {
            Err(self.failed.clone().unwrap())
        } else {
            Ok(Some(timing))
        }
    }

    fn finish(&self, hit: Option<Timing>) -> Result<(), StorageError> {
        match hit {
            None => Ok(()),
            Some(_) => Err(self.failed.clone().expect("selected call")),
        }
    }
}

/// Delegates ordinary calls unchanged. A shared gate counts actual trait calls, including
/// reads through `&self`; calls the fake makes internally are not adapter boundaries.
pub struct Fallible<S> {
    inner: S,
    faults: SharedFaults,
}

impl<S> Fallible<S> {
    pub fn new(inner: S, faults: SharedFaults) -> Self {
        Self { inner, faults }
    }

    fn enter(
        &self,
        name: &'static str,
        after: bool,
        prefix: bool,
    ) -> Result<Option<Timing>, StorageError> {
        self.faults.borrow_mut().enter(name, after, prefix)
    }

    fn effect(&self, action: impl FnOnce() -> Value) {
        // No journal or JSON allocations on the ordinary protocol-test path.
        let mut faults = self.faults.borrow_mut();
        if faults.timing.is_some() {
            faults.effects.push(action());
        }
    }
}

impl<S> Deref for Fallible<S> {
    type Target = S;
    fn deref(&self) -> &S {
        &self.inner
    }
}

impl<S> DerefMut for Fallible<S> {
    fn deref_mut(&mut self) -> &mut S {
        &mut self.inner
    }
}

fn infallible<T>(result: Result<T, Infallible>) -> T {
    result.unwrap_or_else(|never| match never {})
}

// Pure logical reads. Some production implementations also fill caches or write temporary
// bundles; those effects are absent from the model and are not fabricated here.
macro_rules! reads {
    ($($name:ident($($arg:ident: $ty:ty),*) -> $out:ty = $call:literal;)*) => {$ (
        fn $name(&self, $($arg: $ty),*) -> Result<$out, StorageError> {
            self.enter($call, false, false)?;
            Ok(infallible(self.inner.$name($($arg),*)))
        }
    )*};
}

impl HubStorage for Fallible<FakeHub> {
    type Op = Op;
    type Attachment = Vec<Obj>;
    type Error = StorageError;

    fn head(&self) -> (u64, Op) {
        self.inner.head()
    }
    fn records(&self) -> RecordState {
        self.inner.records()
    }

    fn pruned(&self) -> RecordState {
        self.inner.pruned()
    }
    fn report(&mut self, machine: &str, records: &RecordState) {
        self.inner.report(machine, records);
    }
    fn reported(&self, machine: &str) -> Option<RecordState> {
        self.inner.reported(machine)
    }
    fn prune(&mut self, count: u64) -> Result<(), StorageError> {
        self.enter("hub.prune", false, false)?;
        infallible(self.inner.prune(count));
        Ok(())
    }

    reads! {
        records_since(records: &RecordState) -> (u64, Vec<Vec<Op>>) = "hub.records_since";
        is_dropped(op: &Op, dropped: &[Op]) -> bool = "hub.is_dropped";
        ops_since(head: &Op, base: &Op) -> (Vec<OpEntry<Op>>, Vec<Obj>) = "hub.ops_since";
        objects_for(ops: &[Op], base: &Op, haves: &Vec<Obj>) -> Vec<Obj> = "hub.objects_for";
        is_closed(op: &Op, dropped: &[Op]) -> bool = "hub.is_closed";
        descends(ancestor: &Op, op: &Op, dropped: &[Op]) -> bool = "hub.descends";
    }

    fn set_head(&mut self, seq: u64, head: &Op, dropped: &[Op]) -> Result<(), StorageError> {
        // HubStore appends before updating its in-memory head. Failures during that append,
        // contraction or indexing need its real log/cache state, not an invented atomic commit.
        self.enter("hub.set_head", false, false)?;
        infallible(self.inner.set_head(seq, head, dropped));
        Ok(())
    }

    fn store_ops(&mut self, ops: &[Op], attachment: &Vec<Obj>) -> Result<(), StorageError> {
        let hit = self.enter("hub.store_ops", !ops.is_empty(), ops.len() > 1)?;
        let ops = if hit == Some(Timing::Prefix) {
            &ops[..ops.len().div_ceil(2)]
        } else {
            ops
        };
        let changed = ops.iter().any(|op| !self.inner.ops.contains(op));
        infallible(self.inner.store_ops(ops, attachment));
        self.faults.borrow_mut().outside_model |= changed;
        self.faults.borrow().finish(hit)
    }

    fn store_objects(&mut self, ops: &[Op], objs: &Vec<Obj>) -> Result<(), StorageError> {
        let hit = self.enter("hub.store_objects", !objs.is_empty(), objs.len() > 1)?;
        let prefix;
        let objs = if hit == Some(Timing::Prefix) {
            prefix = objs[..objs.len().div_ceil(2)].to_vec();
            &prefix
        } else {
            objs
        };
        let changed = objs.iter().any(|obj| !self.inner.objs.contains(obj));
        infallible(self.inner.store_objects(ops, objs));
        self.faults.borrow_mut().outside_model |= changed;
        self.faults.borrow().finish(hit)
    }
}

impl LocalRepo for Fallible<FakeRepo> {
    type Op = Op;
    type Attachment = Vec<Obj>;
    type Error = StorageError;

    fn machine(&self) -> String {
        self.inner.machine()
    }
    fn lacks_pruned(&self) -> StorageError {
        panic!("the fixed-node model cannot lack pruned records")
    }

    reads! {
        is_local(op: &Op) -> bool = "node.is_local";
        is_ancestor(ancestor: &Op, op: &Op) -> bool = "node.is_ancestor";
        ops_between(head: &Op, base: &Op) -> Vec<Op> = "node.ops_between";
        ops_attachment(ops: &[Op]) -> Vec<Obj> = "node.ops_attachment";
        objects_attachment(ops: &[Op], base: &Op) -> Vec<Obj> = "node.objects_attachment";
        fetch_haves() -> Vec<Obj> = "node.fetch_haves";
        objects_request(ops: &[Op]) -> Vec<Obj> = "node.objects_request";
        staged_parents(op: &Op) -> Option<Vec<Op>> = "node.staged_parents";
        objects_missing(ops: &[Op]) -> Vec<Op> = "node.objects_missing";
        accepted_base() -> Op = "node.accepted_base";
        applied_records() -> Records<Op> = "node.applied_records";
        records() -> RecordState = "node.records";
        pending() -> Vec<Op> = "node.pending";
        records_state(records: &Records<Op>) -> RecordState = "node.records_state";
        fresh() -> bool = "node.fresh";
        held(prefix: &RecordState) -> Option<Records<Op>> = "node.held";
        is_dropped(op: &Op) -> bool = "node.is_dropped";
    }

    fn share(&mut self) -> Result<(), StorageError> {
        self.enter("node.share", false, false)?;
        infallible(self.inner.share());
        Ok(())
    }
    fn pushing(&mut self, head: &Op) -> Result<(), StorageError> {
        self.enter("node.pushing", false, false)?;
        infallible(self.inner.pushing(head));
        Ok(())
    }
    fn learned(&mut self, head: &Op) -> Result<(), StorageError> {
        self.enter("node.learned", false, false)?;
        infallible(self.inner.learned(head));
        Ok(())
    }

    fn heads(&mut self) -> Result<Vec<Op>, StorageError> {
        self.enter("node.heads", false, false)?;
        Ok(infallible(self.inner.heads()))
    }

    fn prepare_records(&mut self, records: &Records<Op>) -> Result<bool, StorageError> {
        self.enter("node.prepare_records", false, false)?;
        Ok(infallible(self.inner.prepare_records(records)))
    }

    fn merge_heads(&mut self) -> Result<(), StorageError> {
        let hit = self.enter("node.merge_heads", true, false)?;
        infallible(self.inner.merge_heads());
        let (_, parents, objs) = self.inner.last_merge.as_ref().unwrap();
        self.effect(
            || json!({"kind": "merge", "node": self.inner.index, "parents": parents, "objs": objs}),
        );
        self.faults.borrow().finish(hit)
    }

    fn stage_ops(
        &mut self,
        ops: &[OpEntry<Op>],
        attachment: &Vec<Obj>,
    ) -> Result<(), StorageError> {
        let hit = self.enter("node.stage_ops", !ops.is_empty(), ops.len() > 1)?;
        let all = ops.len();
        let ops = if hit == Some(Timing::Prefix) {
            &ops[..all.div_ceil(2)]
        } else {
            ops
        };
        let changed = ops.iter().any(|op| !self.inner.sops.contains_key(&op.id));
        infallible(self.inner.stage_ops(ops, attachment));
        self.faults.borrow_mut().outside_model |= changed && ops.len() != all;
        if ops.len() == all {
            self.effect(|| json!({"kind": "recvOps", "node": self.inner.index, "ops": ops.iter().map(|op| op.id).collect::<Vec<_>>()}));
        }
        self.faults.borrow().finish(hit)
    }

    fn stage_objects(&mut self, ops: &[Op], objs: &Vec<Obj>) -> Result<(), StorageError> {
        let hit = self.enter("node.stage_objects", !objs.is_empty(), objs.len() > 1)?;
        let prefix;
        let all = objs.len();
        let objs = if hit == Some(Timing::Prefix) {
            prefix = objs[..all.div_ceil(2)].to_vec();
            &prefix
        } else {
            objs
        };
        let changed = objs.iter().any(|obj| !self.inner.sobj.contains(obj));
        infallible(self.inner.stage_objects(ops, objs));
        let received = objs.iter().all(|obj| self.inner.sobj.contains(obj));
        self.faults.borrow_mut().outside_model |= changed && received && objs.len() != all;
        if received && objs.len() == all {
            self.effect(|| json!({"kind": "recvObjs", "node": self.inner.index, "objs": objs}));
        }
        self.faults.borrow().finish(hit)
    }

    fn realize(&mut self, op: &Op) -> Result<(), StorageError> {
        self.enter("node.realize", false, false)?;
        infallible(self.inner.realize(op));
        Ok(())
    }

    fn advance(&mut self, op: &Op) -> Result<(), StorageError> {
        let hit = self.enter("node.advance", true, false)?;
        infallible(self.inner.advance(op));
        self.effect(|| {
            let advanced = self.inner.last_advance.as_ref().expect("advanced");
            advanced.action(self.inner.index)
        });
        self.faults.borrow().finish(hit)
    }

    fn set_accepted_base(&mut self, op: &Op) -> Result<(), StorageError> {
        let hit = self.enter("node.set_accepted_base", true, false)?;
        infallible(self.inner.set_accepted_base(op));
        self.faults.borrow().finish(hit)
    }

    fn adopt(&mut self, records: &Records<Op>) -> Result<(), StorageError> {
        let hit = self.enter("node.adopt", true, false)?;
        infallible(self.inner.adopt(records));
        self.effect(
            || json!({"kind": "adopt", "node": self.inner.index, "records": records.records}),
        );
        self.faults.borrow().finish(hit)
    }

    fn write_fixup(&mut self, publish_from: Option<&Op>) -> Result<Option<Op>, StorageError> {
        let hit = self.enter("node.write_fixup", true, false)?;
        let result = infallible(self.inner.write_fixup(publish_from));
        if let Some((_, parent)) = self.inner.last_fixup {
            self.effect(|| json!({"kind": "userOp", "node": self.inner.index, "parent": parent, "objs": []}));
        }
        self.faults.borrow().finish(hit)?;
        Ok(result)
    }
}
