//! The functions of one ref's slot in formal/Musubi/Refs.lean, answered by the Lean oracle
//! (`RefsExec.lean`; docs/internals/conformance.md, "Per-machine refs"). The model is over
//! any ref algebra, and the tests' targets are jj's, which the oracle can't merge. So this
//! numbers each target it sends, `0` for none, and sends with each request which targets are
//! resolved and which writable, the terms of each conflict, and jj-lib's `merge_ref_targets`
//! of every triple of the request's targets that the laws don't settle, which are all the
//! merges the slot functions make. Equal targets have equal numbers, so the model compares
//! targets as jj does.

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::sync::Arc;

use futures::executor::block_on;
use jj_lib::op_store::RefTarget;
use jj_lib::refs::merge_ref_targets;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use serde_json::Value;
use serde_json::json;

use super::oracle::Oracle;

/// The model's `TSlot`: the bookmark, its remote ref, jj's record of the git ref, and whether
/// the bookmark tracks the remote ref.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Slot {
    pub l: RefTarget,
    pub r: RefTarget,
    pub k: RefTarget,
    pub tr: bool,
}

// One oracle for every model on this thread: the model's requests leave it as they found it.
thread_local!(static ORACLE: RefCell<Option<Oracle>> = const { RefCell::new(None) });

/// The model, with the targets numbered so far and jj's merges of them.
pub struct RefsModel {
    repo: Arc<ReadonlyRepo>,
    targets: Vec<RefTarget>,
    merges: HashMap<[usize; 3], usize>,
}

impl RefsModel {
    /// The model of refs whose targets are commits of `repo`, merged by its index.
    pub fn new(repo: Arc<ReadonlyRepo>) -> Self {
        Self {
            repo,
            targets: vec![RefTarget::absent()],
            merges: HashMap::new(),
        }
    }

    fn id(&mut self, target: &RefTarget) -> usize {
        match self.targets.iter().position(|t| t == target) {
            Some(id) => id,
            None => {
                self.targets.push(target.clone());
                self.targets.len() - 1
            }
        }
    }

    fn target(&self, value: &Value) -> RefTarget {
        let id = value.as_u64().unwrap() as usize;
        self.targets
            .get(id)
            .unwrap_or_else(|| panic!("the oracle needed a merge it wasn't sent ({value})"))
            .clone()
    }

    fn merge(&mut self, ids: [usize; 3]) -> usize {
        if let Some(&merged) = self.merges.get(&ids) {
            return merged;
        }
        let [a, b, c] = ids.map(|id| self.targets[id].clone());
        let merged = block_on(merge_ref_targets(self.repo.index(), &a, &b, &c)).unwrap();
        let merged = self.id(&merged);
        self.merges.insert(ids, merged);
        merged
    }

    fn slot_json(&mut self, slot: &Slot, ids: &mut BTreeSet<usize>) -> Value {
        let [l, r, k] = [&slot.l, &slot.r, &slot.k].map(|t| self.id(t));
        ids.extend([l, r, k]);
        json!({"L": l, "R": r, "K": k, "tr": slot.tr})
    }

    fn slot_of(&self, value: &Value) -> Slot {
        Slot {
            l: self.target(&value["L"]),
            r: self.target(&value["R"]),
            k: self.target(&value["K"]),
            tr: value["tr"].as_bool().unwrap(),
        }
    }

    /// Asks the oracle for `function` of `slots` and `targets`, with `flags`.
    fn call(
        &mut self,
        function: &str,
        slots: &[(&str, &Slot)],
        targets: &[(&str, &RefTarget)],
        flags: &[(&str, bool)],
    ) -> Value {
        let mut request = json!({"op": "refs", "fn": function});
        let mut ids = BTreeSet::from([0]);
        for (key, slot) in slots {
            request[key] = self.slot_json(slot, &mut ids);
        }
        for (key, target) in targets {
            let id = self.id(target);
            ids.insert(id);
            request[key] = json!(id);
        }
        for (key, flag) in flags {
            request[key] = json!(flag);
        }
        let mut merges = vec![];
        for &a in &ids {
            for &b in &ids {
                for &c in &ids {
                    if a != b && b != c && a != c {
                        merges.push(json!([a, b, c, self.merge([a, b, c])]));
                    }
                }
            }
        }
        // Number each conflict's terms before saying which targets are what.
        let mut conflicts = vec![];
        for id in 0..self.targets.len() {
            if !self.targets[id].is_resolved() {
                let terms: Vec<RefTarget> = self.targets[id]
                    .iter()
                    .map(|term| RefTarget::resolved(term.clone()))
                    .collect();
                let terms: BTreeSet<usize> = terms.iter().map(|t| self.id(t)).collect();
                conflicts.push(json!({"conflict": id, "terms": terms}));
            }
        }
        let root = self.repo.store().root_commit_id();
        let resolved: Vec<usize> = (0..self.targets.len())
            .filter(|&id| self.targets[id].is_resolved())
            .collect();
        let writable: Vec<usize> = resolved
            .iter()
            .copied()
            .filter(|&id| self.targets[id].as_normal() != Some(root))
            .collect();
        request["table"] = json!({
            "resolved": resolved,
            "writable": writable,
            "terms": conflicts,
            "merges": merges,
        });
        let reply = ORACLE.with(|oracle| {
            oracle
                .borrow_mut()
                .get_or_insert_with(Oracle::spawn)
                .call(&request)
        });
        assert_eq!(reply["ok"], true, "the oracle refused {function}: {reply}");
        reply
    }

    fn slot_reply(&mut self, function: &str, slots: &[(&str, &Slot)]) -> Slot {
        let reply = self.call(function, slots, &[], &[]);
        self.slot_of(&reply["slot"])
    }

    /// `TSlot.set`: the bookmark at `l`.
    pub fn set(&mut self, s: &Slot, l: &RefTarget) -> Slot {
        let reply = self.call("set", &[("s", s)], &[("l", l)], &[]);
        self.slot_of(&reply["slot"])
    }

    /// `TSlot.track`.
    pub fn track(&mut self, s: &Slot) -> Slot {
        self.slot_reply("track", &[("s", s)])
    }

    /// `TSlot.import` of `.git`'s `g`, a new remote ref tracked by default.
    pub fn import(&mut self, s: &Slot, g: &RefTarget) -> Slot {
        let reply = self.call("import", &[("s", s)], &[("g", g)], &[]);
        self.slot_of(&reply["slot"])
    }

    /// `TSlot.merge`: jj's merge of `v` with `w` against `b`.
    pub fn merge_slots(&mut self, b: &Slot, v: &Slot, w: &Slot) -> Slot {
        self.slot_reply("merge", &[("b", b), ("v", v), ("w", w)])
    }

    fn exported(
        &mut self,
        function: &str,
        s: &Slot,
        targets: &[(&str, &RefTarget)],
    ) -> (Slot, RefTarget) {
        let reply = self.call(function, &[("s", s)], targets, &[]);
        (self.slot_of(&reply["slot"]), self.target(&reply["g"]))
    }

    /// `TSlot.exportLocal` with `.git` at `g`: the slot and `.git` after.
    pub fn export_local(&mut self, s: &Slot, g: &RefTarget) -> (Slot, RefTarget) {
        self.exported("exportLocal", s, &[("g", g)])
    }

    /// `exportRemote` with `.git` at `g`.
    pub fn export_remote(&mut self, s: &Slot, g: &RefTarget) -> (Slot, RefTarget) {
        self.exported("exportRemote", s, &[("g", g)])
    }

    /// `exportConflicted` with `.git` at `g` and expected value `e`.
    pub fn export_conflicted(
        &mut self,
        s: &Slot,
        g: &RefTarget,
        e: &RefTarget,
    ) -> (Slot, RefTarget) {
        self.exported("exportConflicted", s, &[("g", g), ("e", e)])
    }

    /// `LInv` of the slot with `.git` at `g`, which git `moved` or not.
    pub fn linv(&mut self, s: &Slot, g: &RefTarget, moved: bool) -> bool {
        self.call("linv", &[("s", s)], &[("g", g)], &[("moved", moved)])["holds"]
            .as_bool()
            .unwrap()
    }

    /// `CInv`, with expected value `e`.
    pub fn cinv(&mut self, s: &Slot, g: &RefTarget, moved: bool, e: &RefTarget) -> bool {
        self.call(
            "cinv",
            &[("s", s)],
            &[("g", g), ("e", e)],
            &[("moved", moved)],
        )["holds"]
            .as_bool()
            .unwrap()
    }

    /// `Restorable o` where the slot is `s`; for a remote bookmark (`remote`), `CStep.restore`'s
    /// condition, `RestorableRemote o` where the restored remote bookmark is resolved.
    pub fn restorable(&mut self, o: &Slot, s: &Slot, remote: bool) -> bool {
        let function = if remote {
            "restorableRemote"
        } else {
            "restorable"
        };
        self.call(function, &[("o", o), ("s", s)], &[], &[])["holds"]
            .as_bool()
            .unwrap()
    }
}
