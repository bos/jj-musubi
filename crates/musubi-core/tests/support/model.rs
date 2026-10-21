//! Test implementations of the core's storage traits that keep exactly the Lean model's
//! state (docs/conformance.md, "The abstraction").

use std::cell::Cell;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::convert::Infallible;
use std::rc::Rc;

use musubi_core::hub::HubStorage;
use musubi_core::message::OpEntry;
use musubi_core::node::LocalRepo;

pub type Op = u64;
pub type Obj = u64;
pub const ROOT: Op = 0;

/// The operation universe: parents and objects of every operation created so far.
#[derive(Debug, Default)]
pub struct Univ {
    pub parents: Vec<Vec<Op>>,
    pub objs: Vec<Vec<Obj>>,
    pub creator: Vec<Option<usize>>,
    next_obj: Obj,
}

impl Univ {
    pub fn new() -> Self {
        Self {
            parents: vec![vec![]],
            objs: vec![vec![]],
            creator: vec![None],
            next_obj: 0,
        }
    }

    pub fn next(&self) -> Op {
        self.parents.len() as Op
    }

    pub fn fresh_objs(&mut self, count: usize) -> Vec<Obj> {
        (0..count)
            .map(|_| {
                self.next_obj += 1;
                self.next_obj
            })
            .collect()
    }

    pub fn create(&mut self, creator: usize, parents: Vec<Op>, objs: Vec<Obj>) -> Op {
        let id = self.next();
        self.parents.push(parents);
        self.objs.push(objs);
        self.creator.push(Some(creator));
        id
    }

    /// `anc*(op)`.
    pub fn ancestors(&self, op: Op) -> BTreeSet<Op> {
        let mut seen = BTreeSet::new();
        let mut stack = vec![op];
        while let Some(x) = stack.pop() {
            if seen.insert(x) {
                stack.extend(self.parents[x as usize].iter().copied());
            }
        }
        seen
    }

    pub fn is_ancestor(&self, ancestor: Op, op: Op) -> bool {
        self.ancestors(op).contains(&ancestor)
    }

    /// `anc*(head) \ anc*(base)`, ancestors first (ids are topologically ordered).
    pub fn between(&self, head: Op, base: Op) -> Vec<Op> {
        let exclude = self.ancestors(base);
        self.ancestors(head)
            .into_iter()
            .filter(|x| !exclude.contains(x))
            .collect()
    }

    pub fn objs_of(&self, ops: impl IntoIterator<Item = Op>) -> BTreeSet<Obj> {
        ops.into_iter()
            .flat_map(|op| self.objs[op as usize].iter().copied())
            .collect()
    }

    /// `max(set)`: the elements that are not ancestors of another element.
    pub fn maximal(&self, set: &BTreeSet<Op>) -> BTreeSet<Op> {
        set.iter()
            .copied()
            .filter(|&x| !set.iter().any(|&y| y != x && self.is_ancestor(x, y)))
            .collect()
    }
}

pub type SharedUniv = Rc<RefCell<Univ>>;

/// The hub's persistent state.
pub struct FakeHub {
    pub univ: SharedUniv,
    pub ops: BTreeSet<Op>,
    pub objs: BTreeSet<Obj>,
    pub head: Op,
    pub seq: u64,
}

impl FakeHub {
    pub fn new(univ: SharedUniv) -> Self {
        Self {
            univ,
            ops: BTreeSet::from([ROOT]),
            objs: BTreeSet::new(),
            head: ROOT,
            seq: 0,
        }
    }

    pub fn closed(&self, op: Op) -> bool {
        let univ = self.univ.borrow();
        univ.ancestors(op).into_iter().all(|x| {
            self.ops.contains(&x) && univ.objs[x as usize].iter().all(|o| self.objs.contains(o))
        })
    }
}

impl HubStorage for FakeHub {
    type Op = Op;
    /// Object ids carried by object transfers; empty otherwise.
    type Attachment = Vec<Obj>;
    type Error = Infallible;

    fn head(&self) -> (u64, Op) {
        (self.seq, self.head)
    }

    fn set_head(&mut self, seq: u64, head: &Op) -> Result<(), Infallible> {
        self.seq = seq;
        self.head = *head;
        Ok(())
    }

    fn store_ops(&mut self, ops: &[Op], _: &Vec<Obj>) -> Result<(), Infallible> {
        self.ops.extend(ops.iter().copied());
        Ok(())
    }

    fn store_objects(&mut self, _: &[Op], objs: &Vec<Obj>) -> Result<(), Infallible> {
        self.objs.extend(objs.iter().copied());
        Ok(())
    }

    fn ops_since(&self, head: &Op, base: &Op) -> Result<(Vec<OpEntry<Op>>, Vec<Obj>), Infallible> {
        let univ = self.univ.borrow();
        let entries = univ
            .between(*head, *base)
            .into_iter()
            .filter(|op| self.ops.contains(op))
            .map(|id| OpEntry {
                id,
                parents: univ.parents[id as usize].clone(),
            })
            .collect();
        Ok((entries, vec![]))
    }

    /// The model's objects have no structure, so `closure(base)` says nothing; the node's
    /// haves say everything it has.
    fn objects_for(
        &self,
        for_ops: &[Op],
        _: &Op,
        haves: &Vec<Obj>,
    ) -> Result<Vec<Obj>, Infallible> {
        let univ = self.univ.borrow();
        let wanted = univ.objs_of(for_ops.iter().copied());
        Ok(wanted
            .into_iter()
            .filter(|o| self.objs.contains(o) && !haves.contains(o))
            .collect())
    }

    fn is_closed(&self, op: &Op) -> Result<bool, Infallible> {
        Ok(self.closed(*op))
    }

    fn descends(&self, ancestor: &Op, op: &Op) -> Result<bool, Infallible> {
        Ok(self.univ.borrow().is_ancestor(*ancestor, *op))
    }
}

/// A node's persistent state: its jj repository and staged files.
pub struct FakeRepo {
    pub univ: SharedUniv,
    pub index: usize,
    pub lops: BTreeSet<Op>,
    pub lobj: BTreeSet<Obj>,
    pub heads: BTreeSet<Op>,
    pub sops: BTreeMap<Op, Vec<Op>>,
    pub sobj: BTreeSet<Obj>,
    pub base: Op,
    /// Objects a merge creates, chosen by the test before each step.
    pub merge_objs: usize,
    /// The merge the last `merge_heads` created: `(id, parents, objs)`.
    pub last_merge: Option<(Op, Vec<Op>, Vec<Obj>)>,
    /// How often the core read a staged operation, and asked about objects: the work a
    /// real repository does in files and `git` processes.
    pub staged_reads: Cell<usize>,
    pub object_checks: Cell<usize>,
    /// Crash before writing the next objects to stage: a real repository writes operations
    /// and objects separately.
    pub crash_before_objects: bool,
    /// Whether the objects the next `stage_objects` brings are lost: set by staging a fetch's
    /// operations while `crash_before_objects` is armed, so an `Objects` reply, which stages
    /// no operations, is not lost.
    objects_lost: bool,
}

impl FakeRepo {
    pub fn new(univ: SharedUniv, index: usize) -> Self {
        Self {
            univ,
            index,
            lops: BTreeSet::from([ROOT]),
            lobj: BTreeSet::new(),
            heads: BTreeSet::from([ROOT]),
            sops: BTreeMap::new(),
            sobj: BTreeSet::new(),
            base: ROOT,
            merge_objs: 0,
            last_merge: None,
            staged_reads: Cell::new(0),
            object_checks: Cell::new(0),
            crash_before_objects: false,
            objects_lost: false,
        }
    }

    /// `UserOp(p)`: a `jj` command based at `parent` writes a new operation.
    pub fn user_op(&mut self, parent: Op, objs: usize) -> (Op, Vec<Obj>) {
        let mut univ = self.univ.borrow_mut();
        let objs = univ.fresh_objs(objs);
        let op = univ.create(self.index, vec![parent], objs.clone());
        self.lops.insert(op);
        self.lobj.extend(objs.iter().copied());
        let mut heads = self.heads.clone();
        heads.remove(&parent);
        heads.insert(op);
        self.heads = univ.maximal(&heads);
        (op, objs)
    }
}

impl LocalRepo for FakeRepo {
    type Op = Op;
    type Attachment = Vec<Obj>;
    type Error = Infallible;

    fn heads(&mut self) -> Result<Vec<Op>, Infallible> {
        Ok(self.heads.iter().copied().collect())
    }

    fn is_local(&self, op: &Op) -> Result<bool, Infallible> {
        Ok(self.lops.contains(op))
    }

    fn is_ancestor(&self, ancestor: &Op, op: &Op) -> Result<bool, Infallible> {
        Ok(self.univ.borrow().is_ancestor(*ancestor, *op))
    }

    fn merge_heads(&mut self) -> Result<(), Infallible> {
        assert!(self.heads.len() >= 2, "merge with fewer than two heads");
        let mut univ = self.univ.borrow_mut();
        let parents: Vec<Op> = self.heads.iter().copied().collect();
        let objs = univ.fresh_objs(self.merge_objs);
        let op = univ.create(self.index, parents.clone(), objs.clone());
        self.lops.insert(op);
        self.lobj.extend(objs.iter().copied());
        self.heads = BTreeSet::from([op]);
        self.last_merge = Some((op, parents, objs));
        Ok(())
    }

    fn ops_between(&self, head: &Op, base: &Op) -> Result<Vec<Op>, Infallible> {
        Ok(self.univ.borrow().between(*head, *base))
    }

    fn ops_attachment(&self, _: &[Op]) -> Result<Vec<Obj>, Infallible> {
        Ok(vec![])
    }

    fn objects_attachment(&self, ops: &[Op], _: &Op) -> Result<Vec<Obj>, Infallible> {
        Ok(self
            .univ
            .borrow()
            .objs_of(ops.iter().copied())
            .into_iter()
            .collect())
    }

    /// Every object this node has, which the hub then leaves out.
    fn fetch_haves(&self) -> Result<Vec<Obj>, Infallible> {
        Ok(self.lobj.iter().chain(&self.sobj).copied().collect())
    }

    fn objects_request(&self, _: &[Op]) -> Result<Vec<Obj>, Infallible> {
        self.fetch_haves()
    }

    fn stage_ops(&mut self, ops: &[OpEntry<Op>], _: &Vec<Obj>) -> Result<(), Infallible> {
        for entry in ops {
            self.sops.insert(entry.id, entry.parents.clone());
        }
        self.objects_lost = self.crash_before_objects;
        Ok(())
    }

    fn stage_objects(&mut self, _: &[Op], objs: &Vec<Obj>) -> Result<(), Infallible> {
        if !std::mem::take(&mut self.objects_lost) {
            self.sobj.extend(objs.iter().copied());
        }
        Ok(())
    }

    fn staged_parents(&self, op: &Op) -> Result<Option<Vec<Op>>, Infallible> {
        self.staged_reads.set(self.staged_reads.get() + 1);
        Ok(self.sops.get(op).cloned())
    }

    fn objects_missing(&self, ops: &[Op]) -> Result<Vec<Op>, Infallible> {
        self.object_checks.set(self.object_checks.get() + 1);
        let univ = self.univ.borrow();
        Ok(ops
            .iter()
            .filter(|op| {
                !univ.objs[**op as usize]
                    .iter()
                    .all(|o| self.lobj.contains(o) || self.sobj.contains(o))
            })
            .copied()
            .collect())
    }

    /// Like a real repository, refuses to realize anything not staged, without its parents,
    /// or without its objects.
    fn realize(&mut self, op: &Op) -> Result<(), Infallible> {
        let univ = self.univ.borrow();
        assert!(self.sops.contains_key(op), "realize {op}: not staged");
        let parents = &univ.parents[*op as usize];
        assert!(
            parents.iter().all(|p| self.lops.contains(p)),
            "realize {op}: parents missing"
        );
        let objs = &univ.objs[*op as usize];
        assert!(
            objs.iter()
                .all(|o| self.lobj.contains(o) || self.sobj.contains(o)),
            "realize {op}: objects missing"
        );
        self.lops.insert(*op);
        self.lobj.extend(objs.iter().copied());
        Ok(())
    }

    fn advance(&mut self, op: &Op) -> Result<(), Infallible> {
        assert!(self.lops.contains(op), "advance {op}: not local");
        let mut heads = self.heads.clone();
        heads.insert(*op);
        self.heads = self.univ.borrow().maximal(&heads);
        Ok(())
    }

    fn accepted_base(&self) -> Result<Op, Infallible> {
        Ok(self.base)
    }

    fn set_accepted_base(&mut self, op: &Op) -> Result<(), Infallible> {
        self.base = *op;
        Ok(())
    }
}
