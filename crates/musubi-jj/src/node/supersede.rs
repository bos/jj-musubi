//! Replicated `jj op abandon` on a node (docs/internals/design.md, "Abandoning operations"):
//! the hub's records this node took and what it dropped beyond them, noticing an abandon,
//! rewriting local operations to match the hive's history, taking the hub's records, and the
//! fix-up. Shared record state and naming live here; `storage` persists it, `normalize`
//! computes contracted names, `abandon` detects local abandons, `rewrite` moves local
//! operations and workspaces, `receive` takes hub records, and `fixup` restores dropped state.
//!
//! Three names can stand for one operation here. The hub's, as its records name its history
//! (*hub space*), which the protocol speaks in; this node's, with what it has yet to publish
//! dropped too (*node space*), which its local operations map to; and older names a record
//! has since superseded, which a `jj` command that loaded the repository before the record
//! still writes on. [`NodeRepo::to_node`] and [`NodeRepo::current`] translate them.

mod abandon;
mod fixup;
mod normalize;
mod receive;
mod rewrite;
mod storage;

use std::collections::HashMap;
use std::collections::HashSet;

use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;

use self::fixup::Fixup;
use self::normalize::Fact;
use self::normalize::Normal;
use self::normalize::Normalizer;
use self::normalize::fact;
use self::storage::Step;
use super::NodeError;
use super::NodeRepo;

use crate::canonical::CanonicalError;
use crate::canonical::Contraction;
use crate::canonical::current;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
use crate::records::HubOp;
use crate::records::Record;
use crate::records::RecordDigest;
use crate::records::RecordPrefix;

/// The attribute of a fix-up's work operation saying when the work it stands for was done,
/// in milliseconds since the epoch: the copy's latest work, which the abandon dropped.
pub const WORKED_AT_ATTRIBUTE: &str = "musubi.worked-at";

/// A canonical operation as this machine's history names it: the hub's history with what this
/// machine has yet to publish dropped too. Its local operations stand for these. Where it has
/// nothing to publish, a hub name and a node name are the same id.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeOp(pub CanonicalOp);

/// The attribute that marks an operation of a fix-up, whose canonical view is its parent's.
pub(super) const FIXUP_ATTRIBUTE: &str = "musubi.fixup";

/// What a node keeps about the hive's records.
#[derive(Default)]
pub(super) struct Records {
    /// The first of the hub's records this node took, known only by their count and digest:
    /// none, unless it joined after the hub pruned them.
    prefix: RecordPrefix,
    /// The hub's records this node took after `prefix`, oldest first.
    applied: Vec<Record>,
    /// The digest of `prefix` and each first so many of `applied`.
    digests: Vec<RecordDigest>,
    /// Records this node took that it no longer holds, as an older announcement gave it fewer
    /// or others: each with the digest of the records up to it, and of those before it. With
    /// those it holds, they are the records it has held ([`NodeRepo::held_records`]).
    earlier: Vec<Earlier>,
    /// Records of the hub's beyond those this node holds that it realized operations named as
    /// they name the history, before taking them, as while they drop an op head: each with
    /// the digest of the records up to it, and of those before it. Its history may leave out
    /// what they drop without its holding them, so that if the hub loses them, it publishes
    /// what they drop as its own drops. Not held: they count as none of the records it took.
    custody: Vec<Earlier>,
    /// Whether this node has nothing of the hive's, so that it may take the hub's records
    /// from those the hub pruned (`musubi_core::node::LocalRepo::fresh`): it joined on the
    /// root, and has taken no records, pushed nothing and realized nothing since.
    fresh: bool,
    /// What this node dropped beyond them.
    pending: Record,
    /// What to write before publishing `pending`, and whether it has been.
    fixup: Option<Fixup>,
    fixup_written: bool,
    /// The canonical operation the fix-up restores the state of: the head before the first
    /// abandon not yet published, as that history named it.
    fixup_from: Option<CanonicalOp>,
    /// Whether this node is moving its op heads to the rewrites of a renaming it recorded,
    /// as a restart then resumes.
    moving: bool,
    /// Where records this node took move its op heads and workspaces, until they have: a
    /// restart moves them there (`realign_heads`).
    realign: Option<Realign>,
    /// How many renamings this node made: applied records', and rewrites of this node's own
    /// drops.
    steps: usize,
    /// What each operation a renaming superseded became then. A renaming renames only what
    /// none before it superseded, so each has one entry, and what it became may have been
    /// superseded since ([`NodeRepo::current_ids`]).
    superseded: HashMap<CanonicalOp, Vec<CanonicalOp>>,
    /// The operations a step dropped, rather than rewrote, as it named them.
    dropped: HashSet<CanonicalOp>,
    /// Unmarked jj rewrites whose original identity was established while detecting an
    /// abandon. A delayed command can still refer to them after cache loss or restart.
    sources: HashMap<LocalOp, CanonicalOp>,
    /// How each record this node took renamed the hub's history below the base then, new name
    /// to old: to name what it drops as the hub does after the hub goes back and takes others.
    hub_renamings: Vec<HashMap<CanonicalOp, CanonicalOp>>,
    /// Hub space to node space: the hub's history with `pending` dropped too, as worked out.
    to_node: std::sync::Mutex<Option<Normalizer>>,
    /// Names as this node's history has them for raw operations of other histories
    /// ([`NodeRepo::current_ids`]).
    normal: std::sync::Mutex<Normal>,
    /// The hub's records this node is getting ready to take.
    taking: Option<Taking>,
    /// For tests of crashes and errors: where the next taking of records stops.
    stop: Option<TakingStop>,
}

/// Where a test stops the next taking of records ([`NodeRepo::fail_holding_records`],
/// [`NodeRepo::crash_taking_records`], [`NodeRepo::crash_publishing_taken_heads`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TakingStop {
    /// The write that holds them fails, having written none of it.
    Hold,
    /// Once they are held, before the op heads move there.
    Heads,
    /// Once the new op heads are in, before the old ones come out.
    Publishing,
    /// Once the op heads moved there, before the workspaces.
    Workspaces,
}

/// Where taking records moves the op heads and the workspaces, by the local operations
/// themselves, which, unlike the translation cache, a crash doesn't lose, written with the
/// records before anything moves.
#[derive(Clone, Debug)]
struct Realign {
    /// The op heads as they were, each with what it becomes.
    from: HashMap<LocalOp, Vec<LocalOp>>,
    /// The op heads they become.
    to: Vec<LocalOp>,
    /// The canonical operation each local operation the move names stands for, as the
    /// translation cache had it, and the rewrites of those the records rename: for the
    /// workspaces to move as the op heads did, and a `jj` command written on the op heads
    /// meanwhile to be canonicalized, and moved where the records name the history, as any
    /// other, even where the translation cache lost them since.
    canonical: HashMap<LocalOp, CanonicalOp>,
}

/// What taking records changes of what `records.json` has: to go back to if writing it
/// fails, so that this node never goes on as if it held records it doesn't.
struct Checkpoint {
    prefix: RecordPrefix,
    applied: Vec<Record>,
    digests: Vec<RecordDigest>,
    earlier: Vec<Earlier>,
    custody: Vec<Earlier>,
    fresh: bool,
    pending: Record,
    fixup: Option<Fixup>,
    fixup_written: bool,
    fixup_from: Option<CanonicalOp>,
    realign: Option<Realign>,
    steps: usize,
}

/// A record this node took that it no longer holds, or one it keeps in custody
/// (`Records::custody`).
#[derive(Clone)]
struct Earlier {
    /// The digest of the records up to it.
    digest: RecordDigest,
    /// The digest of the records before it.
    before: RecordDigest,
    record: Record,
}

/// Records of the hub's being taken: the node's history renamed as they name it, written
/// beside its own, until its op heads move there, as this node takes them.
struct Taking {
    /// The first of them, known only by their count and digest.
    prefix: RecordPrefix,
    records: Vec<Record>,
    /// How many of them this node took already.
    common: usize,
    /// How each of the rest renames the hub's history below the base, new name to old.
    hub_renamings: Vec<HashMap<CanonicalOp, CanonicalOp>>,
    /// What they drop, in node names now.
    dropped: HashSet<CanonicalOp>,
    /// Node space now to node space then.
    renaming: HashMap<CanonicalOp, Vec<CanonicalOp>>,
    /// This copy's private bindings before the trim removes their shared basis.
    own: std::collections::BTreeMap<jj_lib::ref_name::WorkspaceNameBuf, jj_lib::backend::CommitId>,
    /// Whether the op heads moved there, this node holding them.
    switched: bool,
    /// `pending`, as the records name the history.
    pending: Record,
    /// The local operation each local one becomes.
    locals: HashMap<LocalOp, Vec<LocalOp>>,
    /// The op heads `locals` was worked out from, sorted.
    heads: Vec<LocalOp>,
    /// The operation the hub accepted that this machine fetches from, as the records name
    /// it: what it became, or, if dropped, the first of what was below it.
    base: Option<HubOp>,
    /// The digests of the records in custody that these records lack, whose drops are among
    /// `pending`.
    lost_custody: HashSet<RecordDigest>,
}

/// The file in the musubi directory where the sync adapter keeps the head this machine
/// pushed last, once it has learned that the hub took it.
pub const ACCEPTED_PUSH: &str = "accepted_push";

/// `ops` without duplicates, the first of each kept.
fn dedup<Op: Clone + Eq + std::hash::Hash>(ops: impl IntoIterator<Item = Op>) -> Vec<Op> {
    let mut seen = HashSet::new();
    ops.into_iter()
        .filter(|op| seen.insert(op.clone()))
        .collect()
}

impl Records {
    /// Adds a step, a renaming with what it dropped and the sources it established, to what
    /// the steps compose, leaving its counting to the caller. Each lookup composes them, so
    /// that adding one costs only its own size, as reading them all does.
    fn compose(&mut self, (step, dropped, sources): Step) {
        debug_assert!(
            step.values()
                .flatten()
                .all(|op| !self.superseded.contains_key(op) && !step.contains_key(op)),
            "a renaming names as what an operation became one superseded"
        );
        self.superseded.extend(step);
        self.dropped.extend(dropped);
        self.sources.extend(sources);
        self.forget_normalizer();
    }

    /// Forgets the normalizer, what this node drops having changed; the facts it read stay.
    fn forget_normalizer(&mut self) {
        self.normal
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .normalizer = None;
        // The hub-to-node translation names as this node drops too.
        *self
            .to_node
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = None;
    }

    fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            prefix: self.prefix.clone(),
            applied: self.applied.clone(),
            digests: self.digests.clone(),
            earlier: self.earlier.clone(),
            custody: self.custody.clone(),
            fresh: self.fresh,
            pending: self.pending.clone(),
            fixup: self.fixup.clone(),
            fixup_written: self.fixup_written,
            fixup_from: self.fixup_from.clone(),
            realign: self.realign.clone(),
            steps: self.steps,
        }
    }

    fn restore(&mut self, checkpoint: Checkpoint) {
        let Checkpoint {
            prefix,
            applied,
            digests,
            earlier,
            custody,
            fresh,
            pending,
            fixup,
            fixup_written,
            fixup_from,
            realign,
            steps,
        } = checkpoint;
        self.prefix = prefix;
        self.applied = applied;
        self.digests = digests;
        self.earlier = earlier;
        self.custody = custody;
        self.fresh = fresh;
        self.pending = pending;
        self.fixup = fixup;
        self.fixup_written = fixup_written;
        self.fixup_from = fixup_from;
        self.realign = realign;
        self.steps = steps;
        self.forget_normalizer();
    }

    /// What `op` is now ([`current`]).
    fn current(&self, op: &CanonicalOp) -> Vec<CanonicalOp> {
        current(&self.superseded, op)
    }

    pub(super) fn source(&self, local: &LocalOp) -> Option<&CanonicalOp> {
        self.sources
            .get(local)
            .or_else(|| self.realign.as_ref()?.canonical.get(local))
    }

    /// [`NodeRepo::held_records`].
    fn held(&self, prefix: &RecordPrefix) -> Option<(RecordPrefix, Vec<Record>)> {
        let mut digest = &prefix.digest;
        let mut earlier = vec![];
        let (base, mut held) = loop {
            if let Some(count) = self.digests.iter().position(|held| held == digest) {
                break (self.prefix.clone(), self.applied[..count].to_vec());
            }
            if *digest == RecordDigest::root() {
                break (RecordPrefix::none(), vec![]);
            }
            let record = self.earlier.iter().find(|e| e.digest == *digest)?;
            earlier.push(record.record.clone());
            digest = &record.before;
        };
        held.extend(earlier.into_iter().rev());
        (base.count + held.len() as u64 == prefix.count).then_some((base, held))
    }

    /// Makes `records`, after the first ones `prefix` stands for, the records this node holds,
    /// keeping those it no longer holds among `earlier`: the hub may have pruned them since
    /// it reported them, and it can take the hub's records from them ([`Self::held`]).
    fn hold(&mut self, prefix: RecordPrefix, records: Vec<Record>) {
        let digests = digests(&prefix.digest, &records);
        let holds: HashSet<&RecordDigest> = digests.iter().collect();
        let mut kept: HashSet<RecordDigest> = self
            .earlier
            .iter()
            .map(|e| e.digest.clone())
            .filter(|digest| !holds.contains(digest))
            .collect();
        self.earlier.retain(|e| kept.contains(&e.digest));
        for (k, record) in self.applied.iter().enumerate() {
            let digest = &self.digests[k + 1];
            if !holds.contains(digest) && kept.insert(digest.clone()) {
                self.earlier.push(Earlier {
                    digest: digest.clone(),
                    before: self.digests[k].clone(),
                    record: record.clone(),
                });
            }
        }
        drop(holds);
        self.digests = digests;
        self.prefix = prefix;
        self.applied = records;
        self.forget_normalizer();
        // Those after a prefix known only by its count and digest that it no longer holds, it
        // can't find again.
        let lost: HashSet<RecordDigest> = self
            .earlier
            .iter()
            .filter(|e| !self.reaches(&e.digest))
            .map(|e| e.digest.clone())
            .collect();
        self.earlier.retain(|e| !lost.contains(&e.digest));
    }

    /// Whether the records `digest` is the digest of, back through `earlier`, start with none
    /// or with records this node holds.
    fn reaches<'a>(&'a self, mut digest: &'a RecordDigest) -> bool {
        loop {
            if *digest == RecordDigest::root() || self.digests.contains(digest) {
                return true;
            }
            match self.earlier.iter().find(|e| e.digest == *digest) {
                Some(e) => digest = &e.before,
                None => return false,
            }
        }
    }
}

/// The digest of each first so many of `records`, after the records `start` is the digest of.
fn digests(start: &RecordDigest, records: &[Record]) -> Vec<RecordDigest> {
    let mut digests = vec![start.clone()];
    for record in records {
        let digest = digests.last().expect("the root digest").then(record);
        digests.push(digest);
    }
    digests
}

impl NodeRepo {
    /// The first of the hub's records this node took, known only by their count and digest.
    pub fn record_prefix(&self) -> &RecordPrefix {
        &self.records.prefix
    }

    /// The hub's records this node took after [`Self::record_prefix`], oldest first.
    pub fn applied_records(&self) -> &[Record] {
        &self.records.applied
    }

    /// How many records this node took, and their digest.
    pub fn record_state(&self) -> (u64, RecordDigest) {
        let records = &self.records;
        (
            records.prefix.count + records.applied.len() as u64,
            records.digests.last().expect("the prefix's digest").clone(),
        )
    }

    /// The records that `prefix` counts and digests, as this node took them, after the first
    /// ones, known only by their count and digest, that it holds: the first of those it holds
    /// now, or of records it held before. `None` if it never held them, or knows them only by
    /// a count and digest it no longer holds.
    pub fn held_records(&self, prefix: &RecordPrefix) -> Option<(RecordPrefix, Vec<Record>)> {
        self.records.held(prefix)
    }

    /// Whether this node has nothing of the hive's: it joined on the root, and has taken no
    /// records, pushed nothing and realized nothing since. Only such a node may take the hub's
    /// records from those it pruned.
    pub fn is_fresh(&self) -> bool {
        let records = &self.records;
        records.fresh && records.prefix.count == 0 && records.applied.is_empty()
    }

    /// Says this node is about to push to the hub, or to realize one of its operations: it
    /// is no longer [fresh](Self::is_fresh).
    pub fn share(&mut self) -> Result<(), NodeError> {
        if !self.records.fresh {
            return Ok(());
        }
        self.records.fresh = false;
        self.save_records()
    }

    /// Says this node, joining on the root, has nothing of the hive's yet, if it has taken
    /// no records.
    pub(super) fn mark_fresh(&mut self) -> Result<(), NodeError> {
        let records = &self.records;
        if records.fresh || records.prefix.count > 0 || !records.applied.is_empty() {
            return Ok(());
        }
        self.records.fresh = true;
        self.save_records()
    }

    /// What this node dropped that the hub hasn't, as the hub names it.
    pub fn pending_drops(&self) -> &Record {
        &self.records.pending
    }

    /// Names this node's pending drops as the hub's history does, `known` being that history
    /// as this node has it: the canonical ancestors of the hub's head it knows. A pending drop
    /// that is another version of one of them, the same original under a name another record
    /// gave it (a contraction keeps the original identity), becomes that one, for a drop is
    /// of the original. Records the hub went back past name what they dropped as they did,
    /// and another machine may then restore it under its name from before them: published
    /// under the other name, the drop would miss it, and the hub's history would bring it back
    /// here. A pending drop whose body this node lacks, or with no version in `known`, keeps
    /// its name. Returns whether any changed.
    ///
    /// Only the pending drops change: the records this node holds are the hub's, and the
    /// fix-up restores a head of this machine's history, which it drops nothing of. Records
    /// being taken whose op heads haven't moved are worked out again, from the pending drops as
    /// they are now; once the op heads have moved, the pending drops are what those records
    /// left, and their moves go on as recorded. Fails if `known` has two versions of an
    /// original a pending drop is, as no history can, rather than choose one.
    pub fn name_pending_as(&mut self, known: &[CanonicalOp]) -> Result<bool, NodeError> {
        let store = &self.canonical;
        // The original each pending drop is, where its body is here to say.
        let mut originals: HashMap<&CanonicalOp, OperationId> = HashMap::new();
        for op in self.records.pending.ops() {
            if store.has_operation(&op.0) {
                originals.insert(&op.0, store.original_id(&op.0)?);
            }
        }
        if originals.is_empty() {
            return Ok(false);
        }
        let wanted: HashSet<&OperationId> = originals.values().collect();
        // The version of each in the hub's history, of which it has one at most.
        let mut versions: HashMap<OperationId, &CanonicalOp> = HashMap::new();
        for op in known.iter().filter(|op| store.has_operation(op)) {
            let original = store.original_id(op)?;
            if !wanted.contains(&original) {
                continue;
            }
            match versions.get(&original) {
                Some(other) if *other != op => {
                    return Err(CanonicalError::MalformedOperation(op.0.hex()).into());
                }
                Some(_) => {}
                None => {
                    versions.insert(original, op);
                }
            }
        }
        let named = Record::new(self.records.pending.ops().iter().map(|op| {
            match originals
                .get(&op.0)
                .and_then(|original| versions.get(original))
            {
                Some(version) => HubOp((*version).clone()),
                None => op.clone(),
            }
        }));
        if named == self.records.pending {
            return Ok(false);
        }
        let checkpoint = self.records.checkpoint();
        self.records.pending = named;
        if let Err(err) = self.save_records() {
            self.records.restore(checkpoint);
            return Err(err);
        }
        self.forget_to_node();
        if self
            .records
            .taking
            .as_ref()
            .is_some_and(|taking| !taking.switched)
        {
            self.records.taking = None;
        }
        Ok(true)
    }

    /// What `op`, a name from before a renaming here, or none, is now in node space.
    pub fn current(&self, op: &CanonicalOp) -> Result<Vec<NodeOp>, NodeError> {
        Ok(self.current_ids(op)?.into_iter().map(NodeOp).collect())
    }

    /// What `op` is now in node space: what the renamings here made of it, each as this
    /// node's history names it ([`Normalizer`]), so that one of another history, as one
    /// imported since or one a `jj` command wrote on an old one, above another version of
    /// something this node dropped, is named without it.
    pub(super) fn current_ids(&self, op: &CanonicalOp) -> Result<Vec<CanonicalOp>, NodeError> {
        let now = self.records.current(op);
        let mut normal = self
            .records
            .normal
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let Normal { facts, normalizer } = &mut *normal;
        if normalizer.is_none() {
            *normalizer = Some(Normalizer::new(self.dropped_originals(facts, &[])?));
        }
        let normalizer = normalizer.as_mut().expect("made above");
        let mut names = vec![];
        for op in &now {
            names.extend(normalizer.names(&self.canonical, &self.presences, facts, op)?);
        }
        Ok(dedup(names))
    }

    /// The originals of what this node drops: what the records it holds and held drop, what
    /// its renamings dropped, and its pending drops, with `extra`, where the store has them.
    /// Not records in custody: this node holds none of them.
    fn dropped_originals(
        &self,
        facts: &mut HashMap<CanonicalOp, Fact>,
        extra: &[CanonicalOp],
    ) -> Result<HashSet<OperationId>, NodeError> {
        let records = &self.records;
        let names = records
            .applied
            .iter()
            .chain(records.earlier.iter().map(|earlier| &earlier.record))
            .flat_map(Record::ops)
            .chain(records.pending.ops())
            .map(|op| &op.0)
            .chain(&records.dropped)
            .chain(extra);
        let mut originals = HashSet::new();
        for name in names {
            if self.canonical.has_operation(name) {
                originals.insert(fact(&self.canonical, facts, name)?.original);
            }
        }
        Ok(originals)
    }

    /// Whether this node dropped `op`, a hub name: what it has yet to publish, or what records
    /// it is taking or took drop.
    pub fn is_dropped(&self, op: &HubOp) -> bool {
        let records = &self.records;
        let pending = match &records.taking {
            Some(taking) => &taking.pending,
            None => &records.pending,
        };
        pending.contains(op)
            || records.dropped.contains(&op.0)
            || records.applied.iter().any(|record| record.contains(op))
    }

    /// What `op`, a hub name, is in node space: the hub's history with what this node has yet
    /// to publish dropped too.
    pub fn to_node(&self, op: &HubOp) -> Result<Vec<NodeOp>, NodeError> {
        Ok(self.to_node_ids(&op.0)?.into_iter().map(NodeOp).collect())
    }

    fn to_node_ids(&self, op: &CanonicalOp) -> Result<Vec<CanonicalOp>, NodeError> {
        let pending = match &self.records.taking {
            Some(taking) => &taking.pending,
            None => &self.records.pending,
        };
        if pending.is_empty() {
            return self.current_ids(op);
        }
        // As `current_ids` names, but without every version of the pending drops too, by their
        // originals: those of records being taken that the hub lost may be named otherwise
        // than the hub's history names them.
        let now = self.records.current(op);
        let names: Vec<CanonicalOp> = pending.ops().iter().map(|op| op.0.clone()).collect();
        // Always this one, then `normal`.
        let mut to_node = self
            .records
            .to_node
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut normal = self
            .records
            .normal
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let facts = &mut normal.facts;
        if to_node.is_none() {
            *to_node = Some(Normalizer::new(self.dropped_originals(facts, &names)?));
        }
        let normalizer = to_node.as_mut().expect("made above");
        let mut images = vec![];
        for op in &now {
            match normalizer.complete_names(&self.canonical, &self.presences, facts, op)? {
                Some(named) => images.extend(named),
                // Below which the store lacks something: as the pending drops' names alone
                // drop, worked out afresh and kept nowhere, so that what arrives later counts.
                None => images.extend(
                    Contraction::new(&self.canonical, names.iter().cloned())?
                        .sharing(self.presences.clone())
                        .images(&self.canonical, op)?,
                ),
            }
        }
        Ok(dedup(images))
    }

    /// The hub's names for what this node's pending drops renamed here, by their names here.
    /// Noticing a drop renames what it keeps above it at once, in node space, but the hub
    /// renames nothing until the drop reaches it. So a later drop of one of those must name it
    /// as the hub does. These are the operations below `base`, a hub name, above the lowest
    /// pending drop, and any other hub operation translated to node space since, as one
    /// fetched above `base`.
    fn hub_names(
        &self,
        base: &CanonicalOp,
    ) -> Result<HashMap<CanonicalOp, CanonicalOp>, NodeError> {
        let pending = match &self.records.taking {
            Some(taking) => &taking.pending,
            None => &self.records.pending,
        };
        // The store may lack a drop, as one the hub's history no longer has.
        let mut floor: Option<u64> = None;
        for op in pending.ops() {
            if self.canonical.has_operation(&op.0) {
                let generation = self.canonical.generation(&op.0)?;
                floor = Some(floor.map_or(generation, |floor| floor.min(generation)));
            }
        }
        let Some(floor) = floor else {
            return Ok(HashMap::new());
        };
        let below = |op: &CanonicalOp| {
            self.canonical
                .generation(op)
                .is_ok_and(|generation| generation <= floor)
        };
        let mut names = HashMap::new();
        // Descendants first, so that checking the first one's origins covers the rest.
        let hubs = self
            .canonical
            .ancestors_until(std::slice::from_ref(base), below)?;
        for hub in hubs.into_iter().rev() {
            if pending.contains(&HubOp(hub.clone())) {
                continue;
            }
            if let [node] = self.to_node_ids(&hub)?.as_slice()
                && *node != hub
            {
                names.insert(node.clone(), hub);
            }
        }
        let to_node = self
            .records
            .to_node
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some(to_node) = to_node.as_ref() {
            for (hub, node, dropped) in to_node.worked_out() {
                if let [node] = node.as_slice()
                    && !dropped
                {
                    names.entry(node.clone()).or_insert_with(|| hub.clone());
                }
            }
        }
        Ok(names)
    }

    /// Forgets the hub-to-node translation worked out so far, `pending` having changed.
    fn forget_to_node(&mut self) {
        *self
            .records
            .to_node
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = None;
        self.records.forget_normalizer();
    }

    pub(super) fn own_before_taking(
        &self,
    ) -> Option<
        &std::collections::BTreeMap<jj_lib::ref_name::WorkspaceNameBuf, jj_lib::backend::CommitId>,
    > {
        self.records
            .taking
            .as_ref()
            .filter(|taking| !taking.switched)
            .map(|taking| &taking.own)
    }

    /// Forgets what is remembered by local operation id, which a rewrite of local
    /// operations makes stale.
    fn forget_local_caches(&mut self) {
        self.last_realized = None;
        self.last_own = None;
        self.prepared = None;
        self.heads_mapped = false;
        self.join_ancestors = None;
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use std::collections::BTreeMap;
    use std::fs;

    use hegel::TestCase;
    use hegel::generators as gs;
    use jj_lib::content_hash::blake2b_hash;

    use super::storage::digest_hex;
    use super::storage::format_hub_renamings;
    use super::storage::format_step;
    use super::storage::parse_hub_renamings;
    use super::storage::parse_steps;
    use super::*;
    use crate::translation_map::ID_HEX_LEN;
    use jj_lib::op_store::Operation as StoreOperation;

    fn id(byte: u8) -> CanonicalOp {
        CanonicalOp(OperationId::new(vec![byte; 64]))
    }

    /// A node finds every first so many of every list of records it has held, from those it
    /// holds now and those it held before, by their count and digest; and nothing else.
    #[test]
    fn a_node_finds_the_records_it_held() {
        let record = |byte: u8| Record::new([HubOp(id(byte))]);
        let [a, b, c, d, x] = [1, 2, 3, 4, 5].map(record);
        let state = |records: &[Record]| RecordPrefix {
            count: records.len() as u64,
            digest: RecordDigest::of(records),
        };
        let held = |records: &Records, list: &[Record]| records.held(&state(list));
        let whole = |list: &[Record]| Some((RecordPrefix::none(), list.to_vec()));
        let mut records = Records {
            digests: vec![RecordDigest::root()],
            ..Records::default()
        };
        let lists = [
            vec![a.clone(), b.clone(), c.clone()],
            vec![a.clone()],
            vec![a.clone(), x.clone()],
            vec![a.clone(), b.clone(), c.clone(), d.clone()],
            vec![],
        ];
        for (taken, list) in lists.iter().enumerate() {
            records.hold(RecordPrefix::none(), list.clone());
            for list in &lists[..=taken] {
                for count in 0..=list.len() {
                    assert_eq!(held(&records, &list[..count]), whole(&list[..count]));
                }
            }
            // Each record it held, kept once, and none it holds now.
            assert_eq!(records.earlier.len(), [0, 2, 2, 1, 5][taken]);
        }
        assert_eq!(held(&records, std::slice::from_ref(&b)), None);
        assert_eq!(held(&records, &[a.clone(), c.clone()]), None);
        // A digest it holds, but not of as many records.
        let mut wrong = state(&[a.clone(), b]);
        wrong.count = 3;
        assert_eq!(records.held(&wrong), None);
        // After records it knows only by their count and digest, those first.
        let base = state(&[x.clone(), d.clone()]);
        records.hold(base.clone(), vec![a.clone()]);
        let mut after = state(&[x, d, a.clone()]);
        assert_eq!(records.held(&after), Some((base.clone(), vec![a])));
        assert_eq!(records.held(&base), Some((base, vec![])));
        after.count = 1;
        assert_eq!(records.held(&after), None);
        // Records after a prefix it no longer holds, it no longer keeps.
        after.count = 3;
        records.hold(RecordPrefix::none(), vec![]);
        assert_eq!(records.held(&after), None);
        assert_eq!(records.earlier.len(), 5);
        assert_eq!(held(&records, &lists[3]), whole(&lists[3]));
    }

    /// The logs' ids and digests are whole at the length jj's operation ids and record digests
    /// have.
    #[test]
    fn whole_ids_have_the_length_of_real_ones() {
        // As the op store makes an operation's id, and realizing one works it out.
        let op = OperationId::new(
            blake2b_hash(&StoreOperation::make_root(jj_lib::op_store::ViewId::new(
                vec![0; 64],
            )))
            .to_vec(),
        );
        assert_eq!(op.hex().len(), ID_HEX_LEN);
        assert_eq!(digest_hex(&RecordDigest::root()).len(), ID_HEX_LEN);
    }

    /// How many lines of `formatted` the first `written` bytes hold whole, every character of
    /// each there, its line end perhaps not.
    fn whole_lines(formatted: &str, written: usize) -> usize {
        formatted
            .match_indices('\n')
            .filter(|(at, _)| *at <= written)
            .count()
    }

    /// How much of `formatted` an append wrote: all of it, or as far as a crash cut it.
    fn written(tc: &TestCase, formatted: &str) -> usize {
        if tc.draw(gs::booleans()) {
            tc.draw(gs::integers::<usize>().max_value(formatted.len()))
        } else {
            formatted.len()
        }
    }

    /// Renamings appended, each whole or cut anywhere as a crash leaves the end of an append,
    /// with more appended after: a line torn names nothing, the whole ones are read, a
    /// number's last block counting, and a block that lacks a line is known to.
    #[hegel::test(test_cases = 200)]
    fn torn_steps_lose_only_themselves(tc: TestCase) {
        let appends = tc.draw(gs::integers::<u8>().max_value(4));
        let (mut text, mut expected) = (String::new(), BTreeMap::<usize, Option<Step>>::new());
        for a in 0..appends {
            let number = tc.draw(gs::integers::<usize>().min_value(1).max_value(3));
            let (mut step, mut dropped) = (HashMap::new(), HashSet::new());
            for o in 0..tc.draw(gs::integers::<u8>().max_value(3)) {
                let old = id(16 * a + o);
                let images = tc.draw(gs::integers::<u8>().max_value(2));
                step.insert(
                    old.clone(),
                    (0..images).map(|i| id(200 + 4 * o + i)).collect(),
                );
                if tc.draw(gs::booleans()) {
                    dropped.insert(old);
                }
            }
            let sources: HashMap<LocalOp, CanonicalOp> = (0..tc
                .draw(gs::integers::<u8>().max_value(3)))
                .map(|o| (LocalOp(id(150 + 4 * a + o).0), id(230 + o)))
                .collect();
            let formatted = format_step(number, &step, &dropped, &sources);
            // The empty line that starts the append, the number, then each operation's.
            let mut lines: Vec<Option<(&CanonicalOp, Option<&CanonicalOp>)>> = vec![None, None];
            for (old, new) in &step {
                if new.is_empty() {
                    lines.push(Some((old, None)));
                }
                lines.extend(new.iter().map(|op| Some((old, Some(op)))));
            }
            let alias_start = lines.len();
            lines.extend(sources.iter().map(|_| None));
            let written = written(&tc, &formatted);
            let whole = whole_lines(&formatted, written);
            if whole >= 2 {
                let (mut block, mut drops, mut aliases) = Step::default();
                for (old, new) in lines[2..whole.min(alias_start)].iter().flatten() {
                    let became = block.entry((*old).clone()).or_insert_with(|| {
                        if dropped.contains(*old) {
                            drops.push((*old).clone());
                        }
                        vec![]
                    });
                    became.extend(new.cloned());
                }
                aliases.extend(
                    sources
                        .iter()
                        .take(whole.saturating_sub(alias_start))
                        .map(|(local, canonical)| (local.clone(), canonical.clone())),
                );
                expected.insert(
                    number,
                    (whole == lines.len()).then_some((block, drops, aliases)),
                );
            }
            text.push_str(&formatted[..written]);
        }
        let read: BTreeMap<usize, Option<Step>> = parse_steps(&text)
            .into_iter()
            .map(|(number, block)| (number, block.whole()))
            .collect();
        assert_eq!(read, expected);
    }

    /// A line of the renamings log: its record's digest, then its pair, or for the record's
    /// line, how many pairs follow.
    type RenamingLine<'a> = (String, Result<(&'a CanonicalOp, &'a CanonicalOp), usize>);

    /// How records renamed the hub's history, appended, each whole or cut anywhere as a crash
    /// leaves the end of an append, with more appended after: a line torn names nothing, the
    /// whole ones are read, a digest's last block counting, and a block that lacks a line is
    /// known to.
    #[hegel::test(test_cases = 200)]
    fn torn_hub_renamings_lose_only_themselves(tc: TestCase) {
        let records: Vec<Record> = (0..tc.draw(gs::integers::<u8>().max_value(3)))
            .map(|r| Record::new([HubOp(id(100 + r))]))
            .collect();
        let digests = digests(&RecordDigest::root(), &records);
        let (mut text, mut expected) = (String::new(), HashMap::new());
        for a in 0..tc.draw(gs::integers::<u8>().max_value(4)) {
            let from = tc.draw(gs::integers::<usize>().max_value(records.len()));
            let renamings: Vec<HashMap<CanonicalOp, CanonicalOp>> = (from..records.len())
                .map(|r| {
                    (0..tc.draw(gs::integers::<u8>().max_value(2)))
                        .map(|n| (id(16 * a + 4 * r as u8 + n), id(200 + n)))
                        .collect()
                })
                .collect();
            let formatted = format_hub_renamings(&RecordDigest::root(), &records, from, &renamings);
            // The empty line that starts the append, then each record's digest, with how many
            // pairs follow, and its pairs.
            let mut lines: Vec<RenamingLine> = vec![(String::new(), Err(0))];
            for (k, renaming) in renamings.iter().enumerate() {
                let digest = digest_hex(&digests[from + k + 1]);
                lines.push((digest.clone(), Err(renaming.len())));
                lines.extend(renaming.iter().map(|pair| (digest.clone(), Ok(pair))));
            }
            let written = written(&tc, &formatted);
            for (digest, line) in &lines[1..whole_lines(&formatted, written)] {
                match line {
                    Err(count) => {
                        expected.insert(digest.clone(), (HashMap::new(), *count));
                    }
                    Ok((new, old)) => {
                        let (block, _) = expected.get_mut(digest).unwrap();
                        block.insert((*new).clone(), (*old).clone());
                    }
                }
            }
            text.push_str(&formatted[..written]);
        }
        let read: HashMap<String, Option<HashMap<CanonicalOp, CanonicalOp>>> =
            parse_hub_renamings(&text)
                .into_iter()
                .map(|(digest, block)| (digest, block.whole()))
                .collect();
        let expected: HashMap<String, Option<HashMap<CanonicalOp, CanonicalOp>>> = expected
            .into_iter()
            .map(|(digest, (block, count))| (digest, (block.len() == count).then_some(block)))
            .collect();
        assert_eq!(read, expected);
    }

    /// Renamings, each of what was current and to what was or what it made, composed as each
    /// lookup composes them: as composing each into every name before it would.
    #[hegel::test(test_cases = 200)]
    fn renamings_compose_on_lookup(tc: TestCase) {
        let mut records = Records::default();
        let mut eager: HashMap<CanonicalOp, Vec<CanonicalOp>> = HashMap::new();
        let mut current: Vec<u8> = (0..4).collect();
        let mut fresh = 4;
        for _ in 0..tc.draw(gs::integers::<u8>().max_value(4)) {
            let renamed: Vec<u8> = current
                .iter()
                .copied()
                .filter(|_| tc.draw(gs::booleans()))
                .collect();
            let mut kept: Vec<u8> = current
                .iter()
                .copied()
                .filter(|op| !renamed.contains(op))
                .collect();
            let mut step = HashMap::new();
            let mut made = vec![];
            for old in &renamed {
                let mut became = vec![];
                for _ in 0..tc.draw(gs::integers::<u8>().max_value(2)) {
                    if kept.is_empty() || tc.draw(gs::booleans()) {
                        became.push(fresh);
                        made.push(fresh);
                        fresh += 1;
                    } else {
                        let at = tc.draw(gs::integers::<usize>().max_value(kept.len() - 1));
                        became.push(kept[at]);
                    }
                }
                // As contraction's images, without duplicates.
                step.insert(id(*old), dedup(became.into_iter().map(id)));
            }
            for now in eager.values_mut() {
                *now = dedup(
                    std::mem::take(now)
                        .into_iter()
                        .flat_map(|op| step.get(&op).cloned().unwrap_or_else(|| vec![op])),
                );
            }
            eager.extend(step.clone());
            records.compose((step, vec![], HashMap::new()));
            kept.extend(made);
            current = kept;
        }
        for op in (0..fresh).map(id) {
            let expected = eager.get(&op).cloned().unwrap_or_else(|| vec![op.clone()]);
            assert_eq!(records.current(&op), expected, "{op:?}");
        }
    }

    /// Where the translation cache was lost, `map_exactly` maps the local operations as
    /// canonicalizing did, working their canonical forms out without storing them: here a
    /// merge with an operation from before the join, which canonicalizing leaves out, and an
    /// operation on it; but not a new one. It fails if what is from before the join stays
    /// unknown, as nothing above it is then mapped, and if a form it works out is stored.
    #[test]
    fn map_exactly_maps_a_lost_translation_as_canonicalizing_did() {
        let env = musubi_testutil::TestEnv::new();
        let repo = env.init_repo("alpha");
        let open = || NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
        let ops = repo.jj(&["op", "log", "--no-graph", "-T", r#"id ++ "\n""#]);
        let ops: Vec<&str> = ops.lines().collect();
        // Below the join point, the head.
        let before_join = ops[ops.len() - 2].to_owned();
        assert_ne!(before_join, ops[0]);
        open().create_join_operation("musubi: alpha joins").unwrap();
        repo.jj(&["bookmark", "create", "h", "-r", "@-"]);
        repo.jj(&[
            "--at-op",
            &before_join,
            "bookmark",
            "create",
            "w",
            "-r",
            "root()",
        ]);
        // Merges first.
        repo.jj(&["bookmark", "create", "m", "-r", "@-"]);
        let mut node = open();
        let head = node.merge_heads().unwrap();
        let canonical = node.canonicalize(&head).unwrap();
        let stored = node.canonical_store().operation_ids().unwrap();
        drop(node);
        fs::remove_file(repo.repo_path().join("musubi/translation")).unwrap();
        // One the hive lacks, whose canonical form is worked out but not stored.
        repo.jj(&["bookmark", "create", "n", "-r", "@-"]);
        let mut node = open();
        let heads = node.local_heads().unwrap();
        let (mapped, unmapped) = node.local_walk(&heads).unwrap();
        assert!(node.map_exactly(&mapped, &unmapped).unwrap());
        assert_eq!(node.canonical_of(&head), Some(canonical));
        assert_eq!(node.canonical_of(&heads[0]), None);
        assert_eq!(node.canonical_store().operation_ids().unwrap(), stored);
    }
}
