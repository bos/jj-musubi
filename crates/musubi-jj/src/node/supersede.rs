//! Replicated `jj op abandon` on a node (docs/internals/design.md, "Abandoning operations"):
//! the hub's records this node took and what it dropped beyond them, noticing an abandon,
//! rewriting local operations to match the hive's history, taking the hub's records, and the
//! fix-up.
//!
//! Three names can stand for one operation here. The hub's, as its records name its history
//! (*hub space*), which the protocol speaks in; this node's, with what it has yet to publish
//! dropped too (*node space*), which its local operations map to; and older names a record
//! has since superseded, which a `jj` command that loaded the repository before the record
//! still writes on. [`NodeRepo::to_node`] and [`NodeRepo::current`] translate them.

use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Write as _;
use std::fs;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;

use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::Operation as StoreOperation;
use jj_lib::op_store::OperationId;
use jj_lib::operation::Operation;
use jj_lib::ref_name::GitRefNameBuf;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use pollster::FutureExt as _;
use serde::Deserialize;
use serde::Serialize;

use super::CANONICAL_ATTRIBUTE;
use super::NodeError;
use super::NodeRepo;
use super::git;
use super::join::fingerprint;
use crate::canonical;
use crate::canonical::CanonicalError;
use crate::canonical::CanonicalStore;
use crate::canonical::Contraction;
use crate::canonical::current;
use crate::files;
use crate::hive_settings;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
use crate::presence::FORGET_AFTER_ATTRIBUTE;
use crate::presence::FORGET_ATTRIBUTE;
use crate::presence::Presence;
use crate::presence::WORK_ATTRIBUTE;
use crate::presence::format_forget_after;
use crate::records::HubOp;
use crate::records::Record;
use crate::records::RecordDigest;
use crate::records::RecordPrefix;
use crate::translation_map::ID_HEX_LEN;
use crate::translation_map::whole_id;

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

const RECORDS_FILE: &str = "records.json";
const STEPS_FILE: &str = "superseded";
const HUB_RENAMINGS_FILE: &str = "hub-renamings";

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
    /// Whether `realign`'s translations are in the translation cache, as this opened it.
    realign_mapped: bool,
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

/// [`Realign`] as `records.json` has it, in hex.
#[derive(Serialize, Deserialize)]
struct RealignFile {
    from: Vec<(String, Vec<String>)>,
    to: Vec<String>,
    canonical: Vec<(String, String)>,
}

impl Realign {
    fn to_file(&self) -> RealignFile {
        let hex = |ops: &[LocalOp]| ops.iter().map(|op| op.0.hex()).collect::<Vec<_>>();
        let mut from: Vec<(String, Vec<String>)> = self
            .from
            .iter()
            .map(|(old, new)| (old.0.hex(), hex(new)))
            .collect();
        from.sort();
        let mut canonical: Vec<(String, String)> = self
            .canonical
            .iter()
            .map(|(local, canonical)| (local.0.hex(), canonical.0.hex()))
            .collect();
        canonical.sort();
        RealignFile {
            from,
            to: hex(&self.to),
            canonical,
        }
    }

    fn from_file(path: &Path, file: &RealignFile) -> Result<Self, NodeError> {
        let ops = |hexes: &[String]| -> Result<Vec<LocalOp>, NodeError> {
            Ok(parse_ids(path, hexes)?.into_iter().map(LocalOp).collect())
        };
        let mut from = HashMap::new();
        for (old, new) in &file.from {
            from.insert(ops(std::slice::from_ref(old))?.swap_remove(0), ops(new)?);
        }
        let mut canonical = HashMap::new();
        for (local, op) in &file.canonical {
            let [local, op] = [local, op].map(|hex| parse_ids(path, std::slice::from_ref(hex)));
            canonical.insert(
                LocalOp(local?.swap_remove(0)),
                CanonicalOp(op?.swap_remove(0)),
            );
        }
        Ok(Self {
            from,
            to: ops(&file.to)?,
            canonical,
        })
    }
}

/// What a canonical operation is made of that naming it needs: its parents and its original.
/// Immutable, so kept whatever this node drops.
#[derive(Clone)]
struct Fact {
    parents: Vec<CanonicalOp>,
    original: OperationId,
}

/// The facts read so far, and the normalizer for what this node drops now, until that changes.
#[derive(Default)]
struct Normal {
    facts: HashMap<CanonicalOp, Fact>,
    normalizer: Option<Normalizer>,
}

/// Where a raw operation stands, given the originals a history drops.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Class {
    /// Neither it nor anything below it is a version of one.
    Same,
    /// A version of one.
    Drop,
    /// Something below it is.
    Changed,
}

/// Names raw operations as a history that drops `dropped`, originals, does: any operation
/// that is, or is above, another version of one of them, as another history names it,
/// becomes its contraction by every version of them below it. A contraction keeps the
/// original. On shared history with the received records retained, dropping the same
/// originals gives the hub's names; this does not reconstruct unowned missing ancestry.
/// A version of a dropped original becomes what its parents do.
struct Normalizer {
    dropped: HashSet<OperationId>,
    class: HashMap<CanonicalOp, Class>,
    /// Every operation classed as a version of one so far.
    drops: Vec<CanonicalOp>,
    /// The contraction by `drops`, made again when they grow: one that drops nothing below
    /// an operation names it as one that doesn't drop that at all.
    contraction: Option<Contraction>,
    /// What those made before it worked out, and whether each is dropped: still what this
    /// one works out, as every closure they worked out was whole when classed, and nothing
    /// found since is below it.
    worked: HashMap<CanonicalOp, (Vec<CanonicalOp>, bool)>,
}

fn fact(
    store: &CanonicalStore,
    facts: &mut HashMap<CanonicalOp, Fact>,
    op: &CanonicalOp,
) -> Result<Fact, NodeError> {
    if let Some(fact) = facts.get(op) {
        return Ok(fact.clone());
    }
    let (operation, original) = store.read_operation_and_original(op)?;
    let fact = Fact {
        parents: CanonicalOp::parents_of(&operation),
        original,
    };
    facts.insert(op.clone(), fact.clone());
    Ok(fact)
}

impl Normalizer {
    fn new(dropped: HashSet<OperationId>) -> Self {
        Self {
            dropped,
            class: HashMap::new(),
            drops: vec![],
            contraction: None,
            worked: HashMap::new(),
        }
    }

    /// What `op` is named as. Itself if nothing below it is a version of a dropped original,
    /// or if the store lacks something below it: then nothing is worked out, nor kept, so
    /// that what arrives later is looked at.
    fn names(
        &mut self,
        store: &CanonicalStore,
        presences: &Arc<canonical::PresenceMemo>,
        facts: &mut HashMap<CanonicalOp, Fact>,
        op: &CanonicalOp,
    ) -> Result<Vec<CanonicalOp>, NodeError> {
        Ok(self
            .complete_names(store, presences, facts, op)?
            .unwrap_or_else(|| vec![op.clone()]))
    }

    /// [`Self::names`], or none if the store lacks something below `op`.
    fn complete_names(
        &mut self,
        store: &CanonicalStore,
        presences: &Arc<canonical::PresenceMemo>,
        facts: &mut HashMap<CanonicalOp, Fact>,
        op: &CanonicalOp,
    ) -> Result<Option<Vec<CanonicalOp>>, NodeError> {
        if self.dropped.is_empty() {
            return Ok(Some(vec![op.clone()]));
        }
        match self.classify(store, facts, op)? {
            None => Ok(None),
            Some(Class::Same) => Ok(Some(vec![op.clone()])),
            Some(Class::Drop | Class::Changed) => {
                if let Some((images, _)) = self.worked.get(op) {
                    return Ok(Some(images.clone()));
                }
                if self.contraction.is_none() {
                    self.contraction = Some(
                        Contraction::new(store, self.drops.iter().cloned())?
                            .sharing(presences.clone()),
                    );
                }
                let contraction = self.contraction.as_mut().expect("made above");
                // Checks the whole history below it before writing any rewrite.
                Ok(Some(contraction.images(store, op)?))
            }
        }
    }

    /// What each operation worked out so far became, where that isn't just itself, and
    /// whether it is dropped.
    fn worked_out(&self) -> impl Iterator<Item = (&CanonicalOp, &Vec<CanonicalOp>, bool)> {
        self.worked
            .iter()
            .map(|(op, (images, dropped))| (op, images, *dropped))
            .chain(self.contraction.iter().flat_map(|contraction| {
                contraction
                    .images_so_far()
                    .iter()
                    .map(|(op, images)| (op, images, contraction.drops(op)))
            }))
    }

    /// Keeps what the contraction worked out, which a contraction by more drops is about to
    /// replace.
    fn retire(&mut self) {
        let Some(contraction) = self.contraction.take() else {
            return;
        };
        for (op, images) in contraction.into_images() {
            let dropped = self.class.get(&op) == Some(&Class::Drop);
            self.worked.insert(op, (images, dropped));
        }
    }

    /// The class of `op`, or none if the store lacks something below it. Looks only at what
    /// it hasn't classed yet.
    fn classify(
        &mut self,
        store: &CanonicalStore,
        facts: &mut HashMap<CanonicalOp, Fact>,
        op: &CanonicalOp,
    ) -> Result<Option<Class>, NodeError> {
        let root = store.root_operation_id();
        let mut incomplete: HashSet<CanonicalOp> = HashSet::new();
        // (operation, whether its parents have been pushed)
        let mut stack = vec![(op.clone(), false)];
        while let Some((id, expanded)) = stack.pop() {
            if self.class.contains_key(&id) || incomplete.contains(&id) {
                continue;
            }
            if id == *root {
                self.class.insert(id, Class::Same);
                continue;
            }
            if !store.has_operation(&id) {
                incomplete.insert(id);
                continue;
            }
            let fact = fact(store, facts, &id)?;
            if !expanded {
                stack.push((id, true));
                stack.extend(
                    fact.parents
                        .into_iter()
                        .filter(|p| !self.class.contains_key(p) && !incomplete.contains(p))
                        .map(|p| (p, false)),
                );
                continue;
            }
            if fact.parents.iter().any(|p| incomplete.contains(p)) {
                incomplete.insert(id);
                continue;
            }
            let class = if self.dropped.contains(&fact.original) {
                self.drops.push(id.clone());
                self.retire();
                Class::Drop
            } else if fact
                .parents
                .iter()
                .any(|p| self.class.get(p) != Some(&Class::Same))
            {
                Class::Changed
            } else {
                Class::Same
            };
            self.class.insert(id, class);
        }
        Ok(self.class.get(op).copied())
    }
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

#[derive(Default, Serialize, Deserialize)]
struct RecordsFile {
    /// The count and hex digest of `Records::prefix`, if it has any.
    #[serde(default)]
    prefix: Option<(u64, String)>,
    applied: Vec<Vec<String>>,
    pending: Vec<String>,
    fixup: Option<Fixup>,
    fixup_written: bool,
    #[serde(default)]
    fixup_from: Option<String>,
    #[serde(default)]
    moving: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    realign: Option<RealignFile>,
    /// How many renamings of the steps log count: one appended after is from a run cut short.
    #[serde(default)]
    steps: usize,
    #[serde(default)]
    fresh: bool,
    /// `Records::earlier`, each the hex digest of the records before it, and the record.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    earlier: Vec<(String, Vec<String>)>,
    /// `Records::custody`, as `earlier` is.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    custody: Vec<(String, Vec<String>)>,
}

/// What a fix-up writes: work by each copy whose latest work or forget-after an abandon
/// dropped, then the hive's settings as they were (docs/internals/design.md, "The fix-up").
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(super) struct Fixup {
    work: Vec<Work>,
    settings: Option<String>,
    #[serde(default)]
    expected: Option<Expectation>,
}

/// The expected value of each conflicted remote bookmark at the op head as the history before
/// the abandon had it ([`NodeRepo::expectation`]).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct Expectation {
    /// The op head's local operation, rewritten.
    at: String,
    /// Each one's git ref and value, as `git::expected_token` puts it.
    values: Vec<(String, String)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct Work {
    copy: String,
    forget_after: Option<String>,
    worked_at: Option<i64>,
    /// Whether a forget follows: whether the copy is forgotten at the op head the fix-up is
    /// written on. Decided as it starts, and kept, as by a fix-up that replaces it, since the
    /// fix-up's own work would make the copy present at the op head if it is written again
    /// after a crash.
    #[serde(default)]
    forgotten: Option<bool>,
}

fn hex_ids(record: &Record) -> Vec<String> {
    record.ops().iter().map(|op| op.0.0.hex()).collect()
}

fn parse_record(path: &Path, hexes: &[String]) -> Result<Record, NodeError> {
    Ok(Record::new(
        parse_ids(path, hexes)?
            .into_iter()
            .map(|op| HubOp(CanonicalOp(op))),
    ))
}

fn parse_ids(path: &Path, hexes: &[String]) -> Result<Vec<OperationId>, NodeError> {
    hexes
        .iter()
        .map(|hex| {
            OperationId::try_from_hex(hex).ok_or_else(|| NodeError::Io {
                path: path.to_owned(),
                source: std::io::Error::other(format!("bad operation id {hex}")),
            })
        })
        .collect()
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
    /// Reads what `musubi_dir` keeps.
    pub(super) fn load(musubi_dir: &Path) -> Result<Self, NodeError> {
        let path = musubi_dir.join(RECORDS_FILE);
        let file: RecordsFile = match fs::read(&path) {
            Ok(bytes) => serde_json::from_slice(&bytes).map_err(|err| NodeError::Io {
                path: path.clone(),
                source: std::io::Error::other(err),
            })?,
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => RecordsFile::default(),
            Err(source) => return Err(NodeError::Io { path, source }),
        };
        let applied = file
            .applied
            .iter()
            .map(|record| parse_record(&path, record))
            .collect::<Result<Vec<_>, _>>()?;
        let parse_digest = |hex: &str| {
            jj_lib::hex_util::decode_hex(hex)
                .map(|bytes| RecordDigest::from_bytes(&bytes))
                .ok_or_else(|| NodeError::Io {
                    path: path.clone(),
                    source: std::io::Error::other(format!("bad record digest {hex}")),
                })
        };
        let prefix = match &file.prefix {
            None => RecordPrefix::none(),
            Some((count, hex)) => RecordPrefix {
                count: *count,
                digest: parse_digest(hex)?,
            },
        };
        let entries = |entries: &[(String, Vec<String>)]| {
            entries
                .iter()
                .map(|(before, record)| {
                    let before = parse_digest(before)?;
                    let record = parse_record(&path, record)?;
                    Ok(Earlier {
                        digest: before.then(&record),
                        before,
                        record,
                    })
                })
                .collect::<Result<Vec<_>, NodeError>>()
        };
        let earlier = entries(&file.earlier)?;
        let custody = entries(&file.custody)?;
        let mut records = Self {
            digests: digests(&prefix.digest, &applied),
            prefix,
            applied,
            earlier,
            custody,
            fresh: file.fresh,
            pending: parse_record(&path, &file.pending)?,
            fixup: file.fixup,
            fixup_written: file.fixup_written,
            fixup_from: file
                .fixup_from
                .as_deref()
                .and_then(OperationId::try_from_hex)
                .map(CanonicalOp),
            moving: file.moving,
            realign: file
                .realign
                .as_ref()
                .map(|realign| Realign::from_file(&path, realign))
                .transpose()?,
            ..Self::default()
        };
        // Each log has every block that `records.json`, written after it, counts on, unless a
        // power cut lost some of it.
        let damaged = |path: PathBuf| {
            tracing::error!("{} lacks what records.json counts on", path.display());
            NodeError::DamagedLog
        };
        let path = musubi_dir.join(HUB_RENAMINGS_FILE);
        let mut renamings = parse_hub_renamings(&read_log(&path)?);
        records.hub_renamings = records.digests[1..]
            .iter()
            .map(|digest| {
                let block = renamings.remove(&digest_hex(digest));
                block.and_then(Block::whole)
            })
            .collect::<Option<_>>()
            .ok_or_else(|| damaged(path))?;
        let path = musubi_dir.join(STEPS_FILE);
        let mut steps = parse_steps(&read_log(&path)?);
        for number in 1..=file.steps {
            let Some(step) = steps.remove(&number).and_then(Block::whole) else {
                return Err(damaged(path));
            };
            records.compose(step);
            records.steps = number;
        }
        Ok(records)
    }

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
        self.sources.get(local)
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

/// The local operations a walk from the op heads met: those a canonical operation stands for,
/// with it, and the rest, read, parents first.
type LocalWalk = (Vec<(LocalOp, CanonicalOp)>, Vec<(LocalOp, StoreOperation)>);

/// A digest in hex, as the renamings log names records by.
fn digest_hex(digest: &RecordDigest) -> String {
    jj_lib::hex_util::encode_hex(digest.bytes())
}

/// Reads a file musubi appends to, or nothing if there is none.
fn read_log(path: &Path) -> Result<String, NodeError> {
    match fs::read(path) {
        Ok(bytes) => Ok(String::from_utf8_lossy(&bytes).into_owned()),
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(String::new()),
        Err(source) => Err(NodeError::Io {
            path: path.to_owned(),
            source,
        }),
    }
}

/// Appends `text` to the file at `path`, in one write.
fn append_log(path: &Path, text: &str) -> Result<(), NodeError> {
    let io = |source| NodeError::Io {
        path: path.to_owned(),
        source,
    };
    let mut file = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .map_err(io)?;
    file.write_all(text.as_bytes()).map_err(io)
}

/// The width of the numbers in a log's headers, so that a header torn in one names nothing.
const NUMBER_DIGITS: usize = 20;

/// A number in a log's header, whole.
fn whole_number(digits: &str) -> Option<usize> {
    (digits.len() == NUMBER_DIGITS && digits.bytes().all(|b| b.is_ascii_digit()))
        .then(|| digits.parse().ok())
        .flatten()
}

/// A block of a log as read: what its whole lines say, how many lines its header counts, and
/// how many it has.
#[derive(Debug, Default)]
struct Block<T> {
    read: T,
    count: usize,
    seen: usize,
}

impl<T> Block<T> {
    fn new(read: T, count: usize) -> Self {
        Self {
            read,
            count,
            seen: 0,
        }
    }

    /// What it says, if it has every line its header counts: a power cut can lose an append
    /// after the write that counts on it, or part of one.
    fn whole(self) -> Option<T> {
        (self.seen == self.count).then_some(self.read)
    }
}

/// How the records after the first `from` of `records`, which come after the records `start`
/// is the digest of, renamed the hub's history, as the renamings log has them: each a `record
/// <digest> <lines>` line, the digest being of the records up to it, then a `new old` line for
/// each operation. It starts a line, so that it stands apart from a line a crash tore before
/// it.
fn format_hub_renamings(
    start: &RecordDigest,
    records: &[Record],
    from: usize,
    renamings: &[HashMap<CanonicalOp, CanonicalOp>],
) -> String {
    let digests = digests(start, records);
    let mut text = String::from("\n");
    for (k, renaming) in renamings.iter().enumerate() {
        let digest = digest_hex(&digests[from + k + 1]);
        let lines = renaming.len();
        writeln!(text, "record {digest} {lines:0NUMBER_DIGITS$}").expect("writing to a String");
        for (new, old) in renaming {
            writeln!(text, "{} {}", new.0.hex(), old.0.hex()).expect("writing to a String");
        }
    }
    text
}

/// Reads the renamings log ([`format_hub_renamings`]), by digest: a block counts only with the
/// records it was written for, and the last block of a digest counts. Every line has one
/// length, so one torn anywhere, as a crash leaves the end of an append, names nothing.
fn parse_hub_renamings(text: &str) -> HashMap<String, Block<HashMap<CanonicalOp, CanonicalOp>>> {
    let mut renamings = HashMap::new();
    let mut current: Option<String> = None;
    for line in text.lines() {
        if let Some(header) = line.strip_prefix("record ") {
            if let Some((digest, lines)) = header.split_once(' ')
                && digest.len() == ID_HEX_LEN
                && digest.bytes().all(|b| b.is_ascii_hexdigit())
                && let Some(lines) = whole_number(lines)
            {
                current = Some(digest.to_owned());
                renamings.insert(digest.to_owned(), Block::new(HashMap::new(), lines));
            }
            continue;
        }
        let block = current
            .as_ref()
            .and_then(|digest| renamings.get_mut(digest));
        if let (Some(block), Some((new, old))) = (block, line.split_once(' '))
            && let (Some(new), Some(old)) = (whole_id(new), whole_id(old))
        {
            block.read.insert(CanonicalOp(new), CanonicalOp(old));
            block.seen += 1;
        }
    }
    renamings
}

/// A renaming, and what it dropped.
type Step = (
    HashMap<CanonicalOp, Vec<CanonicalOp>>,
    Vec<CanonicalOp>,
    HashMap<LocalOp, CanonicalOp>,
);

/// Renaming `number`, which dropped `dropped`, as the steps log has it: a `step <number>
/// <lines>` line, then an `old new` line for each operation it superseded and each it became,
/// in order, or `old -` where it became none; a dropped operation's lines start with `-`. It
/// starts a line, so that it stands apart from a line a crash tore before it.
fn format_step(
    number: usize,
    step: &HashMap<CanonicalOp, Vec<CanonicalOp>>,
    dropped: &HashSet<CanonicalOp>,
    sources: &HashMap<LocalOp, CanonicalOp>,
) -> String {
    let lines: usize = step.values().map(|new| new.len().max(1)).sum::<usize>() + sources.len();
    let mut text = format!("\nstep {number:0NUMBER_DIGITS$} {lines:0NUMBER_DIGITS$}\n");
    for (old, new) in step {
        let mark = if dropped.contains(old) { "-" } else { "" };
        if new.is_empty() {
            writeln!(text, "{mark}{} -", old.0.hex()).expect("writing to a String");
        }
        for op in new {
            writeln!(text, "{mark}{} {}", old.0.hex(), op.0.hex()).expect("writing to a String");
        }
    }
    for (local, canonical) in sources {
        writeln!(text, "source {} {}", local.0.hex(), canonical.0.hex())
            .expect("writing to a String");
    }
    text
}

/// Reads the steps log ([`format_step`]), by number, the last block of a number counting.
/// Every line has one length, so one torn anywhere, as a crash leaves the end of an append,
/// names nothing.
fn parse_steps(text: &str) -> std::collections::BTreeMap<usize, Block<Step>> {
    let mut steps = std::collections::BTreeMap::new();
    let mut current = None;
    for line in text.lines() {
        if let Some(header) = line.strip_prefix("step ") {
            if let Some((number, lines)) = header.split_once(' ')
                && let (Some(number), Some(lines)) = (whole_number(number), whole_number(lines))
            {
                current = Some(number);
                steps.insert(number, Block::new(Step::default(), lines));
            }
            continue;
        }
        if let Some(pair) = line.strip_prefix("source ") {
            if let Some((local, canonical)) = pair.split_once(' ')
                && let (Some(local), Some(canonical)) = (whole_id(local), whole_id(canonical))
                && let Some(block) = current.and_then(|number| steps.get_mut(&number))
            {
                block.read.2.insert(LocalOp(local), CanonicalOp(canonical));
                block.seen += 1;
            }
            continue;
        }
        let (dropped, line) = match line.strip_prefix('-') {
            Some(line) => (true, line),
            None => (false, line),
        };
        let Some((old, new)) = line.split_once(' ') else {
            continue;
        };
        let new = match new {
            "-" => Some(None),
            hex => whole_id(hex).map(|op| Some(CanonicalOp(op))),
        };
        let block: Option<&mut Block<Step>> = current.and_then(|number| steps.get_mut(&number));
        if let (Some(block), Some(old), Some(new)) = (block, whole_id(old).map(CanonicalOp), new) {
            let (step, drops, _) = &mut block.read;
            let became = step.entry(old.clone()).or_insert_with(|| {
                if dropped {
                    drops.push(old);
                }
                vec![]
            });
            became.extend(new);
            block.seen += 1;
        }
    }
    steps
}

impl NodeRepo {
    fn records_path(&self) -> PathBuf {
        self.repo_path.join("musubi").join(RECORDS_FILE)
    }

    fn save_records(&self) -> Result<(), NodeError> {
        let records = &self.records;
        let prefix = &records.prefix;
        let file = RecordsFile {
            prefix: (prefix.count > 0).then(|| (prefix.count, digest_hex(&prefix.digest))),
            fresh: records.fresh,
            applied: records.applied.iter().map(hex_ids).collect(),
            pending: hex_ids(&records.pending),
            fixup: records.fixup.clone(),
            fixup_written: records.fixup_written,
            fixup_from: records.fixup_from.as_ref().map(|op| op.0.hex()),
            moving: records.moving,
            realign: records.realign.as_ref().map(Realign::to_file),
            steps: records.steps,
            earlier: records
                .earlier
                .iter()
                .map(|earlier| (digest_hex(&earlier.before), hex_ids(&earlier.record)))
                .collect(),
            custody: records
                .custody
                .iter()
                .map(|custody| (digest_hex(&custody.before), hex_ids(&custody.record)))
                .collect(),
        };
        let path = self.records_path();
        let bytes = serde_json::to_vec_pretty(&file).map_err(|err| NodeError::Io {
            path: path.clone(),
            source: std::io::Error::other(err),
        })?;
        files::replace(&path, &bytes).map_err(|source| NodeError::Io { path, source })
    }

    /// Records a renaming, which dropped `dropped`: appends it, in one write, and composes it.
    fn add_step(
        &mut self,
        step: HashMap<CanonicalOp, Vec<CanonicalOp>>,
        dropped: &HashSet<CanonicalOp>,
        counterparts: &HashMap<LocalOp, CanonicalOp>,
    ) -> Result<(), NodeError> {
        if let Some(step) = self.append_step(step, dropped, counterparts)? {
            self.records.compose(step);
            self.records.steps += 1;
        }
        Ok(())
    }

    /// Appends a renaming, which dropped `dropped`, to the steps log, in one write, as the
    /// next step, which `records.json` counts once saved. Returns it, as composed, unless it
    /// changes nothing.
    fn append_step(
        &self,
        step: HashMap<CanonicalOp, Vec<CanonicalOp>>,
        dropped: &HashSet<CanonicalOp>,
        counterparts: &HashMap<LocalOp, CanonicalOp>,
    ) -> Result<Option<Step>, NodeError> {
        let step: HashMap<CanonicalOp, Vec<CanonicalOp>> = step
            .into_iter()
            .filter(|(old, new)| new != std::slice::from_ref(old))
            .collect();
        let sources: HashMap<LocalOp, CanonicalOp> = counterparts
            .iter()
            .filter(|(_, old)| !dropped.contains(*old))
            .filter_map(|(source, old)| {
                let current = match step.get(old).map(Vec::as_slice) {
                    Some([current]) => current,
                    None => old,
                    Some(_) => return None,
                };
                (self.records.sources.get(source) != Some(current))
                    .then(|| (source.clone(), current.clone()))
            })
            .collect();
        if step.is_empty() && sources.is_empty() {
            return Ok(None);
        }
        let path = self.repo_path.join("musubi").join(STEPS_FILE);
        append_log(
            &path,
            &format_step(self.records.steps + 1, &step, dropped, &sources),
        )?;
        let dropped = step
            .keys()
            .filter(|old| dropped.contains(*old))
            .cloned()
            .collect();
        Ok(Some((step, dropped, sources)))
    }

    /// Appends how the records of `records`, after the records `start` is the digest of,
    /// from the `from`th on renamed the hub's history, in one write.
    fn write_hub_renamings(
        &self,
        start: &RecordDigest,
        records: &[Record],
        from: usize,
        renamings: &[HashMap<CanonicalOp, CanonicalOp>],
    ) -> Result<(), NodeError> {
        if renamings.is_empty() {
            return Ok(());
        }
        let path = self.repo_path.join("musubi").join(HUB_RENAMINGS_FILE);
        append_log(
            &path,
            &format_hub_renamings(start, records, from, renamings),
        )
    }

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

    /// The record state once the hub takes `record` after this node's records.
    pub fn record_state_with(&self, record: &Record) -> (u64, RecordDigest) {
        let (count, digest) = self.record_state();
        (count + 1, digest.then(record))
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

    /// The local operations reachable from `heads`: those the translation map, a join point
    /// or the history from before the join account for, where the walk stops, and the rest,
    /// parents first.
    fn local_walk(&self, heads: &[LocalOp]) -> Result<LocalWalk, NodeError> {
        let op_store = self.loader.op_store();
        let mut mapped = vec![];
        let mut unmapped = vec![];
        let mut seen = HashSet::new();
        // (operation, read, whether its parents were pushed)
        let mut stack: Vec<(LocalOp, Option<StoreOperation>)> =
            heads.iter().map(|h| (h.clone(), None)).collect();
        while let Some((id, read)) = stack.pop() {
            if let Some(op) = read {
                unmapped.push((id, op));
                continue;
            }
            if !seen.insert(id.clone()) || self.before_join.contains(&id) {
                continue;
            }
            if let Some(canonical) = self.canonical_of(&id) {
                // An alias establishes identity, not that a pending physical move finished.
                if !self.records.moving || self.records.source(&id).is_none() {
                    mapped.push((id, canonical));
                    continue;
                }
            }
            let op = op_store.read_operation(&id.0).block_on()?;
            if !op.metadata.attributes.contains_key(CANONICAL_ATTRIBUTE)
                && let Some(join) = self.joins.get(&fingerprint(&op))
            {
                mapped.push((id, join.clone()));
                continue;
            }
            let parents = LocalOp::parents_of(&op);
            stack.push((id, Some(op)));
            stack.extend(parents.into_iter().map(|p| (p, None)));
        }
        Ok((mapped, unmapped))
    }

    /// Whether every one of `bases` is below one of the canonical operations `mapped` has.
    fn reaches(
        &self,
        bases: &[CanonicalOp],
        mapped: &[(LocalOp, CanonicalOp)],
    ) -> Result<bool, NodeError> {
        for base in bases {
            let mut found = false;
            for (_, c) in mapped {
                if self.canonical.is_ancestor_of(base, c)? {
                    found = true;
                    break;
                }
            }
            if !found {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Maps what [`Self::local_walk`] found as canonicalizing would, where the hive has the
    /// canonical operations already: join points, and each of `unmapped`, parents first, with
    /// its canonical form (`exact_canonical`). Where the translation cache was lost, that is
    /// every local operation but jj's rewrites and those new since the last sync. Notes those
    /// from before the join too. Returns whether it mapped or noted any of `unmapped`.
    fn map_exactly(
        &mut self,
        mapped: &[(LocalOp, CanonicalOp)],
        unmapped: &[(LocalOp, StoreOperation)],
    ) -> Result<bool, NodeError> {
        for (local, canonical) in mapped {
            if self.canonical_of(local).is_none() {
                self.insert_map(local.clone(), canonical.clone())?;
            }
        }
        let mut found = false;
        for (id, op) in unmapped {
            match self.exact_canonical(id, op) {
                Ok(Some(canonical)) => {
                    self.insert_map(id.clone(), canonical)?;
                    found = true;
                }
                Ok(None) => found |= self.before_join.contains(id),
                // Canonicalizing refuses it too; matching it otherwise is left to the caller.
                Err(NodeError::Format { .. }) => {}
                Err(err) => return Err(err),
            }
        }
        Ok(found)
    }

    /// The operation the hub accepted that this machine fetches from (the sync adapter's
    /// `accepted_base`), a hub name, if it has one.
    fn stored_base(&self) -> Option<HubOp> {
        self.stored_op("accepted_base")
    }

    /// A hub name the sync adapter keeps in `name` in the musubi directory, if it keeps one.
    fn stored_op(&self, name: &str) -> Option<HubOp> {
        let hex = fs::read_to_string(self.repo_path.join("musubi").join(name)).ok()?;
        OperationId::try_from_hex(hex.trim()).map(|op| HubOp(CanonicalOp(op)))
    }

    /// Notices a `jj op abandon` of operations the hub accepted, before anything is
    /// canonicalized on what it rewrote, once for each set of op heads. Returns whether it
    /// noticed one. It must run before the op heads are read for anything else: jj rewrites
    /// every operation above the abandoned ones that isn't below them, putting on their parent
    /// even what was beside them, as a realization merged with them, and musubi puts that
    /// back, so an op head read before is one it no longer reaches.
    pub fn check_abandon(&mut self) -> Result<bool, NodeError> {
        let base = self.stored_base();
        // This machine's push the hub took, which the base may not have moved to yet, as where
        // a sync stopped right after the reply, or lost it: an abandon of it is one of an
        // operation the hub accepted all the same. Both it and the base outlive the hub going
        // back: another machine may have taken them (design.md, "Publishing an abandon").
        let pushed = self
            .stored_op(ACCEPTED_PUSH)
            .filter(|pushed| Some(pushed) != base.as_ref());
        let heads = self.local_heads()?;
        let checked = (heads, base, pushed);
        // A move that taking records left to do, as after an error, is done whether or not
        // the op heads changed since.
        if self.abandon_checked.as_ref() == Some(&checked) && self.records.realign.is_none() {
            return Ok(false);
        }
        let (heads, base, pushed) = checked;
        self.realign_heads(&heads)?;
        let mut noticed = false;
        for base in base.iter().chain(pushed.iter()) {
            if self.notice_abandon(base)? {
                noticed = true;
                break;
            }
        }
        // Only the op heads checked: a `jj op abandon` that moved them meanwhile, remembered as
        // checked, would go unnoticed, and the sync would fail for good. Moved here, they're
        // checked again next time.
        if noticed {
            self.abandon_noticed = true;
        } else {
            self.abandon_checked = Some((heads, base, pushed));
        }
        Ok(noticed)
    }

    /// Whether a local operation that stands for a canonical one, as `counterparts` say, is
    /// on parents that don't stand for that operation's parents.
    fn out_of_place(
        &self,
        counterparts: &HashMap<LocalOp, CanonicalOp>,
        unmapped: &[(LocalOp, StoreOperation)],
    ) -> Result<bool, NodeError> {
        for (id, op) in unmapped {
            let Some(c) = counterparts.get(id) else {
                continue;
            };
            let mut parents = vec![];
            for parent in LocalOp::parents_of(op) {
                if self.before_join.contains(&parent) {
                    continue;
                }
                // As the records name it now, as counterparts are named, and as canonicalizing
                // names a parent (`current_parents`).
                let now = match counterparts.get(&parent) {
                    Some(c) => vec![c.clone()],
                    None => match self.canonical_of(&parent) {
                        Some(c) => self.current_ids(&c)?,
                        None => return Ok(true),
                    },
                };
                for p in now {
                    if !parents.contains(&p) {
                        parents.push(p);
                    }
                }
            }
            if parents != self.canonical.parents(c)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Whether [`Self::check_abandon`] noticed a `jj op abandon` since this last said so, by
    /// whatever ran it: what was staged in the history before is stale.
    pub fn take_abandon_noticed(&mut self) -> bool {
        std::mem::take(&mut self.abandon_noticed)
    }

    /// Moves the op heads and the workspaces where records this node took move them, if a
    /// crash or an error stopped that, exactly as they would have, where the op heads are
    /// still those it moves from or to; and where others are beside some it moves from,
    /// those to what each becomes. Op heads a `jj` command made in place of all of them are
    /// left to [`Self::notice_abandon`] and canonicalizing, as any other, which find what the
    /// operations the move names stood for even where the translation cache lost it since.
    /// Then moves each op head that stands for an operation a renaming superseded to the
    /// local operation of what it became, as a crash between recording the renaming and
    /// moving the op heads leaves them.
    fn realign_heads(&mut self, heads: &[LocalOp]) -> Result<(), NodeError> {
        if let Some(realign) = self.records.realign.clone() {
            if !self.records.realign_mapped {
                for (local, canonical) in &realign.canonical {
                    if self.canonical_of(local).is_none() {
                        self.insert_map(local.clone(), canonical.clone())?;
                    }
                }
                self.records.realign_mapped = true;
            }
            let now: HashSet<&LocalOp> = heads.iter().collect();
            let to: HashSet<&LocalOp> = realign.to.iter().collect();
            let ours = now == realign.from.keys().collect() || now == to;
            // Op heads beside some it moves from, as a crash while moving them leaves them,
            // jj putting each new op head in before taking the old ones out, or a `jj`
            // command made: those it moves from move, each where it was to, and the rest stay.
            let beside = !ours && heads.iter().any(|head| realign.from.contains_key(head));
            if ours && now != to {
                self.publish_heads(heads, &realign.to)?;
            } else if beside {
                self.move_heads(heads, &realign.from, None, None)?;
            }
            let moved = ours || beside;
            if moved {
                self.forget_local_caches();
                self.move_workspaces(&HashMap::new())?;
            }
            // What the operations stood for is kept until none that a renaming superseded is
            // below the op heads, as one a `jj` command wrote on is until it is reparented,
            // canonicalized or not: the translation cache can be lost again before then.
            // Nothing moves from it again.
            let heads = if moved {
                self.local_heads()?
            } else {
                heads.to_vec()
            };
            let renamed = !self.superseded_below(&heads, &realign.canonical)?;
            // Written only where it changes: once, then once more, when it goes.
            let moving = !realign.from.is_empty() || !realign.to.is_empty();
            if renamed || moving {
                self.records.realign = (!renamed).then(|| Realign {
                    from: HashMap::new(),
                    to: vec![],
                    canonical: realign.canonical,
                });
                self.save_records()?;
            }
            if moved {
                return Ok(());
            }
        }
        let mut moved = false;
        for head in heads {
            let Some(canonical) = self.canonical_of(head) else {
                continue;
            };
            if let [now] = self.current_ids(&canonical)?.as_slice()
                && *now != canonical
                && let Some(local) = self.local_of(now)
            {
                self.loader
                    .op_heads_store()
                    .update_op_heads(std::slice::from_ref(&head.0), &local.0)
                    .block_on()?;
                moved = true;
            }
        }
        if moved {
            self.move_workspaces(&HashMap::new())?;
        }
        Ok(())
    }

    /// Notices a `jj op abandon` of operations the hub accepted: `base`, a hub name for an
    /// accepted operation here, is no longer below the op heads. Works out what was dropped,
    /// renames this node's history as contraction does, rewrites its local operations to
    /// match, and records the drops to publish, with the fix-up that goes first. Returns
    /// whether it noticed one.
    pub fn notice_abandon(&mut self, base: &HubOp) -> Result<bool, NodeError> {
        let root = self.canonical.root_operation_id().clone();
        let bases: Vec<CanonicalOp> = self
            .to_node_ids(&base.0)?
            .into_iter()
            .filter(|op| *op != root)
            .collect();
        if bases.is_empty() || bases.iter().any(|op| !self.canonical.has_operation(op)) {
            return Ok(false);
        }
        let heads = self.local_heads()?;
        let (mut mapped, mut unmapped) = self.local_walk(&heads)?;
        let mut reached = self.reaches(&bases, &mapped)?;
        // So too where the translation cache was lost: look again once what canonicalizes to
        // an operation the hive has is mapped, as canonicalizing would map it.
        if !reached && self.map_exactly(&mapped, &unmapped)? {
            (mapped, unmapped) = self.local_walk(&heads)?;
            reached = self.reaches(&bases, &mapped)?;
        }
        if reached && !self.records.moving {
            return Ok(false);
        }
        let frontier: Vec<CanonicalOp> = mapped.iter().map(|(_, c)| c.clone()).collect();
        // The history below what is intact stays; what was above it, and below the base, is
        // where the abandoned operations were, and what jj rewrote stands for.
        let mut kept: HashSet<CanonicalOp> = self
            .canonical
            .ancestors_until(&frontier, |_| false)?
            .into_iter()
            .collect();
        kept.insert(root.clone());
        kept.extend(frontier.iter().cloned());
        let region = self
            .canonical
            .ancestors_until(&bases, |op| kept.contains(op))?;
        let ambiguous = |this: &Self| -> Result<NodeError, NodeError> {
            for local in bases.iter().filter_map(|c| this.local_of(c)) {
                match this.loader.op_store().read_operation(&local.0).block_on() {
                    Ok(_) => return Ok(NodeError::AmbiguousAbandon(local.0.hex())),
                    Err(jj_lib::op_store::OpStoreError::ObjectNotFound { .. }) => {}
                    Err(err) => return Err(err.into()),
                }
            }
            Ok(NodeError::UnreachableHistory)
        };
        let mut surviving_fingerprints = HashSet::new();
        for (local, _) in &mapped {
            let op = self.loader.op_store().read_operation(&local.0).block_on()?;
            surviving_fingerprints.insert(fingerprint(&op));
        }
        let mut by_fingerprint: HashMap<String, Option<CanonicalOp>> = HashMap::new();
        for c in &region {
            let original = self.canonical.original_id(c)?;
            let fingerprints = self
                .originals
                .fingerprints(&original)
                .ok_or(NodeError::UnreachableHistory)?;
            for key in fingerprints {
                if surviving_fingerprints.contains(key) {
                    return Err(ambiguous(self)?);
                }
                by_fingerprint
                    .entry(key.clone())
                    .and_modify(|found| *found = None)
                    .or_insert_with(|| Some(c.clone()));
            }
        }
        // What each rewritten local operation stands for: the canonical operation a
        // realization names, or the one its old self, jj's, was.
        let mut counterparts: HashMap<LocalOp, CanonicalOp> = HashMap::new();
        for (id, op) in &unmapped {
            let named = self
                .records
                .source(id)
                .cloned()
                .or_else(|| {
                    op.metadata
                        .attributes
                        .get(CANONICAL_ATTRIBUTE)
                        .and_then(OperationId::try_from_hex)
                        .map(CanonicalOp)
                })
                .filter(|c| self.canonical.has_operation(c));
            let named = match named {
                Some(c) => match self.current_ids(&c)?.as_slice() {
                    [now] => Some(now.clone()),
                    _ => None,
                },
                None => None,
            };
            let fingerprint = by_fingerprint.get(&fingerprint(op));
            if named.is_none() && matches!(fingerprint, Some(None)) {
                return Err(ambiguous(self)?);
            }
            let found = named.or_else(|| fingerprint.cloned().flatten());
            if let Some(c) = found {
                counterparts.insert(id.clone(), c);
            }
        }
        // Dropped: what this machine had below the base, or below what jj rewrote, that no
        // operation it reaches stands for now.
        if self.records.moving {
            // A rewrite recorded before a restart: move the op heads it didn't.
            let mut nothing = Contraction::new(&self.canonical, std::iter::empty())?;
            let locals = self.rewrite_locals(&mut nothing, &heads, &counterparts, &unmapped)?;
            self.add_step(HashMap::new(), &HashSet::new(), &counterparts)?;
            self.save_records()?;
            self.move_heads(&heads, &locals, None, None)?;
            self.move_workspaces(&locals)?;
            self.records.moving = false;
            self.save_records()?;
            self.forget_local_caches();
            return Ok(true);
        }
        // jj op abandon rewrites what was above what it abandoned. Where nothing was, the
        // base is out of reach for some other reason, which this doesn't explain: dropping
        // everything below it would drop what the hive keeps.
        if unmapped.is_empty() {
            return Ok(false);
        }
        let stands: HashSet<CanonicalOp> = counterparts.values().cloned().collect();
        let mut tops: Vec<CanonicalOp> = bases.clone();
        tops.extend(stands.iter().cloned());
        let dropped: Vec<CanonicalOp> = self
            .canonical
            .ancestors_until(&tops, |op| kept.contains(op))?
            .into_iter()
            .filter(|op| !stands.contains(op))
            .collect();
        // Nothing dropped, though the base is out of reach: whatever jj abandoned came back,
        // as a command in a workspace whose working copy recorded an operation the abandon
        // rewrote brings it back with `snapshot.auto-update-stale`, and a later abandon moved
        // it, so that operations jj rewrote stand for the hive's elsewhere than the hive has
        // them. Put them back where the hive has them, publishing nothing, as jj keeps what
        // came back on one machine.
        if dropped.is_empty() && self.out_of_place(&counterparts, &unmapped)? {
            let mut nothing = Contraction::new(&self.canonical, std::iter::empty())?;
            let locals = self.rewrite_locals(&mut nothing, &heads, &counterparts, &unmapped)?;
            // As below: a restart partway resumes the move, and jj's rewrites keep the
            // identities established here.
            self.add_step(HashMap::new(), &HashSet::new(), &counterparts)?;
            self.records.moving = true;
            self.save_records()?;
            self.move_heads(&heads, &locals, None, None)?;
            self.move_workspaces(&locals)?;
            self.records.moving = false;
            self.save_records()?;
            self.forget_local_caches();
            return Ok(true);
        }
        if dropped.is_empty() {
            return Ok(false);
        }
        tracing::info!(
            "jj op abandon dropped {} operations the hive has",
            dropped.len()
        );
        let old_head = self.standing_for(&heads, &counterparts, &bases)?;
        let mut contraction = Contraction::new(&self.canonical, dropped.iter().cloned())?
            .sharing(self.presences.clone());
        let new_head = match &old_head {
            Some(old) => contraction.images(&self.canonical, old)?.first().cloned(),
            None => None,
        };
        let locals = self.rewrite_locals(&mut contraction, &heads, &counterparts, &unmapped)?;
        let hub_names = self.hub_names(&base.0)?;
        let pending = self.records.pending.ops().iter().cloned().chain(
            dropped
                .iter()
                .map(|op| HubOp(hub_names.get(op).cloned().unwrap_or_else(|| op.clone()))),
        );
        self.records.pending = Record::new(pending);
        self.forget_to_node();
        // Restoring the state from before the first abandon not yet published, the fix-up
        // covers every such abandon.
        let (from, expected) = match (&self.records.fixup_from, self.records.fixup_written) {
            (Some(from), false) => {
                let expected = self.records.fixup.as_ref().and_then(|f| f.expected.clone());
                let expected = expected.and_then(|mut expected| {
                    let at = LocalOp(OperationId::try_from_hex(&expected.at)?);
                    let now = self.rekeyed(&at, contraction.dropped(), &unmapped, &locals)?;
                    expected.at = now.0.hex();
                    Some(expected)
                });
                if let Some(fixup) = &mut self.records.fixup {
                    fixup.expected.clone_from(&expected);
                }
                (Some(from.clone()), expected)
            }
            _ => {
                let expected = match &old_head {
                    Some(old) => {
                        self.expectation(&heads, old, &counterparts, &unmapped, &locals)?
                    }
                    None => None,
                };
                (old_head, expected)
            }
        };
        if let (Some(old), Some(new)) = (from, new_head) {
            let mut fixup = self.fixup_between(&old, &new)?;
            fixup.expected = expected;
            // A fix-up this one replaces may have been written in part, before a crash: the
            // op head then has its work, so decide as it did.
            if let Some(replaced) = &self.records.fixup
                && !self.records.fixup_written
            {
                for work in &mut fixup.work {
                    work.forgotten = replaced
                        .work
                        .iter()
                        .find(|was| was.copy == work.copy)
                        .and_then(|was| was.forgotten);
                }
            }
            self.records.fixup = Some(fixup);
            self.records.fixup_written = false;
            self.records.fixup_from = Some(old);
        }
        // Recorded before the op heads move, so that a restart in between resumes the move; a
        // renaming appended without them doesn't count.
        let dropped_here = contraction.dropped().clone();
        self.add_step(contraction.into_images(), &dropped_here, &counterparts)?;
        self.records.moving = true;
        self.save_records()?;
        self.move_heads(&heads, &locals, None, None)?;
        self.move_workspaces(&locals)?;
        self.records.moving = false;
        self.save_records()?;
        self.forget_local_caches();
        Ok(true)
    }

    /// The canonical operation the first op head stood for before the abandon: its own, or
    /// the nearest one below it, where it is new. Where jj put a new one on history that was
    /// intact, below what it abandoned, one of `bases` that descends from that is nearer: the
    /// op heads descended from the base.
    fn standing_for(
        &self,
        heads: &[LocalOp],
        counterparts: &HashMap<LocalOp, CanonicalOp>,
        bases: &[CanonicalOp],
    ) -> Result<Option<CanonicalOp>, NodeError> {
        let mut stack: Vec<LocalOp> = heads.iter().take(1).cloned().collect();
        let mut seen = HashSet::new();
        while let Some(id) = stack.pop() {
            if !seen.insert(id.clone()) {
                continue;
            }
            if let Some(c) = counterparts.get(&id) {
                return Ok(Some(c.clone()));
            }
            if let Some(c) = self.canonical_of(&id) {
                for base in bases {
                    if *base != c && self.canonical.is_ancestor_of(&c, base)? {
                        return Ok(Some(base.clone()));
                    }
                }
                return Ok(Some(c));
            }
            let op = self.loader.op_store().read_operation(&id.0).block_on()?;
            stack.extend(LocalOp::parents_of(&op));
        }
        Ok(None)
    }

    /// The expected value of each conflicted remote bookmark at the first of `heads` as the
    /// history before the abandon had it, under the id of its rewrite in `locals`. The walk
    /// back through history takes each operation jj rewrote as the canonical operation it
    /// stands for, as `counterparts` has them, and goes from an operation new since, among
    /// `unmapped`, to `old`, what the head stood for, rather than to what jj put under it.
    fn expectation(
        &self,
        heads: &[LocalOp],
        old: &CanonicalOp,
        counterparts: &HashMap<LocalOp, CanonicalOp>,
        unmapped: &[(LocalOp, StoreOperation)],
        locals: &HashMap<LocalOp, Vec<LocalOp>>,
    ) -> Result<Option<Expectation>, NodeError> {
        let Some(head) = heads.first() else {
            return Ok(None);
        };
        let new: HashSet<&LocalOp> = unmapped
            .iter()
            .map(|(id, _)| id)
            .filter(|id| !counterparts.contains_key(*id))
            .collect();
        let old_op = self.canonical.load_operation(old)?;
        // The walk starts among local operations and goes on among canonical ones, from a
        // counterpart or through `old_op`, so an operation here may be either, and its id is
        // taken for a local one: `counterparts` and `new` hold local ones only, which a
        // canonical id matches only at the root, the same id in both stores, which neither
        // holds.
        let local = |op: &Operation| LocalOp(op.id().clone());
        let parents = |op: &Operation| -> Result<Option<Vec<Operation>>, NodeError> {
            if let Some(c) = counterparts.get(&local(op)) {
                return Ok(Some(
                    self.canonical.load_operation(c)?.parents().block_on()?,
                ));
            }
            if !new.contains(&local(op)) {
                return Ok(None);
            }
            let mut parents = vec![];
            let mut to_old = true;
            for parent in op.parents().block_on()? {
                if new.contains(&local(&parent)) || counterparts.contains_key(&local(&parent)) {
                    parents.push(parent);
                } else if std::mem::take(&mut to_old) {
                    parents.push(old_op.clone());
                }
            }
            Ok(Some(parents))
        };
        let roots = [
            self.root_op_id().0.clone(),
            self.canonical.root_operation_id().0.clone(),
        ];
        let history = git::History {
            known: &git::Expected::new(),
            roots: &roots,
            is_join: &|op| self.is_join_point(op),
            parents: &parents,
        };
        let op = self.loader.load_operation(&head.0).block_on()?;
        let values = git::expected_values(self.loader.store(), &op, &history)?;
        if values.is_empty() {
            return Ok(None);
        }
        let at = match locals.get(head).map(Vec::as_slice) {
            Some([now]) => now.clone(),
            Some(_) => return Ok(None),
            None => head.clone(),
        };
        Ok(Some(Expectation {
            at: at.0.hex(),
            values: values
                .into_iter()
                .map(|(name, value)| {
                    (
                        name.as_str().to_owned(),
                        git::expected_token(value.as_ref()),
                    )
                })
                .collect(),
        }))
    }

    /// What `at`, the op head a fix-up's expected values were worked out at, is after an
    /// abandon: jj's rewrite of it, among `unmapped`, as this machine rewrote that in `locals`;
    /// or itself, where neither touched it. None where the abandon dropped it, as `dropped`
    /// has the canonical operations, or made it several.
    fn rekeyed(
        &self,
        at: &LocalOp,
        dropped: &HashSet<CanonicalOp>,
        unmapped: &[(LocalOp, StoreOperation)],
        locals: &HashMap<LocalOp, Vec<LocalOp>>,
    ) -> Option<LocalOp> {
        let single = |id: &LocalOp| match locals.get(id).map(Vec::as_slice) {
            Some([now]) => Some(now.clone()),
            Some(_) => None,
            None => Some(id.clone()),
        };
        if locals.contains_key(at) {
            return single(at);
        }
        let op = self
            .loader
            .op_store()
            .read_operation(&at.0)
            .block_on()
            .ok()?;
        let print = fingerprint(&op);
        let mut rewrites = unmapped.iter().filter(|(_, op)| fingerprint(op) == print);
        match (rewrites.next(), rewrites.next()) {
            (Some((id, _)), None) => single(id),
            (Some(_), Some(_)) => None,
            // Untouched by both, unless what it stands for went.
            (None, _) => self
                .canonical_of(at)
                .filter(|c| !dropped.contains(c))
                .map(|_| at.clone()),
        }
    }

    /// Rewrites the local operations reachable from `heads` to match `contraction` of the
    /// canonical history they stand for, as `counterparts` and the translation map say: each
    /// surviving canonical operation's local one with its contracted parents' local ones as
    /// parents, its view and metadata otherwise as they were, so that nothing exports and no
    /// ref moves; and each local operation that stands for none, as `unmapped` has them, on
    /// its parents' rewrites. Returns the local operations each becomes.
    fn rewrite_locals(
        &mut self,
        contraction: &mut Contraction,
        heads: &[LocalOp],
        counterparts: &HashMap<LocalOp, CanonicalOp>,
        unmapped: &[(LocalOp, StoreOperation)],
    ) -> Result<HashMap<LocalOp, Vec<LocalOp>>, NodeError> {
        let op_store = self.loader.op_store().clone();
        let canonical = &self.canonical;
        // Every canonical operation of the history that may change, with the local one now
        // standing for it.
        let mut standing: HashMap<CanonicalOp, LocalOp> = HashMap::new();
        // The local operations reachable from the heads that stand for canonical ones that may
        // change: more than one local operation can stand for a canonical one, as a
        // realization and its export do, and the translation map knows only the latest.
        let mut stack: Vec<LocalOp> = heads.to_vec();
        let mut seen = HashSet::new();
        while let Some(local) = stack.pop() {
            if !seen.insert(local.clone()) || self.before_join.contains(&local) {
                continue;
            }
            match self.canonical_of(&local) {
                Some(c) => {
                    if !contraction.may_change(canonical, &c)? {
                        continue;
                    }
                    standing.entry(c).or_insert_with(|| local.clone());
                }
                None if counterparts.contains_key(&local) => {}
                None => {}
            }
            let op = op_store.read_operation(&local.0).block_on()?;
            stack.extend(LocalOp::parents_of(&op));
        }
        for (local, c) in counterparts {
            standing.insert(c.clone(), local.clone());
        }
        let mut tops: Vec<CanonicalOp> = standing.keys().cloned().collect();
        for head in heads {
            if let Some(c) = self.canonical_of(head) {
                tops.push(c);
            }
        }
        let mut affected: Vec<CanonicalOp> = canonical.ancestors_until(&tops, |op| {
            !standing.contains_key(op) && !contraction.may_change(canonical, op).unwrap_or(true)
        })?;
        affected.retain(|op| self.local_of(op).is_some() || standing.contains_key(op));
        // Validate and contract tips before their prefixes: asking in parents-first order
        // would rescan each growing prefix to check original identities, quadratically.
        for c in affected.iter().rev() {
            contraction.images(canonical, c)?;
        }
        // Parents first: `ancestors_until` puts them so.
        let mut local_now: HashMap<CanonicalOp, LocalOp> = HashMap::new();
        let mut locals: HashMap<LocalOp, Vec<LocalOp>> = HashMap::new();
        for c in &affected {
            let Some(template) = standing.get(c).cloned().or_else(|| self.local_of(c)) else {
                continue;
            };
            let images = contraction.images(&self.canonical, c)?;
            if contraction.drops(c) {
                let mut rewritten = vec![];
                for image in &images {
                    rewritten.push(self.local_for(image, &local_now)?);
                }
                locals.insert(template, dedup(rewritten));
                continue;
            }
            let new = images[0].clone();
            let mut op = op_store.read_operation(&template.0).block_on()?;
            let mut parents = vec![];
            for parent in self.canonical.parents(&new)? {
                parents.push(self.local_for(&parent, &local_now)?.0);
            }
            let changed = new != *c
                || (counterparts.contains_key(&template)
                    && !op.metadata.attributes.contains_key(CANONICAL_ATTRIBUTE))
                || op.parents != parents
                || op
                    .metadata
                    .attributes
                    .get(CANONICAL_ATTRIBUTE)
                    .is_some_and(|hex| *hex != new.0.hex());
            let rewrite = if changed {
                op.parents = parents;
                // The translation map is disposable. Without a durable marker, translating
                // this rewrite after cache loss would mint an origin from its new parents.
                // It also prevents jj's local content addressing from coalescing originals.
                op.metadata
                    .attributes
                    .insert(CANONICAL_ATTRIBUTE.to_owned(), new.0.hex());
                LocalOp(op_store.write_operation(&op).block_on()?)
            } else {
                template.clone()
            };
            self.insert_map(rewrite.clone(), new.clone())?;
            local_now.insert(new, rewrite.clone());
            locals.insert(template, vec![rewrite]);
        }
        // Another local operation standing for the same canonical one, as jj's rewrite of an
        // operation and a copy of it a stale workspace brought back do, becomes the same.
        for (local, c) in counterparts {
            if !locals.contains_key(local)
                && let Some(rewritten) = standing.get(c).and_then(|winner| locals.get(winner))
            {
                locals.insert(local.clone(), rewritten.clone());
            }
        }
        // Operations written since that stand for nothing yet, on their parents' rewrites.
        for (id, op) in unmapped {
            if counterparts.contains_key(id) {
                continue;
            }
            let old_parents = LocalOp::parents_of(op);
            let parents = dedup(
                old_parents
                    .iter()
                    .flat_map(|p| locals.get(p).cloned().unwrap_or_else(|| vec![p.clone()])),
            );
            let rewrite = if parents == old_parents {
                id.clone()
            } else {
                let mut op = op.clone();
                op.parents = parents.into_iter().map(|parent| parent.0).collect();
                LocalOp(op_store.write_operation(&op).block_on()?)
            };
            locals.insert(id.clone(), vec![rewrite]);
        }
        Ok(locals)
    }

    /// The local operation for `canonical`, a node-space operation: one just rewritten, or
    /// the one the translation map has.
    fn local_for(
        &self,
        canonical: &CanonicalOp,
        local_now: &HashMap<CanonicalOp, LocalOp>,
    ) -> Result<LocalOp, NodeError> {
        local_now
            .get(canonical)
            .cloned()
            .or_else(|| self.local_of(canonical))
            .ok_or_else(|| {
                NodeError::NotRealizable(canonical.0.hex(), "its local operation is missing")
            })
    }

    /// Moves the op heads to their rewrites, and to `head` too if given, keeping the maximal
    /// ones: `heads := max(images(heads) ∪ {head})`. `merged`, a merge of some of those, goes
    /// in place of the ones it merges.
    fn move_heads(
        &mut self,
        heads: &[LocalOp],
        locals: &HashMap<LocalOp, Vec<LocalOp>>,
        head: Option<&LocalOp>,
        merged: Option<&LocalOp>,
    ) -> Result<(), NodeError> {
        let new = self.new_heads(heads, locals, head, merged)?;
        self.publish_heads(heads, &new)
    }

    /// The op heads [`Self::move_heads`] moves `heads` to.
    fn new_heads(
        &self,
        heads: &[LocalOp],
        locals: &HashMap<LocalOp, Vec<LocalOp>>,
        head: Option<&LocalOp>,
        merged: Option<&LocalOp>,
    ) -> Result<Vec<LocalOp>, NodeError> {
        let mut new = self.moved_heads(heads, locals, head)?;
        if let Some(merged) = merged {
            let parents = LocalOp::parents_of(
                &self
                    .loader
                    .op_store()
                    .read_operation(&merged.0)
                    .block_on()?,
            );
            new.retain(|op| !parents.contains(op));
            new.push(merged.clone());
        }
        Ok(new)
    }

    /// Makes `new` the op heads in place of `heads`.
    fn publish_heads(&mut self, heads: &[LocalOp], new: &[LocalOp]) -> Result<(), NodeError> {
        let old: Vec<OperationId> = heads
            .iter()
            .filter(|h| !new.contains(h))
            .map(|h| h.0.clone())
            .collect();
        // The new heads go in before the old come out, the last with them: a crash in between
        // leaves extra heads, which jj merges, rather than losing any.
        let op_heads = self.loader.op_heads_store().clone();
        if let Some((last, rest)) = new.split_last() {
            for head in rest {
                op_heads.update_op_heads(&[], &head.0).block_on()?;
            }
            if self.records.stop == Some(TakingStop::Publishing) {
                // As a crash in jj's update leaves them, its new op head in.
                op_heads.update_op_heads(&[], &last.0).block_on()?;
                self.stop_taking(TakingStop::Publishing)?;
            }
            op_heads.update_op_heads(&old, &last.0).block_on()?;
        }
        Ok(())
    }

    /// The op heads `heads` moved to their rewrites, with `head` too if given, the maximal
    /// ones: `max(images(heads) ∪ {head})`.
    fn moved_heads(
        &self,
        heads: &[LocalOp],
        locals: &HashMap<LocalOp, Vec<LocalOp>>,
        head: Option<&LocalOp>,
    ) -> Result<Vec<LocalOp>, NodeError> {
        let mut new: Vec<LocalOp> = dedup(
            heads
                .iter()
                .flat_map(|h| locals.get(h).cloned().unwrap_or_else(|| vec![h.clone()]))
                .chain(head.cloned()),
        );
        // Keep only the maximal ones, by the canonical operations they stand for.
        let canonical: Vec<Option<CanonicalOp>> =
            new.iter().map(|local| self.canonical_of(local)).collect();
        let mut keep = vec![true; new.len()];
        for i in 0..new.len() {
            for j in 0..new.len() {
                if i == j || !keep[j] {
                    continue;
                }
                if let (Some(a), Some(b)) = (&canonical[i], &canonical[j])
                    && a != b
                    && self.canonical.is_ancestor_of(a, b)?
                {
                    keep[i] = false;
                }
            }
        }
        let mut index = 0;
        new.retain(|_| {
            index += 1;
            keep[index - 1]
        });
        Ok(new)
    }

    /// Moves the operation each of this repository's workspaces recorded to its rewrite, as
    /// `locals` or a renaming has it, as jj's own `jj op abandon` moves the workspace it runs
    /// in: otherwise jj takes the working copy for a sibling of the history the next time its
    /// commit changes. Only the record moves; no file changes. A workspace this can't load is
    /// left, and jj's `jj workspace update-stale` moves it.
    pub(super) fn move_workspaces(
        &self,
        locals: &HashMap<LocalOp, Vec<LocalOp>>,
    ) -> Result<(), NodeError> {
        let mut roots: BTreeSet<PathBuf> = BTreeSet::new();
        let mut names = BTreeSet::new();
        for head in self.local_heads()? {
            let view = self.repo_at(&head)?;
            names.extend(view.view().wc_commit_ids().keys().cloned());
        }
        for name in &names {
            if let Ok(Some(path)) = self.loader.workspace_store().get_workspace_path(name) {
                roots.insert(path);
            }
        }
        // Where `.jj/repo` is a directory, the workspace around it.
        if let Some(root) = self.repo_path.parent().and_then(Path::parent) {
            roots.insert(root.to_owned());
        }
        // Worked out only if a working copy needs it.
        let by_content = std::cell::OnceCell::new();
        for root in roots {
            if let Err(err) = self.move_workspace(&root, locals, &by_content) {
                tracing::warn!(
                    "recording {}'s operation as rewritten: {err}",
                    root.display()
                );
            }
        }
        Ok(())
    }

    /// The rewrites `locals` makes, by the fingerprint of what each rewrites: its content but
    /// for its parents, which jj's own rewrite of an operation keeps. None for a fingerprint
    /// that more than one operation has, or one that `locals` drops or splits.
    fn rewrites_by_content(
        &self,
        locals: &HashMap<LocalOp, Vec<LocalOp>>,
    ) -> HashMap<String, Option<LocalOp>> {
        let op_store = self.loader.op_store();
        let mut by_content: HashMap<String, Option<LocalOp>> = HashMap::new();
        for (old, new) in locals {
            // One that can't be read stands for nothing here.
            let Ok(op) = op_store.read_operation(&old.0).block_on() else {
                continue;
            };
            let rewrite = match new.as_slice() {
                [new] => Some(new.clone()),
                _ => None,
            };
            by_content
                .entry(fingerprint(&op))
                .and_modify(|found| *found = None)
                .or_insert(rewrite);
        }
        by_content
    }

    /// The rewrite of `recorded`, an operation a working copy records that `jj op abandon`
    /// rewrote without moving the working copy, as it does one not at an op head, where no
    /// renaming names its rewrite: one not yet published, whose canonical form no record
    /// superseded. jj's rewrite keeps all but the parents, so it is the one operation
    /// `by_content` has with the same fingerprint, if the op heads no longer reach `recorded`.
    /// Left stale, the working copy's next command would merge what the abandon dropped back
    /// in, with `snapshot.auto-update-stale`, and the hub would refuse every push of it.
    fn rewrite_by_content(
        &self,
        recorded: &LocalOp,
        by_content: &HashMap<String, Option<LocalOp>>,
    ) -> Result<Option<LocalOp>, NodeError> {
        let op = match self
            .loader
            .op_store()
            .read_operation(&recorded.0)
            .block_on()
        {
            Ok(op) => op,
            Err(jj_lib::op_store::OpStoreError::ObjectNotFound { .. }) => return Ok(None),
            Err(err) => return Err(err.into()),
        };
        let Some(Some(rewrite)) = by_content.get(&fingerprint(&op)) else {
            return Ok(None);
        };
        // An operation still in the history keeps its working copy.
        let heads = self.local_heads()?;
        let mut stack = heads.clone();
        let mut seen = HashSet::new();
        while let Some(local) = stack.pop() {
            if local == *recorded {
                return Ok(None);
            }
            if !seen.insert(local.clone()) {
                continue;
            }
            let op = self.loader.op_store().read_operation(&local.0).block_on()?;
            stack.extend(LocalOp::parents_of(&op));
        }
        Ok(Some(rewrite.clone()))
    }

    fn move_workspace(
        &self,
        root: &Path,
        locals: &HashMap<LocalOp, Vec<LocalOp>>,
        by_content: &std::cell::OnceCell<HashMap<String, Option<LocalOp>>>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        if !root.join(".jj").join("working_copy").is_dir() {
            return Ok(());
        }
        use jj_lib::workspace::WorkspaceLoaderFactory as _;
        let mut workspace = jj_lib::workspace::DefaultWorkspaceLoaderFactory
            .create(root)?
            .load(
                self.loader.settings(),
                &jj_lib::default_backend_factories::default_backend_factories(),
                &jj_lib::default_backend_factories::default_working_copy_factories(),
            )?;
        let same = |a: &Path, b: &Path| match (a.canonicalize(), b.canonicalize()) {
            (Ok(a), Ok(b)) => a == b,
            _ => false,
        };
        if !same(workspace.repo_path(), &self.repo_path) {
            return Ok(());
        }
        // Read under the lock, so that a `jj` command that records another meanwhile isn't
        // moved back.
        let mut locked = workspace.start_working_copy_mutation().block_on()?;
        let recorded = LocalOp(locked.locked_wc().old_operation_id().clone());
        let rewrite = match locals.get(&recorded).map(Vec::as_slice) {
            Some([rewrite]) => Some(rewrite.clone()),
            _ => {
                let now = match self.canonical_of(&recorded) {
                    Some(canonical) => match self.current_ids(&canonical)?.as_slice() {
                        [now] if *now != canonical => self.local_of(now),
                        _ => None,
                    },
                    None => None,
                };
                now.map_or_else(
                    || {
                        let by_content =
                            by_content.get_or_init(|| self.rewrites_by_content(locals));
                        self.rewrite_by_content(&recorded, by_content)
                    },
                    |op| Ok(Some(op)),
                )?
            }
        };
        let Some(rewrite) = rewrite.filter(|rewrite| *rewrite != recorded) else {
            return Ok(());
        };
        locked.finish(rewrite.0).block_on()?;
        Ok(())
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

    /// Gets ready to take `records`, the hub's, after the first ones `prefix` stands for:
    /// renames this node's history as they name it, writing the rewrites of its local
    /// operations beside them, without moving its op heads. Returns whether they drop an op
    /// head. `prefix` is this node's, or none, or this node is [fresh](Self::is_fresh).
    pub fn prepare_records(
        &mut self,
        prefix: &RecordPrefix,
        records: &[Record],
    ) -> Result<bool, NodeError> {
        if self
            .records
            .taking
            .as_ref()
            .is_none_or(|taking| taking.prefix != *prefix || taking.records != records)
        {
            self.prepare(prefix, records)?;
        } else {
            self.prepare_again_if_moved()?;
        }
        let taking = self.records.taking.as_ref().expect("prepared above");
        if taking.switched {
            return Ok(false);
        }
        let heads = self.local_heads()?;
        Ok(heads.iter().any(|head| {
            self.canonical_of(head)
                .is_some_and(|c| taking.dropped.contains(&c))
        }))
    }

    /// Whether received records remain in custody. Taking the hub's next announcement either
    /// applies them or, if the hub lost them, makes their drops pending, even when it announces
    /// the records this node already applied.
    pub fn has_record_custody(&self) -> bool {
        !self.records.custody.is_empty()
    }

    /// Keeps in custody `records`, after those `prefix` stands for, beyond the first `common`
    /// this node holds, before anything written for them or named as they name the history
    /// is: its history may then leave out what they drop, though it takes them only later, as
    /// while they drop an op head, or never, if the hub loses them first. Writes only records
    /// it doesn't hold or keep already.
    fn keep_custody(
        &mut self,
        prefix: &RecordPrefix,
        records: &[Record],
        common: usize,
    ) -> Result<(), NodeError> {
        let chain = digests(&prefix.digest, records);
        let new: Vec<Earlier> = {
            let held: HashSet<&RecordDigest> = self.records.digests.iter().collect();
            let kept: HashSet<&RecordDigest> = self
                .records
                .custody
                .iter()
                .map(|custody| &custody.digest)
                .collect();
            (common..records.len())
                .filter(|&k| !held.contains(&chain[k + 1]) && !kept.contains(&chain[k + 1]))
                .map(|k| Earlier {
                    digest: chain[k + 1].clone(),
                    before: chain[k].clone(),
                    record: records[k].clone(),
                })
                .collect()
        };
        if new.is_empty() {
            return Ok(());
        }
        let checkpoint = self.records.checkpoint();
        self.records.custody.extend(new);
        if let Err(err) = self.save_records() {
            self.records.restore(checkpoint);
            return Err(err);
        }
        Ok(())
    }

    /// Renames this node's history as `records` name it, writing the rewrites of its local
    /// operations, from scratch.
    fn prepare(&mut self, prefix: &RecordPrefix, records: &[Record]) -> Result<(), NodeError> {
        self.records.taking = None;
        // The hub-to-node translation as it is with no records being taken, which
        // `rename_for` uses.
        self.forget_to_node();
        let taking = self.rename_for(prefix, records)?;
        self.records.taking = Some(taking);
        self.forget_to_node();
        Ok(())
    }

    /// Prepares the records being taken again if the op heads moved since they were
    /// prepared, as a `jj` command moves them. Their rewrites are only of what was reachable
    /// from the op heads then, and a sync's next step gives the operation such a command wrote
    /// a canonical form, as `realize` does on a node opened since, on the history the records
    /// rename: taken without renaming it, it would bring back what they drop. Does nothing if
    /// the op heads moved there already.
    fn prepare_again_if_moved(&mut self) -> Result<(), NodeError> {
        let Some(taking) = self
            .records
            .taking
            .as_ref()
            .filter(|taking| !taking.switched)
        else {
            return Ok(());
        };
        let mut heads = self.local_heads()?;
        heads.sort();
        if heads == taking.heads {
            return Ok(());
        }
        let (prefix, records) = (taking.prefix.clone(), taking.records.clone());
        self.prepare(&prefix, &records)
    }

    /// The renaming that taking `records`, after those `prefix` stands for, makes, its local
    /// rewrites written.
    fn rename_for(
        &mut self,
        prefix: &RecordPrefix,
        records: &[Record],
    ) -> Result<Taking, NodeError> {
        // Only a node with nothing of the hive's takes records it knows only by their count
        // and digest: it has nothing they drop. Any node may take records all whole in place
        // of those it knew so: whichever of them drops what it has, it drops by name.
        if *prefix != self.records.prefix && prefix.count > 0 && !self.is_fresh() {
            return Err(NodeError::PrunedRecords);
        }
        let applied = self.records.applied.clone();
        let common = if *prefix == self.records.prefix {
            applied
                .iter()
                .zip(records)
                .take_while(|(a, b)| a == b)
                .count()
        } else {
            0
        };
        // Before anything below, or anything named as they name the history, writes a local
        // operation.
        self.keep_custody(prefix, records, common)?;
        let store = &self.canonical;
        let heads = self.local_heads()?;
        let (mapped, unmapped) = self.local_walk(&heads)?;
        // Records in custody that these lack: the hub lost them, and this node publishes what
        // they drop, as of records it took that the hub lost. It never took them, so its
        // history may still have what they drop, which it drops now too.
        let incoming: HashSet<RecordDigest> =
            digests(&prefix.digest, records).into_iter().collect();
        let lost_custody: Vec<&Earlier> = self
            .records
            .custody
            .iter()
            .filter(|custody| !incoming.contains(&custody.digest))
            .collect();
        // Another raw version of a dropped original may be here without the record that
        // renamed it. Match physical history, not old bodies in the canonical cache.
        let mut local_versions: HashMap<OperationId, Vec<CanonicalOp>> = HashMap::new();
        if common < records.len() || !lost_custody.is_empty() {
            let wanted: HashSet<OperationId> = records[common..]
                .iter()
                .chain(lost_custody.iter().map(|custody| &custody.record))
                .flat_map(Record::ops)
                .filter(|op| store.has_operation(&op.0))
                .map(|op| store.original_id(&op.0))
                .collect::<Result<_, _>>()?;
            let tops: Vec<CanonicalOp> = mapped.into_iter().map(|(_, op)| op).collect();
            for op in store.ancestors_until(&tops, |_| false)? {
                let original = store.original_id(&op)?;
                if wanted.contains(&original) {
                    local_versions.entry(original).or_default().push(op);
                }
            }
        }
        // A hub name from after the `from`th record this node took, as the history named the
        // operation after the records the hub and this node share: back through how each
        // record since renamed the hub's history. An operation made since has no such name,
        // and keeps its own.
        let hub_renamings = &self.records.hub_renamings;
        let back = |op: &CanonicalOp, from: usize| {
            (common..from).rev().fold(op.clone(), |op, k| {
                match hub_renamings.get(k).and_then(|renaming| renaming.get(&op)) {
                    Some(old) => old.clone(),
                    None => op,
                }
            })
        };
        // What this node dropped beyond the records they share: its own pending drops, and
        // its records the hub lacks (as after the hub went back), named so.
        let mut mine: Vec<CanonicalOp> = self
            .records
            .pending
            .ops()
            .iter()
            .map(|op| back(&op.0, applied.len()))
            .collect();
        for (k, record) in applied.iter().enumerate().skip(common) {
            mine.extend(record.ops().iter().map(|op| back(&op.0, k)));
        }
        // Named as the history this node realized named them; `name_pending_as` names them as
        // the hub's does, by their originals.
        let mut to_drop = vec![];
        // What the records both hold drop already is no drop of this node's.
        let mut shared_originals = HashSet::new();
        for op in applied[..common].iter().flat_map(Record::ops) {
            if store.has_operation(&op.0) {
                shared_originals.insert(store.original_id(&op.0)?);
            }
        }
        for custody in &lost_custody {
            for op in custody.record.ops() {
                if store.has_operation(&op.0)
                    && shared_originals.contains(&store.original_id(&op.0)?)
                {
                    continue;
                }
                mine.push(op.0.clone());
                if store.has_operation(&op.0)
                    && let Some(versions) = local_versions.get(&store.original_id(&op.0)?)
                {
                    to_drop.extend(versions.iter().cloned());
                }
            }
        }
        let lost_custody: HashSet<RecordDigest> = lost_custody
            .into_iter()
            .map(|custody| custody.digest.clone())
            .collect();
        // Where the hub lost records this machine took, it may have lost the base too: the
        // root is accepted wherever the hub went back to, at the cost of fetching everything.
        let mut base = if common < applied.len() {
            Some(store.root_operation_id().clone())
        } else {
            self.stored_base().map(|base| base.0)
        };
        // Then forward through the hub's records, one at a time, keeping how each renames
        // the hub's history below the base; and the node names of what they drop, but what
        // this node dropped already, whose node names are what is left below it.
        let mut renamings: Vec<HashMap<CanonicalOp, CanonicalOp>> = vec![];
        for record in &records[common..] {
            let names: Vec<CanonicalOp> = record.ops().iter().map(|op| op.0.clone()).collect();
            let dropped_here: HashSet<CanonicalOp> = mine.iter().cloned().collect();
            for op in &names {
                if let Some(versions) = local_versions.get(&store.original_id(op)?) {
                    to_drop.extend(versions.iter().cloned());
                }
                let shared = renamings.iter().rev().fold(op.clone(), |op, renaming| {
                    renaming.get(&op).cloned().unwrap_or(op)
                });
                if dropped_here.contains(op)
                    || self.records.dropped.contains(&shared)
                    || !store.has_operation(&shared)
                {
                    continue;
                }
                to_drop.extend(self.to_node_ids(&shared)?);
            }
            let mut contraction =
                Contraction::new(store, names.iter().cloned())?.sharing(self.presences.clone());
            // An operation made after the records they share has no name from before them,
            // so its history names the record's operations as renamed since: it is named as
            // this machine's history names it, as any machine that has it pushes it.
            let mut ours =
                Contraction::new(store, to_drop.iter().cloned())?.sharing(self.presences.clone());
            let theirs: HashSet<&CanonicalOp> = names.iter().collect();
            // A record drops an original, whatever it names it: what this node dropped as
            // another version of one the record names is published by it, as another machine
            // published it under the name the hub's history gave it.
            let mut theirs_originals = HashSet::new();
            for op in names.iter().filter(|op| store.has_operation(op)) {
                theirs_originals.insert(store.original_id(op)?);
            }
            let mut renamed = vec![];
            for op in mine.iter().filter(|op| !theirs.contains(op)) {
                if !store.has_operation(op) {
                    renamed.push(op.clone());
                    continue;
                }
                if theirs_originals.contains(&store.original_id(op)?) {
                    continue;
                }
                let images = contraction.images(store, op)?;
                if images == std::slice::from_ref(op) {
                    renamed.extend(ours.images(store, op)?);
                } else {
                    renamed.extend(images);
                }
            }
            mine = renamed;
            if let Some(old) = base.take() {
                base = if store.has_operation(&old) {
                    contraction.images(store, &old)?.first().cloned()
                } else {
                    Some(old)
                };
            }
            let dropped = contraction.dropped().clone();
            renamings.push(
                contraction
                    .into_images()
                    .into_iter()
                    .filter(|(old, _)| !dropped.contains(old))
                    .filter_map(|(old, new)| match new.as_slice() {
                        [new] => Some((new.clone(), old)),
                        _ => None,
                    })
                    .collect(),
            );
        }
        let mut contraction = Contraction::new(store, to_drop)?.sharing(self.presences.clone());
        let locals = self.rewrite_locals(&mut contraction, &heads, &HashMap::new(), &unmapped)?;
        let mut heads = heads;
        heads.sort();
        Ok(Taking {
            prefix: prefix.clone(),
            records: records.to_vec(),
            common,
            hub_renamings: renamings,
            dropped: contraction.dropped().clone(),
            switched: false,
            renaming: contraction.into_images(),
            pending: Record::new(mine.into_iter().map(HubOp)),
            locals,
            heads,
            base: base.map(HubOp),
            lost_custody,
        })
    }

    /// Whether records are being taken whose renaming the op heads haven't moved to.
    pub(super) fn taking_unswitched(&self) -> bool {
        self.records
            .taking
            .as_ref()
            .is_some_and(|taking| !taking.switched)
    }

    /// The op heads that moving them where the records being taken name them leaves beside
    /// `head`, as they name them: `max(images(heads) ∪ {head}) \ {head}`. Empty if no records
    /// are being taken, or the op heads are there already.
    pub(super) fn taken_beside(&mut self, head: &LocalOp) -> Result<Vec<LocalOp>, NodeError> {
        self.prepare_again_if_moved()?;
        let Some(taking) = self
            .records
            .taking
            .as_ref()
            .filter(|taking| !taking.switched)
        else {
            return Ok(vec![]);
        };
        let mut beside = self.moved_heads(&self.local_heads()?, &taking.locals, Some(head))?;
        beside.retain(|op| op != head);
        Ok(beside)
    }

    /// Takes the records being taken, and moves the op heads where they name them, and to
    /// `head` too if given: `heads := max(images(heads) ∪ {head})`, with `merged`, if given, a
    /// merge of `head` with heads [`Self::taken_beside`] it, in place of those it merges,
    /// preparing the records again first if the op heads moved
    /// ([`Self::prepare_again_if_moved`]). Does nothing if no records are being taken, or the
    /// op heads are there already. The caller moves the workspaces after
    /// ([`Self::move_taken_workspaces`]), holding no lock of jj's: jj takes a workspace's lock
    /// before its colocated git lock.
    pub(super) fn switch_to_taken(
        &mut self,
        head: Option<&LocalOp>,
        merged: Option<&LocalOp>,
    ) -> Result<(), NodeError> {
        self.prepare_again_if_moved()?;
        let Some(mut taking) = self.records.taking.take() else {
            return Ok(());
        };
        if !taking.switched {
            // Translation no longer names the history as `taking` does, whether this fails,
            // dropping it, or holds it, its pending drops becoming this node's.
            self.forget_to_node();
            // Every operation the move names written first, which the realizations are by now.
            self.settle()?;
            let heads = self.local_heads()?;
            let to = self.new_heads(&heads, &taking.locals, head, merged)?;
            let renamed = taking
                .locals
                .iter()
                .filter(|(old, new)| new.as_slice() != std::slice::from_ref(*old))
                .flat_map(|(old, new)| std::iter::once(old).chain(new));
            let canonical = heads
                .iter()
                .chain(&to)
                .chain(renamed)
                .filter_map(|local| Some((local.clone(), self.canonical_of(local)?)))
                .collect();
            let from = heads
                .iter()
                .map(|head| {
                    let new = taking.locals.get(head).cloned();
                    (head.clone(), new.unwrap_or_else(|| vec![head.clone()]))
                })
                .collect();
            let realign = Realign {
                from,
                to: to.clone(),
                canonical,
            };
            self.hold_taken(&mut taking, realign)?;
            self.stop_taking(TakingStop::Heads)?;
            self.publish_heads(&heads, &to)?;
            self.forget_local_caches();
            taking.switched = true;
        }
        self.records.taking = Some(taking);
        Ok(())
    }

    /// Whether one of the local operations `canonical` names that stands for an operation a
    /// renaming superseded is below `heads`.
    fn superseded_below(
        &self,
        heads: &[LocalOp],
        canonical: &HashMap<LocalOp, CanonicalOp>,
    ) -> Result<bool, NodeError> {
        let mut superseded: HashMap<&LocalOp, &CanonicalOp> = HashMap::new();
        for (local, c) in canonical {
            if self.current_ids(c)? != std::slice::from_ref(c) {
                superseded.insert(local, c);
            }
        }
        // Below the lowest of them, an operation that stands for one of the store's has none
        // of them below it. One written on one of them, canonicalized on what that became, is
        // as high as that one, at least.
        let mut floor = u64::MAX;
        for c in superseded.values() {
            if self.canonical.has_operation(c) {
                floor = floor.min(self.canonical.generation(c)?);
            }
        }
        let op_store = self.loader.op_store();
        let mut stack = heads.to_vec();
        let mut seen = HashSet::new();
        while let Some(local) = stack.pop() {
            if !seen.insert(local.clone()) || self.before_join.contains(&local) {
                continue;
            }
            if superseded.contains_key(&local) {
                return Ok(true);
            }
            if self
                .canonical_of(&local)
                .is_some_and(|c| self.canonical.generation(&c).is_ok_and(|g| g < floor))
            {
                continue;
            }
            let op = op_store.read_operation(&local.0).block_on()?;
            stack.extend(LocalOp::parents_of(&op));
        }
        Ok(false)
    }

    /// Makes the records being taken the records this node holds, and what they rename its
    /// history, pending drops and fix-up as, in the write that counts their renaming, before
    /// the op heads move there: counted alone, the renaming would leave what they drop
    /// dropped here, but neither pending nor in a record this node holds, so that if the hub
    /// lost them, nothing here would publish it again. The op heads and the workspaces move
    /// after, as `realign` says, which the write records, so that a restart moves them if
    /// they hadn't (`realign_heads`). If the write fails, this node holds what it did, as
    /// `records.json` still says.
    fn hold_taken(&mut self, taking: &mut Taking, realign: Realign) -> Result<(), NodeError> {
        // Appended first, each counting only once `records.json` says so.
        self.write_hub_renamings(
            &taking.prefix.digest,
            &taking.records,
            taking.common,
            &taking.hub_renamings,
        )?;
        let step = self.append_step(taking.renaming.clone(), &taking.dropped, &HashMap::new())?;
        let checkpoint = self.records.checkpoint();
        // Its own drops published, the fix-up goes with them.
        if taking.pending.is_empty() {
            self.records.fixup = None;
            self.records.fixup_written = false;
            self.records.fixup_from = None;
        } else if let Some(fixup) = &self.records.fixup
            && let Some(expected) = &fixup.expected
        {
            // The op head the expected values were worked out at, as the records renamed it,
            // unless they dropped it or made it several.
            let at = OperationId::try_from_hex(&expected.at)
                .map(LocalOp)
                .filter(|at| {
                    !self
                        .canonical_of(at)
                        .is_some_and(|c| taking.dropped.contains(&c))
                });
            let now = at.and_then(|at| match taking.locals.get(&at).map(Vec::as_slice) {
                Some([now]) => Some(now.clone()),
                Some(_) => None,
                None => Some(at),
            });
            let fixup = self.records.fixup.as_mut().expect("matched above");
            match now {
                Some(now) => fixup.expected.as_mut().expect("matched above").at = now.0.hex(),
                None => fixup.expected = None,
            }
        }
        // Lost receipts have now had their effects applied with the incoming records. Keep
        // their readable prefixes as earlier records, without ever reporting them as the
        // current applied list. The hold's reachability cleanup discards unknown prefixes.
        let earlier: HashSet<RecordDigest> = self
            .records
            .earlier
            .iter()
            .map(|entry| entry.digest.clone())
            .collect();
        self.records.earlier.extend(
            self.records
                .custody
                .iter()
                .filter(|entry| {
                    taking.lost_custody.contains(&entry.digest) && !earlier.contains(&entry.digest)
                })
                .cloned(),
        );
        self.records
            .hold(taking.prefix.clone(), taking.records.clone());
        // Custody taken, or lost and now pending, in the same write.
        let held: HashSet<RecordDigest> = self.records.digests.iter().cloned().collect();
        self.records.custody.retain(|custody| {
            !held.contains(&custody.digest) && !taking.lost_custody.contains(&custody.digest)
        });
        self.records.fresh = false;
        self.records.pending = taking.pending.clone();
        self.records.steps += usize::from(step.is_some());
        self.records.realign = Some(realign);
        if let Err(err) = self
            .stop_taking(TakingStop::Hold)
            .and_then(|()| self.save_records())
        {
            self.records.restore(checkpoint);
            return Err(err);
        }
        if let Some(step) = step {
            self.records.compose(step);
        }
        self.records.hub_renamings.truncate(taking.common);
        self.records
            .hub_renamings
            .extend(std::mem::take(&mut taking.hub_renamings));
        self.forget_to_node();
        Ok(())
    }

    /// Moves the workspaces' recorded operations where the records taken name them, once the
    /// op heads are there, which is the last of taking them.
    pub(super) fn move_taken_workspaces(&mut self) -> Result<(), NodeError> {
        let Some(taking) = self.records.taking.take_if(|taking| taking.switched) else {
            return Ok(());
        };
        self.stop_taking(TakingStop::Workspaces)?;
        self.move_workspaces(&taking.locals)?;
        self.records.realign = None;
        self.save_records()
    }

    /// For tests of errors: the next write that holds records taken fails, as an I/O error
    /// would, having written none of it.
    pub fn fail_holding_records(&mut self) {
        self.records.stop = Some(TakingStop::Hold);
    }

    /// For tests of crashes: the next taking of records stops, failing, once it holds them,
    /// before the op heads move there, or, if `heads_moved`, once they have, before the
    /// workspaces. Reopening the repository then is a crash there.
    pub fn crash_taking_records(&mut self, heads_moved: bool) {
        self.records.stop = Some(if heads_moved {
            TakingStop::Workspaces
        } else {
            TakingStop::Heads
        });
    }

    /// For tests of crashes: the next move of the op heads, as taking records makes it,
    /// stops, failing, once the new op heads are in, before the old ones come out, as a crash
    /// in jj's update of them leaves them.
    pub fn crash_publishing_taken_heads(&mut self) {
        self.records.stop = Some(TakingStop::Publishing);
    }

    /// Fails, once, if a test said to stop taking records `at`.
    fn stop_taking(&mut self, at: TakingStop) -> Result<(), NodeError> {
        if self.records.stop != Some(at) {
            return Ok(());
        }
        self.records.stop = None;
        Err(NodeError::Io {
            path: self.records_path(),
            source: std::io::Error::other(format!("stopped for a test: {at:?}")),
        })
    }

    /// Takes the hub's records, after the first ones `prefix` stands for, none of which drops
    /// an op head. Returns the operation the hub accepted that this machine fetches from, as
    /// they name it.
    pub fn adopt_records(
        &mut self,
        prefix: &RecordPrefix,
        records: &[Record],
    ) -> Result<Option<HubOp>, NodeError> {
        self.prepare_records(prefix, records)?;
        self.switch_to_taken(None, None)?;
        let base = self
            .records
            .taking
            .as_ref()
            .expect("prepared above")
            .base
            .clone();
        self.move_taken_workspaces()?;
        Ok(base)
    }

    /// What the fix-up must write for the state at `new`, the node-space rewrite of `old`,
    /// to be as it was at `old`. Presence is as it was (docs/internals/design.md, "Presence
    /// through an abandon"), but where a copy's latest work, or the `musubi.forget-after` it
    /// last recorded, is work the abandon dropped, the fix-up does it again, with when it was
    /// done and what it recorded, so that what comes after has it; then forgets the copy
    /// again if it is forgotten where the fix-up is written ([`Self::write_fixup`]).
    fn fixup_between(&mut self, old: &CanonicalOp, new: &CanonicalOp) -> Result<Fixup, NodeError> {
        let before = self.presence(old)?;
        let after = self.presence(new)?;
        let mut fixup = Fixup::default();
        for copy in after.known() {
            if !after.ops_of(copy).any(|work| work.op.is_none()) {
                continue;
            }
            fixup.work.push(Work {
                copy: copy.clone(),
                forget_after: before
                    .has_forget_after(copy)
                    .then(|| format_forget_after(before.forget_after(copy))),
                worked_at: self.worked_at(&before, copy)?,
                forgotten: None,
            });
        }
        let (was, is) = (self.settings_at(old)?, self.settings_at(new)?);
        if was != is
            && let Some(was) = was
        {
            fixup.settings = Some(was.to_attribute());
        }
        Ok(fixup)
    }

    /// When a copy last worked, as `presence` has it: the latest end of its latest work's
    /// operations, or what a fix-up recorded for them.
    fn worked_at(
        &self,
        presence: &Presence<canonical::Work>,
        copy: &str,
    ) -> Result<Option<i64>, NodeError> {
        let mut last = None;
        for op in presence
            .worked(copy)
            .into_iter()
            .flatten()
            .filter_map(|work| work.op.as_ref())
        {
            let millis = self.work_time(op)?;
            last = Some(last.map_or(millis, |l: i64| l.max(millis)));
        }
        Ok(last)
    }

    /// When the work a canonical operation stands for was done, in milliseconds since the
    /// epoch: the end of the operation, or what a fix-up recorded.
    pub(super) fn work_time(&self, op: &CanonicalOp) -> Result<i64, NodeError> {
        let operation = self.canonical.read_operation(op)?;
        Ok(operation
            .metadata
            .attributes
            .get(WORKED_AT_ATTRIBUTE)
            .and_then(|text| text.parse().ok())
            .unwrap_or(operation.metadata.time.end.timestamp.0))
    }

    /// The expected value of each conflicted remote bookmark at `head`, as the history before
    /// the abandons the fix-up covers had it: the walk back through history stops at the op
    /// head the abandon was noticed at, with the values worked out there.
    fn expected_before(&self, head: &ReadonlyRepo) -> Result<Option<String>, NodeError> {
        let known = self.pending_expected();
        if known.is_empty() {
            return Ok(None);
        }
        let history = git::History {
            known: &known,
            roots: std::slice::from_ref(&self.root_op_id().0),
            is_join: &|op| self.is_join_point(op),
            parents: &|_| Ok(None),
        };
        let values = git::expected_values(head.store(), head.operation(), &history)?;
        Ok(git::format_expected(&values))
    }

    /// The expected values a fix-up not yet written will record, under the op head they were
    /// worked out at, for every walk to stop at until then: an export before the fix-up, as
    /// of a merge, would otherwise write what the rewritten history expects, and `jj` import
    /// it.
    pub(super) fn pending_expected(&self) -> git::Expected {
        let expectation = match &self.records.fixup {
            Some(fixup) if !self.records.fixup_written => fixup.expected.as_ref(),
            _ => None,
        };
        let Some((expectation, at)) =
            expectation.and_then(|e| Some((e, LocalOp(OperationId::try_from_hex(&e.at)?))))
        else {
            return git::Expected::new();
        };
        // Records being taken rename it before taking them re-keys it, as the op heads move
        // there, and a realization in the history they name is exported first: under both
        // names until then.
        let taken = self
            .records
            .taking
            .as_ref()
            .filter(|taking| !taking.switched)
            .and_then(|taking| match taking.locals.get(&at).map(Vec::as_slice) {
                Some([now]) => Some(now.clone()),
                _ => None,
            });
        let mut known = git::Expected::new();
        for (name, token) in &expectation.values {
            let Some(value) = git::parse_expected_token(token) else {
                continue;
            };
            let name = GitRefNameBuf::from(name.clone());
            for at in std::iter::once(&at).chain(&taken) {
                known.insert((at.clone(), name.clone()), value.clone());
            }
        }
        known
    }

    /// Writes the fix-up on the single op head, if it hasn't been, and returns the canonical
    /// operation of its last operation.
    pub fn write_fixup(&mut self) -> Result<Option<NodeOp>, NodeError> {
        self.write_fixup_until(None)
    }

    /// Gives pending drops a fresh publication id when the hub already has this head.
    /// The cached fix-up has restored its saved state; this child preserves the state now,
    /// with no work, settings or expected-value instructions to replay. A concurrent command
    /// that already changed the head makes a new marker unnecessary.
    /// The comparison uses exact ids, as the core does, without translating `expected`.
    pub fn write_drop_tip(&mut self, expected: &HubOp) -> Result<Option<NodeOp>, NodeError> {
        self.check_abandon()?;
        let repo = self.merged_repo_unchecked()?;
        let head = self.canonicalize(&LocalOp(repo.op_id().clone()))?;
        if head != expected.0 {
            return Ok(None);
        }
        let mut tx = repo.start_transaction();
        tx.set_attribute(FIXUP_ATTRIBUTE.to_owned(), "1".to_owned());
        let op = tx.commit("musubi: pass on jj op abandon").block_on()?;
        Ok(Some(NodeOp(
            self.canonicalize(&LocalOp(op.operation().id().clone()))?,
        )))
    }

    /// For tests of crashes: writes the fix-up's work by its first `written` copies, then
    /// stops, as a crash would, with the fix-up not yet written. It writes the rest of the
    /// work, and the forget after it, only when written again.
    pub fn crash_writing_fixup(&mut self, written: usize) -> Result<(), NodeError> {
        self.write_fixup_until(Some(written)).map(drop)
    }

    /// Restores only work whose operation the pending records removed before this machine
    /// received its publisher's fix-up. The original identity authenticates its timestamp
    /// in the retained record body; current presence supplies newer work and forgetting.
    fn repair_received_work(&mut self, head: &CanonicalOp) -> Result<(), NodeError> {
        if self.records.pending.is_empty() {
            return Ok(());
        }
        let mut sources = HashMap::new();
        for op in self.records.pending.ops() {
            if self.canonical.has_operation(&op.0) {
                sources.insert(self.canonical.original_id(&op.0)?, op.0.clone());
            }
        }
        let presence = self.presence(head)?;
        let mut repairs = vec![];
        for copy in presence.known() {
            let has_receipt_ghost = presence
                .ops_of(copy)
                .filter(|work| work.op.is_none())
                .any(|work| sources.contains_key(&work.original));
            if !has_receipt_ghost {
                continue;
            }
            let missing: Vec<_> = presence
                .worked(copy)
                .into_iter()
                .flatten()
                .filter(|work| work.op.is_none())
                .collect();
            if missing
                .iter()
                .any(|work| !sources.contains_key(&work.original))
            {
                continue;
            }
            let mut last = self.worked_at(&presence, copy)?;
            for work in missing {
                let millis = self.work_time(&sources[&work.original])?;
                last = Some(last.map_or(millis, |at| at.max(millis)));
            }
            repairs.push(Work {
                copy: copy.clone(),
                forget_after: presence
                    .has_forget_after(copy)
                    .then(|| format_forget_after(presence.forget_after(copy))),
                worked_at: last,
                forgotten: None,
            });
        }
        if repairs.is_empty() {
            return Ok(());
        }
        // Completed restoration stays in history. A new obligation must not replay its
        // settings or expected values; an unfinished recipe keeps its partial-write choices.
        let mut fixup = if self.records.fixup_written {
            Fixup::default()
        } else {
            self.records.fixup.clone().unwrap_or_default()
        };
        for repair in repairs {
            if let Some(work) = fixup.work.iter_mut().find(|work| work.copy == repair.copy) {
                // Current causal work may have an earlier clock time than an old recipe.
                work.worked_at = repair.worked_at;
            } else {
                fixup.work.push(repair);
            }
        }
        if !self.records.fixup_written && self.records.fixup.as_ref() == Some(&fixup) {
            return Ok(());
        }
        let checkpoint = self.records.checkpoint();
        if self.records.fixup_written {
            self.records.fixup_from = None;
        }
        self.records.fixup = Some(fixup);
        self.records.fixup_written = false;
        if let Err(err) = self.save_records() {
            self.records.restore(checkpoint);
            return Err(err);
        }
        Ok(())
    }

    /// [`Self::write_fixup`], stopping after `stop` operations if given.
    fn write_fixup_until(&mut self, stop: Option<usize>) -> Result<Option<NodeOp>, NodeError> {
        // Before reading the fix-up, which an abandon noticed now replaces, and not between
        // its operations.
        self.check_abandon()?;
        let head = self.merged_repo_unchecked()?;
        let canonical_head = self.canonicalize(&LocalOp(head.op_id().clone()))?;
        self.repair_received_work(&canonical_head)?;
        if self.records.fixup_written {
            return Ok(None);
        }
        let mut after_work: Vec<String> = vec![];
        // Which copies are forgotten at the op head, which may have operations above the
        // fix-up's `new`, as a forget not yet published: the fix-up leaves each so.
        if let Some(fixup) = &self.records.fixup
            && fixup.work.iter().any(|work| work.forgotten.is_none())
        {
            let presence = self.presence(&canonical_head)?;
            for work in &mut self.records.fixup.as_mut().expect("matched above").work {
                work.forgotten
                    .get_or_insert_with(|| !presence.is_present(&work.copy));
            }
            self.save_records()?;
        }
        let fixup = self.records.fixup.clone().unwrap_or_default();
        let shown = self.shown_names(&canonical_head)?;
        // The first operation restores them, so that no operation of the fix-up has them as
        // the rewritten history would.
        let mut first = Some((fixup.settings.clone(), self.expected_before(&head)?));
        let mut start = |repo: &Arc<ReadonlyRepo>| {
            let mut tx = repo.start_transaction();
            tx.set_attribute(FIXUP_ATTRIBUTE.to_owned(), "1".to_owned());
            if let Some((settings, expected)) = first.take() {
                if let Some(settings) = settings {
                    tx.set_attribute(hive_settings::ATTRIBUTE.to_owned(), settings);
                }
                if let Some(expected) = expected {
                    tx.set_attribute(git::EXPECTED_ATTRIBUTE.to_owned(), expected);
                }
            }
            tx
        };
        for (written, work) in fixup.work.iter().enumerate() {
            if stop == Some(written) {
                return Ok(None);
            }
            let repo = self.merged_repo_unchecked()?;
            let mut tx = start(&repo);
            tx.set_attribute(WORK_ATTRIBUTE.to_owned(), work.copy.clone());
            if let Some(after) = &work.forget_after {
                tx.set_attribute(FORGET_AFTER_ATTRIBUTE.to_owned(), after.clone());
            }
            if let Some(at) = work.worked_at {
                tx.set_attribute(WORKED_AT_ATTRIBUTE.to_owned(), at.to_string());
            }
            let display = if work.copy == self.machine.key() {
                self.machine.name().to_owned()
            } else {
                shown
                    .get(&work.copy)
                    .cloned()
                    .unwrap_or_else(|| work.copy.clone())
            };
            tx.commit(format!(
                "musubi: keep {display}'s last use after jj op abandon"
            ))
            .block_on()?;
            if work.forgotten == Some(true) {
                after_work.push(work.copy.clone());
            }
        }
        if stop.is_some() {
            return Ok(None);
        }
        let repo = self.merged_repo_unchecked()?;
        let mut tx = start(&repo);
        if !after_work.is_empty() {
            tx.set_attribute(FORGET_ATTRIBUTE.to_owned(), after_work.join(" "));
        }
        let op = tx.commit("musubi: pass on jj op abandon").block_on()?;
        self.records.fixup_written = true;
        self.save_records()?;
        Ok(Some(NodeOp(
            self.canonicalize(&LocalOp(op.operation().id().clone()))?,
        )))
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use std::collections::BTreeMap;

    use hegel::TestCase;
    use hegel::generators as gs;
    use jj_lib::content_hash::blake2b_hash;

    use super::*;

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
