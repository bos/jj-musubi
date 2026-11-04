//! Restoring presence, settings, and expected refs that an abandon dropped.

use std::collections::HashMap;
use std::sync::Arc;

use jj_lib::op_store::OperationId;
use jj_lib::ref_name::GitRefNameBuf;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use pollster::FutureExt as _;
use serde::Deserialize;
use serde::Serialize;

use super::FIXUP_ATTRIBUTE;
use super::NodeError;
use super::NodeOp;
use super::NodeRepo;
use super::WORKED_AT_ATTRIBUTE;

use crate::canonical;
use crate::hive_settings;
use crate::node::git;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
use crate::presence::FORGET_AFTER_ATTRIBUTE;
use crate::presence::FORGET_ATTRIBUTE;
use crate::presence::Presence;
use crate::presence::WORK_ATTRIBUTE;
use crate::presence::format_forget_after;
use crate::records::HubOp;

/// What a fix-up writes: work by each copy whose latest work or forget-after an abandon
/// dropped, then the hive's settings as they were (docs/internals/design.md, "The fix-up").
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(super) struct Fixup {
    pub(super) work: Vec<Work>,
    settings: Option<String>,
    #[serde(default)]
    pub(super) expected: Option<Expectation>,
}

/// The expected value of each conflicted remote bookmark at the op head as the history before
/// the abandon had it ([`NodeRepo::expectation`]).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(super) struct Expectation {
    /// The op head's local operation, rewritten.
    pub(super) at: String,
    /// Each one's git ref and value, as `git::expected_token` puts it.
    pub(super) values: Vec<(String, String)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(super) struct Work {
    pub(super) copy: String,
    forget_after: Option<String>,
    worked_at: Option<i64>,
    /// Whether a forget follows: whether the copy is forgotten at the op head the fix-up is
    /// written on. Decided as it starts, and kept, as by a fix-up that replaces it, since the
    /// fix-up's own work would make the copy present at the op head if it is written again
    /// after a crash.
    #[serde(default)]
    pub(super) forgotten: Option<bool>,
}

impl NodeRepo {
    /// What the fix-up must write for the state at `new`, the node-space rewrite of `old`,
    /// to be as it was at `old`. Presence is as it was (docs/internals/design.md, "Presence
    /// through an abandon"), but where a copy's latest work, or the `musubi.forget-after` it
    /// last recorded, is work the abandon dropped, the fix-up does it again, with when it was
    /// done and what it recorded, so that what comes after has it; then forgets the copy
    /// again if it is forgotten where the fix-up is written ([`Self::write_fixup`]).
    pub(super) fn fixup_between(
        &mut self,
        old: &CanonicalOp,
        new: &CanonicalOp,
    ) -> Result<Fixup, NodeError> {
        let before = self.presence(old)?;
        let after = self.presence(new)?;
        let mut fixup = Fixup::default();
        for copy in before.known().union(after.known()) {
            // If the whole accepted base was abandoned, its image can be the root: there
            // is then no surviving operation to stamp with the copies it knew.
            if after.known().contains(copy) && !after.ops_of(copy).any(|work| work.op.is_none()) {
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
    pub(in super::super) fn work_time(&self, op: &CanonicalOp) -> Result<i64, NodeError> {
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
    pub(in super::super) fn pending_expected(&self) -> git::Expected {
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
            let before = self
                .records
                .fixup_from
                .as_ref()
                .map(|head| self.presence(head))
                .transpose()?;
            let mut work = self
                .records
                .fixup
                .as_ref()
                .expect("matched above")
                .work
                .clone();
            for work in &mut work {
                if work.forgotten.is_some() {
                    continue;
                }
                // Unpublished work or a forget above the abandon takes precedence. A copy
                // lost with the entire base instead keeps its previous presence and use.
                if let Some(at) = self.worked_at(&presence, &work.copy)? {
                    work.worked_at = Some(at);
                }
                if presence.has_forget_after(&work.copy) {
                    work.forget_after =
                        Some(format_forget_after(presence.forget_after(&work.copy)));
                }
                let present = if presence.known().contains(&work.copy) {
                    presence.is_present(&work.copy)
                } else {
                    before
                        .as_ref()
                        .is_some_and(|before| before.is_present(&work.copy))
                };
                work.forgotten = Some(!present);
            }
            self.records.fixup.as_mut().expect("matched above").work = work;
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
