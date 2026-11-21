//! Recovery a user or daemon can perform from a supported refusal. A repeated recovery,
//! an unrecognized failure, or work returning without an independent native witness remains
//! a test failure.

use std::collections::BTreeMap;

use jj_lib::object_id::ObjectId as _;
use musubi_jj::node::NodeError;

use super::MAX_RECOVERIES;
use super::OperationHistory;
use super::World;

impl World {
    /// Recovers from a sync of node `m` that failed, as a user would from what it says: from a
    /// known jj limitation (docs/internals/races.md), where jj can't merge this machine's operations
    /// with the hive's, so musubi pauses, by reverting the operation the
    /// error names, or where it names none, as a user given its list would: the newest, other
    /// than the recovery's own. Fails the case on any other error, or if the operation to
    /// revert is one already reverted, or a revert the recovery made: reverting it would put
    /// back what it reverted.
    pub(super) fn recover(&mut self, m: usize, what: &str, err: &anyhow::Error) {
        let found = err
            .chain()
            .find_map(|e| match e.downcast_ref::<NodeError>() {
                Some(NodeError::Unmergeable { ours, culprit, .. }) => {
                    Some((ours.clone(), culprit.clone()))
                }
                _ => None,
            });
        let Some((ours, culprit)) = found else {
            // Several errors share a message: name which.
            let which = err
                .chain()
                .find_map(|e| e.downcast_ref::<NodeError>())
                .map(|e| format!(" ({e:?})"))
                .unwrap_or_default();
            self.fail(&format!(
                "{what} of {} failed: {err:#}{which}",
                self.machine(m)
            ));
        };
        let ops = self.op_summaries(m);
        let op = match culprit {
            Some(op) => Some(op.0.hex()).filter(|op| !self.recovery_ops.contains(op)),
            // As `can_undo` does, skip merges, which jj refuses to revert, and workspace
            // operations, which rewrite no commits, so they can't be what jj fails to
            // merge, and which strand a working copy when reverted.
            None => ours.iter().map(|op| op.0.hex()).find(|op| {
                !self.recovery_ops.contains(op)
                    && ops.get(op).is_some_and(|(parents, description)| {
                        *parents == 1 && !description.to_lowercase().contains("workspace")
                    })
            }),
        };
        let Some(op) = op.filter(|_| self.recovery_actions < MAX_RECOVERIES) else {
            self.fail(&format!(
                "{what} of {} keeps failing: {err:#}",
                self.machine(m)
            ));
        };
        self.recovery_actions += 1;
        self.jj(m, &["op", "revert", &op]);
        let written: Vec<String> = self
            .op_summaries(m)
            .into_keys()
            .filter(|id| !ops.contains_key(id))
            .collect();
        self.recovery_ops.insert(op);
        self.recovery_ops.extend(written);
    }

    /// Every operation in machine `m`'s operation log, by hex id, with its number of parents
    /// and the first line of its description.
    fn op_summaries(&self, m: usize) -> BTreeMap<String, (usize, String)> {
        self.raw_jj(
            m,
            &[
                "--ignore-working-copy",
                "op",
                "log",
                "--no-graph",
                "-T",
                r#"id ++ "\t" ++ parents.len() ++ "\t" ++ description.first_line() ++ "\n""#,
            ],
        )
        .lines()
        .filter_map(|line| {
            let mut fields = line.splitn(3, '\t');
            let id = fields.next()?;
            let parents = fields.next()?.parse().ok()?;
            Some((id.to_owned(), (parents, fields.next()?.to_owned())))
        })
        .collect()
    }

    /// Takes an abandoned operation that a `jj` command on machine `m` brought back into its
    /// history, absent before it, for jj's doing, not musubi's, which runs no command: with
    /// auto-update-stale, a command in a workspace whose working copy recorded an operation
    /// `jj op abandon` rewrote brings back what it abandoned, as on one machine
    /// (docs/internals/races.md, "Known jj limitations"). jj leaves a working copy so where
    /// the abandon ran in another workspace, or where an operation came after its last
    /// command, as musubi's do. `before` is `abandoned_present` from before the command.
    pub(super) fn forgive_jj_returns(&mut self, m: usize, before: Option<OperationHistory>) {
        let Some(before) = before else {
            return;
        };
        let exact = !self.abandoned.is_empty();
        let after = self.operation_history(m, exact);
        let copy = self.fx.machine_key(m);
        for op in self
            .abandoned
            .iter_mut()
            .filter(|op| op.originals.is_none())
        {
            for id in after.native_by_header.get(&op.header).into_iter().flatten() {
                if before.native.contains(id) {
                    continue;
                }
                let original = after.native_originals.get(id);
                let absent = match original {
                    Some(id) => {
                        !before.originals.contains(id) && !before.unknown.contains(&op.header)
                    }
                    None => !before.headers.contains(&op.header),
                };
                if absent {
                    let key = (copy.clone(), id.clone());
                    op.native_witnesses.entry(key.clone()).or_insert(None);
                    if let Some(original) = original {
                        op.qualify_native(&key, original.clone());
                    }
                }
            }
        }
        let count = self.abandoned.len();
        self.abandoned
            .retain(|op| before.may_contain(op) || !after.proves_present(op));
        if self.abandoned.len() < count {
            self.record("  (jj brought back an abandoned operation)".to_owned());
        }
    }

    /// A native command can resume old history on any copy. Unknown aliases prevent
    /// proving prior absence; only an exact native id or original proves a return.
    pub(super) fn abandoned_present(&self, m: usize) -> Option<OperationHistory> {
        (!self.abandoned.is_empty()).then(|| self.operation_history(m, true))
    }
}
