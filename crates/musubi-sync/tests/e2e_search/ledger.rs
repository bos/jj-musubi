//! Who rewrote what since the hive last fully converged. Whether a divergence or a conflict
//! is what jj does with the same operations is the reference's to say (`reference`); the
//! ledger tells the same rebase done twice, which the hub's sequencing exists to prevent,
//! from rewrites that commands make alike, and says in failure messages who rewrote what.
//!
//! Commands that the sequence runs are recorded: diffing what the machine saw at its op
//! heads before the command with what it sees after counts every change the command
//! rewrote, including descendants jj rebased and merges of concurrent operations. Changes
//! that musubi itself makes when it merges a node's work with the hub's are recorded apart,
//! as merges, by the commits they make.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use crate::view::View;

/// What a machine sees at its op heads, merged: the commits of each change.
#[derive(Clone, Default)]
pub struct Seen {
    changes: BTreeMap<String, BTreeSet<String>>,
}

impl Seen {
    pub fn of(views: &[View]) -> Self {
        let mut seen = Self::default();
        for view in views {
            for (change, commits) in view.changes() {
                seen.changes.entry(change).or_default().extend(commits);
            }
        }
        seen
    }
}

#[derive(Default)]
pub struct Ledger {
    /// Changes whose commits each machine's commands changed.
    rewrites: BTreeMap<String, BTreeSet<usize>>,
    /// Changes whose commits each node's own merges changed: commits that first appeared
    /// during that node's sync, so no command made them and no other node realized them.
    merges: BTreeMap<String, BTreeSet<usize>>,
    /// Every commit seen so far.
    known: BTreeSet<String>,
    /// The commands and merges that rewrote each change, for failure messages.
    history: BTreeMap<String, Vec<String>>,
    /// Changes a command at an older operation rewrote.
    at_op: BTreeSet<String>,
    /// Changes that branches were moved to with git.
    git_targets: BTreeSet<String>,
    /// Divergence already present at the last full convergence.
    divergent_before: BTreeSet<String>,
}

impl Ledger {
    /// Forgets everything, once the hive has fully converged on `view`.
    pub fn reset(&mut self, view: &View) {
        *self = Self {
            divergent_before: view.divergent(),
            known: view.commits.iter().map(|c| c.id.clone()).collect(),
            ..Self::default()
        };
    }

    /// Records what machine `m` sees after a sync: commits no one has seen before were
    /// made by its node's merges.
    pub fn record_sync(&mut self, m: usize, what: &str, after: &Seen) {
        for (change, commits) in &after.changes {
            for commit in commits {
                if self.known.insert(commit.clone()) {
                    self.merges.entry(change.clone()).or_default().insert(m);
                    self.history
                        .entry(change.clone())
                        .or_default()
                        .push(what.to_owned());
                }
            }
        }
    }

    /// Records a command on machine `m` that went from `before` to `after`.
    pub fn record(&mut self, m: usize, what: &str, before: &Seen, after: &Seen, at_op: bool) {
        let empty = BTreeSet::new();
        let rewritten: BTreeSet<String> = before
            .changes
            .keys()
            .chain(after.changes.keys())
            .filter(|c| {
                before.changes.get(*c).unwrap_or(&empty) != after.changes.get(*c).unwrap_or(&empty)
            })
            .cloned()
            .collect();
        self.known.extend(after.changes.values().flatten().cloned());
        for change in &rewritten {
            self.rewrites.entry(change.clone()).or_default().insert(m);
            self.history
                .entry(change.clone())
                .or_default()
                .push(what.to_owned());
        }
        if at_op {
            self.at_op.extend(rewritten);
        }
    }

    /// Records a branch moved with git to a commit of change `target`.
    pub fn git_move(&mut self, target: Option<&str>) {
        self.git_targets.extend(target.map(str::to_owned));
    }

    /// The divergent changes in `view` that look like the same rebase done twice: two
    /// visible commits of a change with the same parents, description and contents, neither
    /// rewritten from the other (as `copy_of` says of two commit ids), which is what two
    /// nodes merging the same concurrent operations would produce. Two machines' commands
    /// can do that too, by rewriting a commit the same way, as can a command at an older
    /// operation, or a snapshot of a commit git moved a branch to, which jj imports beside
    /// the snapshot; so can jj rebasing two rewrites of a change onto the same parents, or a
    /// command and a merge rebasing it alike, which `Reference::same_rebase_twice` tells
    /// apart.
    pub fn alike_commits(&self, view: &View, copy_of: impl Fn(&str, &str) -> bool) -> Vec<String> {
        let mut alike = vec![];
        for change in view.divergent() {
            let mut copies: BTreeMap<(&Vec<String>, &String), Vec<&str>> = BTreeMap::new();
            for commit in view.commits.iter().filter(|c| c.change == change) {
                copies
                    .entry((&commit.parents, &commit.subject))
                    .or_default()
                    .push(&commit.id);
            }
            let twice = copies.values().any(|ids| {
                ids.iter()
                    .enumerate()
                    .any(|(i, a)| ids[i + 1..].iter().any(|b| copy_of(a, b)))
            });
            let commanded = self.rewrites.get(&change).map_or(0, BTreeSet::len);
            if twice
                && commanded < 2
                && !self.at_op.contains(&change)
                && !self.git_targets.contains(&change)
                && !self.divergent_before.contains(&change)
            {
                alike.push(change);
            }
        }
        alike
    }

    /// Machines whose commands or merges rewrote `change`, for failure messages.
    pub fn rewriters(&self, change: &str) -> BTreeSet<usize> {
        let mut machines = self.rewrites.get(change).cloned().unwrap_or_default();
        machines.extend(self.merges.get(change).into_iter().flatten());
        machines
    }

    /// The commands that rewrote `change`.
    pub fn history(&self, change: &str) -> &[String] {
        self.history.get(change).map_or(&[], Vec::as_slice)
    }
}
