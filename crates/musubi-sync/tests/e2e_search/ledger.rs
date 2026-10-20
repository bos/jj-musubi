//! Who changed what since the hive last fully converged, for the properties that state the
//! race catalogue's outcomes generally:
//!
//! - no spurious divergence: a change is divergent only if at least two machines rewrote it,
//!   or a command at an older operation did (a concurrent operation on one machine, which
//!   jj itself resolves into divergence);
//! - no spurious conflict: a bookmark or tag is conflicted only if at least two machines
//!   changed it, or git moved it, or a command at an older operation did.
//!
//! Only `jj` commands that the sequence runs are recorded: diffing what the machine saw at
//! its op heads before the command with what it sees after counts every change the command
//! rewrote, including descendants jj rebased and merges of concurrent operations. Changes
//! that musubi itself makes when it merges a node's work with the hub's are deliberately not
//! recorded: they must never be the reason anything diverges or conflicts, which is what the
//! hub's sequencing guarantees.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use crate::view::View;

/// What a machine sees at its op heads, merged: the commits of each change, and the
/// targets of each bookmark and tag at any head.
#[derive(Clone, Default)]
pub struct Seen {
    changes: BTreeMap<String, BTreeSet<String>>,
    bookmarks: BTreeMap<String, BTreeSet<BTreeSet<String>>>,
    tags: BTreeMap<String, BTreeSet<BTreeSet<String>>>,
}

impl Seen {
    pub fn of(views: &[View]) -> Self {
        let mut seen = Self::default();
        let bookmarks: Vec<_> = views.iter().map(View::bookmark_targets).collect();
        let tags: Vec<_> = views.iter().map(View::tag_targets).collect();
        for view in views {
            for (change, commits) in view.changes() {
                seen.changes.entry(change).or_default().extend(commits);
            }
        }
        // An absent name is a value too: creating a bookmark changes it.
        for (all, per_view) in [(&mut seen.bookmarks, &bookmarks), (&mut seen.tags, &tags)] {
            let names: BTreeSet<&String> = per_view.iter().flat_map(BTreeMap::keys).collect();
            for name in names {
                for targets in per_view {
                    all.entry(name.clone())
                        .or_default()
                        .insert(targets.get(name).cloned().unwrap_or_default());
                }
            }
        }
        seen
    }
}

fn changed_names(
    before: &BTreeMap<String, BTreeSet<BTreeSet<String>>>,
    after: &BTreeMap<String, BTreeSet<BTreeSet<String>>>,
) -> BTreeSet<String> {
    let empty = BTreeSet::from([BTreeSet::new()]);
    before
        .keys()
        .chain(after.keys())
        .filter(|name| before.get(*name).unwrap_or(&empty) != after.get(*name).unwrap_or(&empty))
        .cloned()
        .collect()
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
    /// The commands that rewrote each change, for failure messages.
    history: BTreeMap<String, Vec<String>>,
    bookmarks: BTreeMap<String, BTreeSet<usize>>,
    tags: BTreeMap<String, BTreeSet<usize>>,
    /// Changes, bookmarks, and tags a command at an older operation changed.
    at_op: BTreeSet<String>,
    at_op_bookmarks: BTreeSet<String>,
    at_op_tags: BTreeSet<String>,
    /// Branches moved or deleted with git, and the changes they were moved to.
    git_moves: BTreeSet<String>,
    git_targets: BTreeSet<String>,
    /// Divergence and conflicts already present at the last full convergence.
    divergent_before: BTreeSet<String>,
    conflicted_before: BTreeSet<String>,
}

impl Ledger {
    /// Forgets everything, once the hive has fully converged on `view`.
    pub fn reset(&mut self, view: &View) {
        *self = Self {
            divergent_before: view.divergent(),
            conflicted_before: conflicted(view),
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
        let bookmarks = changed_names(&before.bookmarks, &after.bookmarks);
        let tags = changed_names(&before.tags, &after.tags);
        self.known.extend(after.changes.values().flatten().cloned());
        for change in &rewritten {
            self.rewrites.entry(change.clone()).or_default().insert(m);
            self.history
                .entry(change.clone())
                .or_default()
                .push(what.to_owned());
        }
        for name in &bookmarks {
            self.bookmarks.entry(name.clone()).or_default().insert(m);
        }
        for name in &tags {
            self.tags.entry(name.clone()).or_default().insert(m);
        }
        if at_op {
            self.at_op.extend(rewritten);
            self.at_op_bookmarks.extend(bookmarks);
            self.at_op_tags.extend(tags);
        }
    }

    /// Records a branch moved with git to a commit of change `target`, or deleted.
    pub fn git_move(&mut self, branch: &str, target: Option<&str>) {
        self.git_moves.insert(branch.to_owned());
        self.git_targets.extend(target.map(str::to_owned));
    }

    /// The divergent changes in `view` that something explains: two machines, or a command
    /// at an older operation, rewrote them; or they descend from such a change, or are
    /// kept visible beneath one.
    pub fn explained_divergence(&self, view: &View) -> BTreeSet<String> {
        let divergent = view.divergent();
        let mut explained: BTreeSet<String> = divergent
            .iter()
            .filter(|change| {
                self.divergent_before.contains(*change)
                    || self.at_op.contains(*change)
                    || self.rewriting_machines(change).len() >= 2
                    // A branch moved with git to a commit that a snapshot then rewrites:
                    // jj imports the branch in its own operation, keeping the old commit
                    // visible beside the new one. jj does this on one machine, too.
                    || self.git_targets.contains(*change)
            })
            .cloned()
            .collect();
        let change_of: BTreeMap<&str, &str> = view
            .commits
            .iter()
            .map(|c| (c.id.as_str(), c.change.as_str()))
            .collect();
        // Every rewrite of a commit rebases its descendants, so when two machines rewrite a
        // commit, each rebases the descendants it knows of, and a descendant that only one
        // of them knew of is rebased the other way when the hub's sequencing has a node
        // merge the two: once each way, and the descendant diverges too. And some commits
        // keep rewritten ancestors visible beside their new versions: a branch moved with
        // git to a commit the hive has since rewritten, which jj imports; a conflicted
        // bookmark or tag, which keeps every commit it might point to visible (and merging
        // over one turns the commits it moved away from into ones it might point to); and a
        // divergent commit's descendants, which jj leaves where they are when it merges
        // operations, since it can't tell which of the change's commits replaced their
        // parent. jj does all of this on one machine, with concurrent operations.
        let held: BTreeSet<String> = view
            .conflicted_names()
            .iter()
            .filter(|conflicted| self.conflict_explained(conflicted))
            .filter_map(|conflicted| conflict_targets(view, conflicted))
            .flatten()
            .collect();
        loop {
            let before = explained.len();
            for commit in &view.commits {
                let ancestors = view.ancestors(&commit.id);
                if self.git_targets.contains(&commit.change)
                    || held.contains(&commit.id)
                    || explained.contains(&commit.change)
                {
                    for ancestor in &ancestors {
                        if let Some(change) = change_of.get(ancestor.as_str())
                            && divergent.contains(*change)
                        {
                            explained.insert((*change).to_owned());
                        }
                    }
                }
                if divergent.contains(&commit.change)
                    && ancestors.iter().any(|a| {
                        *a != commit.id
                            && change_of
                                .get(a.as_str())
                                .is_some_and(|c| explained.contains(*c))
                    })
                {
                    explained.insert(commit.change.clone());
                }
            }
            if explained.len() == before {
                break;
            }
        }
        explained
    }

    /// Machines whose commands or merges rewrote `change`.
    fn rewriting_machines(&self, change: &str) -> BTreeSet<usize> {
        let mut machines = self.rewrites.get(change).cloned().unwrap_or_default();
        machines.extend(self.merges.get(change).into_iter().flatten());
        machines
    }

    /// The divergent changes in `view` that nothing explains, and those that look like the
    /// same rebase done twice: two visible commits of a change with the same parents,
    /// description and contents (as `same_contents` says of two commit ids), which is what
    /// two nodes merging the same concurrent operations would produce, and which the hub's
    /// sequencing exists to prevent. (Two machines' commands can do that too, by rewriting
    /// a commit the same way, which explains it.)
    pub fn spurious_divergence(
        &self,
        view: &View,
        same_contents: impl Fn(&str, &str) -> bool,
    ) -> Vec<String> {
        let explained = self.explained_divergence(view);
        let mut spurious = vec![];
        for change in view.divergent() {
            if !explained.contains(&change) {
                spurious.push(change);
                continue;
            }
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
                    .any(|(i, a)| ids[i + 1..].iter().any(|b| same_contents(a, b)))
            });
            let commanded = self.rewrites.get(&change).map_or(0, BTreeSet::len);
            if twice
                && commanded < 2
                && !self.at_op.contains(&change)
                && !self.git_targets.contains(&change)
                && !self.divergent_before.contains(&change)
            {
                spurious.push(format!("{change} (the same rebase twice)"));
            }
        }
        spurious
    }

    /// The conflicted bookmarks and tags in `view` that nothing explains.
    ///
    /// `abandoned_merge` says whether a conflicted name (as `View::conflicted_names` names
    /// it) conflicts only because a merge commit it pointed to was abandoned: jj moves a
    /// bookmark on an abandoned commit to the commit's parents, so to several at once from
    /// a merge, even when the abandon and the bookmark were concurrent.
    pub fn spurious_conflicts(
        &self,
        view: &View,
        abandoned_merge: impl Fn(&str) -> bool,
    ) -> Vec<String> {
        let divergence = self.explained_divergence(view);
        let mut spurious = vec![];
        for conflicted in view.conflicted_names() {
            // A bookmark on a divergent commit moves with each rewrite, so it conflicts
            // whenever the divergence does.
            let on_divergence = conflict_targets(view, &conflicted).is_some_and(|ids| {
                view.commits
                    .iter()
                    .any(|c| ids.contains(&c.id) && divergence.contains(&c.change))
            });
            if !on_divergence
                && !self.conflict_explained(&conflicted)
                && !abandoned_merge(&conflicted)
            {
                let (kind, name) = conflicted.split_once(' ').unwrap();
                let changers = if kind == "bookmark" {
                    self.bookmarks.get(name)
                } else {
                    self.tags.get(name)
                };
                spurious.push(format!("{conflicted} (changed by {changers:?})"));
            }
        }
        spurious
    }

    /// Whether something other than divergence explains why a bookmark or tag
    /// (`conflicted`, as `View::conflicted_names` names it) conflicts: two machines, git,
    /// or a command at an older operation changed it, or it already conflicted.
    fn conflict_explained(&self, conflicted: &str) -> bool {
        let (kind, name) = conflicted.split_once(' ').unwrap();
        let (changers, at_op) = if kind == "bookmark" {
            (self.bookmarks.get(name), &self.at_op_bookmarks)
        } else {
            (self.tags.get(name), &self.at_op_tags)
        };
        self.conflicted_before.contains(conflicted)
            || at_op.contains(name)
            || (kind == "bookmark" && self.git_moves.contains(name))
            || changers.is_some_and(|ms| ms.len() >= 2)
    }

    /// Who rewrote `change`, for failure messages.
    pub fn rewriters(&self, change: &str) -> BTreeSet<usize> {
        self.rewriting_machines(change)
    }

    /// The commands that rewrote `change`.
    pub fn history(&self, change: &str) -> &[String] {
        self.history.get(change).map_or(&[], Vec::as_slice)
    }
}

fn conflicted(view: &View) -> BTreeSet<String> {
    view.conflicted_names()
}

/// The commits a conflicted bookmark or tag (`conflicted`, as `View::conflicted_names` names
/// it) might point to.
fn conflict_targets(view: &View, conflicted: &str) -> Option<BTreeSet<String>> {
    let (kind, name) = conflicted.split_once(' ')?;
    let mut targets = if kind == "bookmark" {
        view.bookmark_targets()
    } else {
        view.tag_targets()
    };
    targets.remove(name)
}
