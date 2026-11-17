//! Structural equality and excess divergence/conflicts between hive and native jj views.
//!
//! Commit ids are unsuitable for equality: jj records replay times in rebased commits.
//! These comparisons retain contents, parent structure and existing change identities,
//! while treating newly created working-copy identities as fresh on either side.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::Hash;
use std::hash::Hasher as _;
use std::sync::Arc;

use futures::executor::block_on;
use jj_lib::backend::ChangeId;
use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::RefTarget;
use jj_lib::op_store::View;
use jj_lib::operation::Operation;

use super::Reference;

/// What the reference needs of a commit, read once.
pub(super) struct Facts {
    pub(super) change: ChangeId,
    pub(super) parents: Vec<CommitId>,
    /// Tree, description and author, but not the author's time.
    pub(super) content: u64,
    /// The author's time, unless jj resets it in a rewrite.
    pub(super) author_time: Option<(i64, i32)>,
}

/// A name's target's terms, added and removed, by structural key, each sorted.
pub(super) type Terms = (Vec<Option<u64>>, Vec<Option<u64>>);

/// A view as agreement compares it, with commits as structural keys (`Reference::keys`).
#[derive(PartialEq, Eq, Debug, Default)]
pub(super) struct Summary {
    pub(super) visible: BTreeMap<u64, usize>,
    pub(super) refs: BTreeMap<String, Terms>,
}

pub(super) fn hash(value: impl Hash) -> u64 {
    let mut hasher = std::hash::DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

/// A view's heads, for caching what's visible in it.
pub(super) fn heads_key(view: &View) -> Vec<u8> {
    let mut heads: Vec<&CommitId> = view.head_ids.iter().collect();
    heads.sort();
    heads
        .into_iter()
        .flat_map(|head| head.as_bytes())
        .copied()
        .collect()
}

/// Every bookmark, tag and remote bookmark (outside the `git` pseudo-remote, which
/// canonical views don't have), as `bookmark <name>`, `tag <name>` and
/// `remote <name>@<remote> <state>`.
pub(super) fn refs(view: &View) -> BTreeMap<String, RefTarget> {
    let mut refs = BTreeMap::new();
    for (name, target) in &view.local_bookmarks {
        refs.insert(format!("bookmark {}", name.as_str()), target.clone());
    }
    for (name, target) in &view.local_tags {
        refs.insert(format!("tag {}", name.as_str()), target.clone());
    }
    for (remote, remote_view) in &view.remote_views {
        for (name, remote_ref) in &remote_view.bookmarks {
            refs.insert(
                format!(
                    "remote {}@{} {:?}",
                    name.as_str(),
                    remote.as_str(),
                    remote_ref.state
                ),
                remote_ref.target.clone(),
            );
        }
    }
    refs
}

pub(super) fn show_target(target: Option<&RefTarget>) -> String {
    match target {
        None => "absent".to_owned(),
        Some(target) => target
            .iter()
            .map(|id| {
                id.as_ref()
                    .map_or("-".to_owned(), |id| id.hex()[..12].to_owned())
            })
            .collect::<Vec<_>>()
            .join(","),
    }
}

impl Reference {
    pub(super) fn facts(&mut self, id: &CommitId) -> &Facts {
        if !self.facts.contains_key(id) {
            let commit = self.loader.store().get_commit(id).unwrap();
            let author = commit.author();
            let content = hash((
                format!("{:?}", commit.tree_ids()),
                commit.description(),
                &author.name,
                &author.email,
            ));
            let facts = Facts {
                change: commit.change_id().clone(),
                parents: commit.parent_ids().to_vec(),
                content,
                // jj resets the author's time when it rewrites a discardable commit, one
                // that is empty with no description, as it rebases a working copy.
                author_time: (!commit.description().is_empty())
                    .then_some((author.timestamp.timestamp.0, author.timestamp.tz_offset)),
            };
            self.facts.insert(id.clone(), facts);
        }
        &self.facts[id]
    }

    /// How many visible commits each change has in `view`, by jj's change id.
    pub(super) fn change_counts(&mut self, view: &View) -> BTreeMap<String, usize> {
        let mut counts = BTreeMap::new();
        for id in self.visible(view).iter() {
            *counts
                .entry(self.facts(id).change.reverse_hex())
                .or_default() += 1;
        }
        counts
    }

    /// How `view`, the hive's, differs from `replaced`, a machine's view of the operation an
    /// operation replaced, exactly as `check_realizations` holds a machine's operation to the
    /// hive's: a realization has the same heads; an operation of the machine's own has no
    /// commit visible that the hive's hides; either has the same bookmarks and tags.
    pub(super) fn unlike_replaced(
        &mut self,
        replaced: &View,
        realized: bool,
        view: &View,
    ) -> Option<String> {
        let short = |ids: &mut Vec<String>| {
            ids.sort();
            ids.clone()
        };
        let mut why = vec![];
        let theirs = self.visible(view);
        if realized {
            if replaced.head_ids != view.head_ids {
                why.push("the heads differ".to_owned());
            }
        } else {
            // Checked before walking: the reference's store may lack what the hive hides.
            let mut lacked: Vec<String> = replaced
                .head_ids
                .iter()
                .filter(|c| !theirs.contains(*c))
                .map(|c| c.hex()[..12].to_owned())
                .collect();
            if lacked.is_empty() {
                let ours = self.visible(replaced);
                lacked = ours
                    .difference(&theirs)
                    .map(|c| c.hex()[..12].to_owned())
                    .collect();
            }
            if !lacked.is_empty() {
                why.push(format!("the hive's hides {:?}", short(&mut lacked)));
            }
        }
        if replaced.local_bookmarks != view.local_bookmarks {
            why.push("bookmarks differ".to_owned());
        }
        if replaced.local_tags != view.local_tags {
            why.push("tags differ".to_owned());
        }
        (!why.is_empty()).then(|| why.join(", "))
    }

    /// The commits visible in `view`, the root's aside.
    pub(super) fn visible(&mut self, view: &View) -> Arc<HashSet<CommitId>> {
        let key = heads_key(view);
        if let Some(found) = self.visible.get(&key) {
            return found.clone();
        }
        let root = self.loader.store().root_commit_id().clone();
        let mut found = HashSet::new();
        let mut pending: Vec<CommitId> = view.head_ids.iter().cloned().collect();
        while let Some(id) = pending.pop() {
            if id == root || !found.insert(id.clone()) {
                continue;
            }
            pending.extend(self.facts(&id).parents.clone());
        }
        let found = Arc::new(found);
        self.visible.insert(key, found.clone());
        found
    }

    /// The changes visible at any of `ops`.
    pub(super) fn changes_of<'a>(
        &mut self,
        ops: impl Iterator<Item = &'a Operation>,
    ) -> HashSet<ChangeId> {
        let mut changes = HashSet::new();
        for op in ops {
            let view = block_on(self.loader.op_store().read_view(op.view_id())).unwrap();
            for id in self.visible(&view).iter() {
                changes.insert(self.facts(id).change.clone());
            }
        }
        changes
    }

    /// Structural keys for `ids` and their ancestors: a commit's change id (unless the
    /// change is new, not `known`), contents, author time (likewise), and parents' keys.
    pub(super) fn keys(
        &mut self,
        ids: &[CommitId],
        known: &dyn Fn(&ChangeId) -> bool,
    ) -> HashMap<CommitId, u64> {
        let root = self.loader.store().root_commit_id().clone();
        let mut keys: HashMap<CommitId, u64> = HashMap::from([(root, 0)]);
        let mut pending: Vec<CommitId> = ids.to_vec();
        while let Some(id) = pending.last().cloned() {
            if keys.contains_key(&id) {
                pending.pop();
                continue;
            }
            let parents = self.facts(&id).parents.clone();
            let missing: Vec<CommitId> = parents
                .iter()
                .filter(|p| !keys.contains_key(*p))
                .cloned()
                .collect();
            if !missing.is_empty() {
                pending.extend(missing);
                continue;
            }
            pending.pop();
            let facts = self.facts(&id);
            let new = !known(&facts.change);
            let key = hash((
                (!new).then(|| facts.change.clone()),
                facts.content,
                facts.author_time.filter(|_| !new),
                parents.iter().map(|p| keys[p]).collect::<Vec<_>>(),
            ));
            keys.insert(id, key);
        }
        keys
    }

    pub(super) fn summary(&mut self, view: &View, known: &HashSet<ChangeId>) -> Summary {
        let visible: Vec<CommitId> = self.visible(view).iter().cloned().collect();
        let named: Vec<CommitId> = refs(view)
            .values()
            .flat_map(|target| target.iter().flatten().cloned())
            .collect();
        let all: Vec<CommitId> = visible.iter().chain(&named).cloned().collect();
        let keys = self.keys(&all, &|change| known.contains(change));
        let mut summary = Summary::default();
        for id in &visible {
            *summary.visible.entry(keys[id]).or_default() += 1;
        }
        // A conflict's terms in any order are the same conflict: jj's merges order them by
        // the order they merge operations in.
        let key = |id: &Option<CommitId>| id.as_ref().map(|id| keys[id]);
        for (name, target) in refs(view) {
            let mut adds: Vec<Option<u64>> = target.adds().map(key).collect();
            let mut removes: Vec<Option<u64>> = target.removes().map(key).collect();
            adds.sort();
            removes.sort();
            summary.refs.insert(name, (adds, removes));
        }
        summary
    }

    /// How `view`, the hive's, differs from `replayed`, the reference's, for messages.
    pub(super) fn difference(
        &mut self,
        view: &View,
        replayed: &View,
        known: &HashSet<ChangeId>,
    ) -> String {
        let ours = self.summary(view, known);
        let theirs = self.summary(replayed, known);
        let mut out = vec![];
        let mut described = |side: &str, view: &View, summary: &Summary, other: &Summary| {
            let visible: Vec<CommitId> = self.visible(view).iter().cloned().collect();
            let keys = self.keys(&visible, &|change| known.contains(change));
            let mut only: Vec<String> = visible
                .iter()
                .filter(|id| {
                    summary.visible.get(&keys[*id]) > other.visible.get(&keys[*id]).or(Some(&0))
                })
                .map(|id| {
                    let workspaces: Vec<&str> = view
                        .wc_commit_ids
                        .iter()
                        .filter(|(_, wc)| *wc == id)
                        .map(|(name, _)| name.as_str())
                        .collect();
                    let commit = self.loader.store().get_commit(id).unwrap();
                    let parents: Vec<String> = commit
                        .parent_ids()
                        .iter()
                        .map(|p| p.hex()[..12].to_owned())
                        .collect();
                    format!(
                        "{} ({}, on {}, {:?}{})",
                        &id.hex()[..12],
                        &self.facts(id).change.reverse_hex()[..12],
                        parents.join("+"),
                        commit.description().lines().next().unwrap_or_default(),
                        if workspaces.is_empty() {
                            String::new()
                        } else {
                            format!(", working copy of {}", workspaces.join(","))
                        }
                    )
                })
                .collect();
            only.sort();
            if !only.is_empty() {
                out.push(format!("visible only {side}: {}", only.join(", ")));
            }
        };
        described("in the hive", view, &ours, &theirs);
        described("in jj's", replayed, &theirs, &ours);
        let names: BTreeSet<&String> = ours.refs.keys().chain(theirs.refs.keys()).collect();
        let (view_refs, replayed_refs) = (refs(view), refs(replayed));
        for name in names {
            if ours.refs.get(name) != theirs.refs.get(name) {
                out.push(format!(
                    "{name}: {} in the hive, {} in jj's",
                    show_target(view_refs.get(name)),
                    show_target(replayed_refs.get(name))
                ));
            }
        }
        out.join("; ")
    }

    /// What `hive`, a view of the hive's, has beyond `jj`, the reference's view where the
    /// two had the same operations: changes that diverge into commits `jj` doesn't have as
    /// many of, as change ids name them, and bookmarks and tags conflicted with terms `jj`'s
    /// targets lack. Commits are compared by structural key, those of changes not `known`
    /// by all but their change ids.
    pub(super) fn beyond(
        &mut self,
        hive: &View,
        jj: &View,
        known: &HashSet<ChangeId>,
    ) -> Vec<String> {
        let (hive_visible, jj_visible) = (self.visible(hive), self.visible(jj));
        let (hive_refs, jj_refs) = (refs(hive), refs(jj));
        let all: Vec<CommitId> = hive_visible
            .iter()
            .chain(jj_visible.iter())
            .chain(
                hive_refs
                    .values()
                    .chain(jj_refs.values())
                    .flat_map(|target| target.iter().flatten()),
            )
            .cloned()
            .collect();
        let keys = self.keys(&all, &|change| known.contains(change));
        let mut by_change =
            |visible: &HashSet<CommitId>| -> BTreeMap<String, BTreeMap<u64, usize>> {
                let mut by_change: BTreeMap<String, BTreeMap<u64, usize>> = BTreeMap::new();
                for id in visible {
                    let change = self.facts(id).change.reverse_hex();
                    *by_change
                        .entry(change)
                        .or_default()
                        .entry(keys[id])
                        .or_default() += 1;
                }
                by_change
            };
        let (hive_changes, jj_changes) = (by_change(&hive_visible), by_change(&jj_visible));
        let within = |ours: &BTreeMap<u64, usize>, theirs: Option<&BTreeMap<u64, usize>>| {
            ours.iter()
                .all(|(key, n)| theirs.and_then(|t| t.get(key)).is_some_and(|m| m >= n))
        };
        let mut beyond = vec![];
        for (change, commits) in &hive_changes {
            if commits.values().sum::<usize>() > 1 && !within(commits, jj_changes.get(change)) {
                beyond.push(format!("{change} diverges"));
            }
        }
        let terms = |target: &RefTarget| -> BTreeMap<u64, usize> {
            let mut terms = BTreeMap::new();
            // Added terms and removed ones apart, absent ones included.
            for (i, id) in target.iter().enumerate() {
                let key = hash((i % 2, id.as_ref().map(|id| keys[id])));
                *terms.entry(key).or_default() += 1;
            }
            terms
        };
        for (name, target) in &hive_refs {
            if name.starts_with("remote ") || target.is_resolved() {
                continue;
            }
            let theirs = jj_refs
                .get(name)
                .filter(|target| !target.is_resolved())
                .map(terms);
            if !within(&terms(target), theirs.as_ref()) {
                beyond.push(format!("{name} conflicts"));
            }
        }
        beyond
    }

    /// What the hive's head has beyond the reference's (`beyond`): divergence and conflicts
    /// jj wouldn't make of the same operations. Changes visible at only one of them count as
    /// new, as jj's and musubi's working-copy commits for an abandoned one are.
    pub fn beyond_jj(&mut self) -> Vec<String> {
        let read = |op: &Operation| block_on(self.loader.op_store().read_view(op.view_id()));
        let (hive, jj) = (
            read(&self.head_copy).unwrap(),
            read(&self.head_replay).unwrap(),
        );
        let changes = |reference: &mut Self, view: &View| -> HashSet<ChangeId> {
            let visible = reference.visible(view);
            visible
                .iter()
                .map(|id| reference.facts(id).change.clone())
                .collect()
        };
        let (ours, theirs) = (changes(self, &hive), changes(self, &jj));
        let known: HashSet<ChangeId> = ours.intersection(&theirs).cloned().collect();
        self.beyond(&hive, &jj, &known)
    }
}
