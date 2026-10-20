//! What one machine sees at one operation, read with one `jj log`, and the candidate
//! helpers that rules share with their preconditions.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

pub const ROOT: &str = "0000000000000000000000000000000000000000";

pub const TEMPLATE: &str = concat!(
    r#"commit_id ++ "\t" ++ change_id ++ "\t" ++ parents.map(|c| c.commit_id()).join(",")"#,
    r#" ++ "\t" ++ if(immutable, "i", "m") ++ "\t" ++ if(conflict, "c", "-")"#,
    r#" ++ "\t" ++ local_bookmarks.map(|b| b.name() ++ if(b.conflict(), "?")).join(",")"#,
    r#" ++ "\t" ++ tags.map(|t| t.name() ++ if(t.conflict(), "?")).join(",")"#,
    r#" ++ "\t" ++ remote_bookmarks.map(|b| b.name() ++ "@" ++ b.remote()).join(",")"#,
    r#" ++ "\t" ++ working_copies.map(|w| w.name()).join(",")"#,
    r#" ++ "\t" ++ description.first_line()"#,
    r#" ++ "\n""#
);

pub struct Commit {
    pub id: String,
    pub change: String,
    pub parents: Vec<String>,
    pub mutable: bool,
    pub conflict: bool,
    pub bookmarks: Vec<String>,
    pub tags: Vec<String>,
    /// As listed, with `?` after conflicted names.
    raw_bookmarks: Vec<String>,
    raw_tags: Vec<String>,
    /// Remote bookmarks, `name@remote`.
    pub remote_bookmarks: Vec<String>,
    /// The workspaces whose working copy this is: this machine's own, and the other
    /// machines' as `machine/workspace`.
    pub working_copies: Vec<String>,
    /// The first line of the description.
    pub subject: String,
}

/// The visible commits, in `jj log` order (children before parents).
pub struct View {
    pub commits: Vec<Commit>,
}

fn split(field: &str) -> Vec<String> {
    field
        .split(',')
        .filter(|s| !s.is_empty())
        .map(str::to_owned)
        .collect()
}

fn unmarked(field: &str) -> Vec<String> {
    split(field)
        .into_iter()
        .map(|name| name.trim_end_matches('?').to_owned())
        .collect()
}

impl View {
    pub fn parse(out: &str) -> Self {
        let commits = out
            .lines()
            .map(|line| {
                let fields: Vec<&str> = line.splitn(10, '\t').collect();
                assert_eq!(fields.len(), 10, "unexpected log line {line:?}");
                Commit {
                    id: fields[0].to_owned(),
                    change: fields[1].to_owned(),
                    parents: split(fields[2]),
                    mutable: fields[3] == "m",
                    conflict: fields[4] == "c",
                    bookmarks: unmarked(fields[5]),
                    tags: unmarked(fields[6]),
                    raw_bookmarks: split(fields[5]),
                    raw_tags: split(fields[6]),
                    remote_bookmarks: split(fields[7]),
                    working_copies: split(fields[8]),
                    subject: fields[9].to_owned(),
                }
            })
            .collect();
        Self { commits }
    }

    /// Every visible commit but the root: targets for bookmarks, tags, git branches.
    pub fn targets(&self) -> Vec<String> {
        self.commits
            .iter()
            .filter(|c| c.id != ROOT)
            .map(|c| c.id.clone())
            .collect()
    }

    /// Commits that may be rewritten.
    pub fn mutable(&self) -> Vec<String> {
        self.commits
            .iter()
            .filter(|c| c.mutable)
            .map(|c| c.id.clone())
            .collect()
    }

    /// Mutable commits with conflicts, for `jj resolve`.
    pub fn conflicted(&self) -> Vec<String> {
        self.commits
            .iter()
            .filter(|c| c.mutable && c.conflict)
            .map(|c| c.id.clone())
            .collect()
    }

    /// Commits that `jj squash -r` can fold into their single, mutable parent.
    pub fn squashable(&self) -> Vec<String> {
        let mutable: BTreeSet<String> = self.mutable().into_iter().collect();
        self.commits
            .iter()
            .filter(|c| c.mutable && c.parents.len() == 1 && mutable.contains(&c.parents[0]))
            .map(|c| c.id.clone())
            .collect()
    }

    pub fn bookmarks(&self) -> Vec<String> {
        self.names(|c| &c.bookmarks).into_keys().collect()
    }

    /// Bookmarks that are not conflicted, which `jj git push` accepts.
    pub fn pushable_bookmarks(&self) -> Vec<String> {
        let conflicted = self.conflicted_names();
        self.bookmarks()
            .into_iter()
            .filter(|name| !conflicted.contains(&format!("bookmark {name}")))
            .collect()
    }

    /// Conflicted bookmarks and tags, as `bookmark <name>` and `tag <name>`. (A conflict
    /// between a move and a deletion has a single target.)
    pub fn conflicted_names(&self) -> BTreeSet<String> {
        let mut names = BTreeSet::new();
        for commit in &self.commits {
            for (kind, list) in [
                ("bookmark", &commit.raw_bookmarks),
                ("tag", &commit.raw_tags),
            ] {
                for name in list {
                    if let Some(name) = name.strip_suffix('?') {
                        names.insert(format!("{kind} {name}"));
                    }
                }
            }
        }
        names
    }

    /// Names with a remote bookmark on a real remote: `jj bookmark create` refuses them
    /// while they are tracked, even after the local bookmark is deleted.
    pub fn remote_names(&self) -> BTreeSet<String> {
        self.commits
            .iter()
            .flat_map(|c| &c.remote_bookmarks)
            .filter_map(|b| b.rsplit_once('@'))
            .filter(|(_, remote)| *remote != "git")
            .map(|(name, _)| name.to_owned())
            .collect()
    }

    pub fn tags(&self) -> Vec<String> {
        self.names(|c| &c.tags).into_keys().collect()
    }

    /// Each name with its visible targets.
    fn names(&self, field: impl Fn(&Commit) -> &Vec<String>) -> BTreeMap<String, BTreeSet<String>> {
        let mut names: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for commit in &self.commits {
            for name in field(commit) {
                names
                    .entry(name.clone())
                    .or_default()
                    .insert(commit.id.clone());
            }
        }
        names
    }

    pub fn bookmark_targets(&self) -> BTreeMap<String, BTreeSet<String>> {
        self.names(|c| &c.bookmarks)
    }

    pub fn tag_targets(&self) -> BTreeMap<String, BTreeSet<String>> {
        self.names(|c| &c.tags)
    }

    /// Other machines' workspaces, `machine/workspace`, with their working copies.
    pub fn other_workspaces(&self) -> BTreeMap<String, String> {
        let mut workspaces = BTreeMap::new();
        for commit in &self.commits {
            for name in &commit.working_copies {
                if name.contains('/') {
                    workspaces.insert(name.clone(), commit.id.clone());
                }
            }
        }
        workspaces
    }

    /// Other machines' working copies, if mutable.
    pub fn other_working_copies(&self) -> Vec<String> {
        let mutable: BTreeSet<String> = self.mutable().into_iter().collect();
        let ids: BTreeSet<String> = self
            .other_workspaces()
            .into_values()
            .filter(|id| mutable.contains(id))
            .collect();
        self.ordered(&ids)
    }

    /// Mutable proper ancestors of other machines' working copies: rewriting one rebases
    /// that machine's `@`.
    pub fn under_other_working_copies(&self) -> Vec<String> {
        let mutable: BTreeSet<String> = self.mutable().into_iter().collect();
        let mut found = BTreeSet::new();
        for wc in self.other_workspaces().into_values() {
            let mut ancestors = self.ancestors(&wc);
            ancestors.remove(&wc);
            found.extend(ancestors.into_iter().filter(|c| mutable.contains(c)));
        }
        self.ordered(&found)
    }

    /// `ids` in log order, so that draws do not depend on commit hashes.
    fn ordered(&self, ids: &BTreeSet<String>) -> Vec<String> {
        self.commits
            .iter()
            .filter(|c| ids.contains(&c.id))
            .map(|c| c.id.clone())
            .collect()
    }

    /// `id` and everything descending from it.
    pub fn descendants(&self, id: &str) -> BTreeSet<String> {
        let mut found = BTreeSet::from([id.to_owned()]);
        for commit in self.commits.iter().rev() {
            if commit.parents.iter().any(|p| found.contains(p)) {
                found.insert(commit.id.clone());
            }
        }
        found
    }

    /// `id` and everything it descends from.
    pub fn ancestors(&self, id: &str) -> BTreeSet<String> {
        let mut found = BTreeSet::from([id.to_owned()]);
        for commit in &self.commits {
            if found.contains(&commit.id) {
                found.extend(commit.parents.iter().cloned());
            }
        }
        found
    }

    /// Parents for new commits and rebase destinations: anything but the root. Commits
    /// directly on the root stay immutable (see `World::new`), and nothing new goes there.
    pub fn bases(&self) -> Vec<String> {
        self.targets()
    }

    /// Valid destinations for `jj rebase -s source`: not `source`'s descendants.
    pub fn rebase_source_destinations(&self, source: &str) -> Vec<String> {
        let excluded = self.descendants(source);
        self.bases()
            .into_iter()
            .filter(|c| !excluded.contains(c))
            .collect()
    }

    /// Valid destinations for `jj rebase -r revision`: anything but the revision itself.
    pub fn rebase_revision_destinations(&self, revision: &str) -> Vec<String> {
        self.bases().into_iter().filter(|c| c != revision).collect()
    }

    /// Second parents for `jj new first other`: commits unrelated to `first`.
    pub fn unrelated(&self, first: &str) -> Vec<String> {
        let related: BTreeSet<String> = self
            .ancestors(first)
            .union(&self.descendants(first))
            .cloned()
            .collect();
        self.bases()
            .into_iter()
            .filter(|c| !related.contains(c))
            .collect()
    }

    /// The change → commits map, for detecting which changes a command rewrote.
    pub fn changes(&self) -> BTreeMap<String, BTreeSet<String>> {
        let mut changes: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for commit in &self.commits {
            changes
                .entry(commit.change.clone())
                .or_default()
                .insert(commit.id.clone());
        }
        changes
    }

    /// Changes with more than one visible commit.
    pub fn divergent(&self) -> BTreeSet<String> {
        self.changes()
            .into_iter()
            .filter(|(_, commits)| commits.len() > 1)
            .map(|(change, _)| change)
            .collect()
    }
}
