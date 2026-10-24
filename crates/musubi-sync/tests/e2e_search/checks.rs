//! The properties checked whenever the hive fully converges: at the end of every sequence,
//! and when the `converge` rule fires.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fmt::Write as _;

use crate::view::View;
use crate::world::World;

/// Whether `MUSUBI_SEARCH_MASK` (a comma-separated list) masks a known bug, so a search
/// can look past it until it is fixed.
pub fn masked(bug: &str) -> bool {
    std::env::var("MUSUBI_SEARCH_MASK").is_ok_and(|v| v.split(',').any(|b| b == bug))
}

impl World {
    /// Syncs to a fixed point, checks every property, then starts the ledger afresh.
    pub fn converge(&mut self) {
        self.record("converge".to_owned());
        self.sync_everything();
        // A machine with edits it hasn't snapshotted snapshots them with its next `jj`
        // command, rewriting its working copy, possibly at an older operation and so
        // concurrently with another machine's rewrite of it. Have it look, as rules do, so
        // the ledger records who rewrote it, then sync that.
        if self.snapshot_pending() {
            self.sync_everything();
        }
        if masked("export-after-merge") {
            // Masks found::bookmark_moved_by_a_node_merge_is_exported: a node's own merge
            // can leave its `.git` behind its bookmarks. Any `jj` command that writes an
            // operation exports everything (`jj git export` is a no-op when colocated).
            for m in 0..self.nodes() {
                self.jj(m, &["bookmark", "create", "mask-export", "-r", "@"]);
                self.jj(m, &["bookmark", "delete", "mask-export"]);
            }
            self.sync_everything();
        }
        // Visible commits with change ids and descriptions, local bookmarks (conflicted
        // ones identically), git branches, and a quiet `jj status`.
        let converged = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.fx.assert_converged();
        }));
        if let Err(panic) = converged {
            eprintln!("not converged; trace:\n{}", self.trace.join("\n"));
            std::panic::resume_unwind(panic);
        }
        // `assert_converged` synced too; any commit new to the ledger came from a merge.
        for m in 0..self.nodes() {
            self.record_merges(m);
        }
        let views: Vec<View> = (0..self.nodes()).map(|m| self.view_at_head(m)).collect();
        self.check_heads();
        self.check_operations();
        self.check_tags();
        self.check_workspaces(&views);
        self.check_divergence(&views[0]);
        self.check_conflicts(&views[0]);
        self.check_other_workspaces();
        let view = self.view_at_head(0);
        self.ledger.reset(&view);
    }

    /// Syncs every node, repeatedly, until a whole round changes nothing, as
    /// `Hive::sync_all` does, recording each node's merges.
    fn sync_everything(&mut self) {
        for _ in 0..20 {
            let mut steps = 0;
            for m in 0..self.nodes() {
                steps += self.sync_counted(m);
            }
            if steps == 0 {
                return;
            }
        }
        self.fail("the hive did not converge");
    }

    /// Every workspace of every machine, each after those whose working copies it is built
    /// on.
    fn workspaces_ancestors_first(&self) -> Vec<(usize, usize)> {
        let view = self.view_at_head(0);
        let mut pending: Vec<((usize, usize), String)> = vec![];
        for m in 0..self.nodes() {
            let wcs = self.working_copies(m);
            for (ws, workspace) in self.workspaces[m].iter().enumerate() {
                pending.push(((m, ws), wcs[&workspace.name].clone()));
            }
        }
        let mut order = vec![];
        while !pending.is_empty() {
            let ready = (0..pending.len())
                .find(|&i| {
                    let mut ancestors = view.ancestors(&pending[i].1);
                    ancestors.remove(&pending[i].1);
                    !pending.iter().any(|(_, wc)| ancestors.contains(wc))
                })
                .unwrap_or(0);
            order.push(pending.remove(ready).0);
        }
        order
    }

    /// Every node's canonical head is the hub's.
    fn check_heads(&mut self) {
        let hub = self.fx.hive.hub_head();
        for m in 0..self.nodes() {
            let heads = match self.fx.hive.members[m].adapter.repo_mut().canonical_heads() {
                Ok(heads) => heads,
                Err(err) => self.fail(&format!("{}'s heads: {err}", self.machine(m))),
            };
            if heads != vec![hub.clone()] {
                self.fail(&format!(
                    "{}'s canonical heads are not the hub's head",
                    self.machine(m)
                ));
            }
        }
    }

    /// Every operation made on any machine since setup is in every machine's op log.
    fn check_operations(&self) {
        let new_ops = |m: usize| -> BTreeSet<String> {
            self.op_keys(m)
                .difference(&self.baseline_keys[m])
                .cloned()
                .collect()
        };
        let first = new_ops(0);
        for m in 1..self.nodes() {
            let mine = new_ops(m);
            if mine != first {
                self.fail(&format!(
                    "operations differ: only on {}: {:?}; only on {}: {:?}",
                    self.machine(0),
                    first.difference(&mine).collect::<Vec<_>>(),
                    self.machine(m),
                    mine.difference(&first).collect::<Vec<_>>(),
                ));
            }
        }
    }

    /// Tags agree everywhere, conflicted ones identically. (Each machine's `@git` tags are
    /// its own, like its git branches.)
    fn check_tags(&self) {
        let template = r#"if(!remote, name ++ ":" ++ if(conflict, "conflict:", "") ++ added_targets.map(|c| c.commit_id()).join(",") ++ "\n")"#;
        let tags = |m: usize| self.raw_jj(m, &["tag", "list", "-T", template]);
        let first = tags(0);
        for m in 1..self.nodes() {
            let mine = tags(m);
            if mine != first {
                self.fail(&format!(
                    "tags differ between {} and {}:\n{first}\n---\n{mine}",
                    self.machine(0),
                    self.machine(m)
                ));
            }
        }
    }

    /// Each machine has its own workspaces, and their working copies are visible, but for a
    /// machine the hive has forgotten, whose working copy can stay on the hidden commit its
    /// forget abandoned until its next work. (It shows the other machines' too, as
    /// `machine/workspace`: `check_other_workspaces`.)
    fn check_workspaces(&self, views: &[View]) {
        let shown = self.fx.shown_machines();
        for (m, view) in views.iter().enumerate() {
            let listed: BTreeSet<String> = self
                .raw_jj(m, &["workspace", "list", "-T", "name ++ \"\\n\""])
                .lines()
                .filter(|name| !name.contains('/'))
                .map(str::to_owned)
                .collect();
            let expected: BTreeSet<String> = self.workspaces[m]
                .iter()
                .map(|ws| ws.name.clone())
                .collect();
            if listed != expected {
                self.fail(&format!(
                    "{} lists workspaces {listed:?}, expected {expected:?}",
                    self.machine(m)
                ));
            }
            if !shown.contains(&self.fx.machine_key(m)) {
                continue;
            }
            let visible: BTreeSet<String> = view.commits.iter().map(|c| c.id.clone()).collect();
            for (name, wc) in self.working_copies(m) {
                if !visible.contains(&wc) {
                    self.fail(&format!(
                        "{}'s workspace {name} is at {wc}, which is not visible",
                        self.machine(m)
                    ));
                }
            }
        }
    }

    /// A change diverges only if two machines, or a command at an older operation,
    /// rewrote it since the hive last converged.
    fn check_divergence(&self, view: &View) {
        let spurious = self.ledger.spurious_divergence(view, |a, b| {
            let diff = self.raw_jj(
                0,
                &[
                    "--ignore-working-copy",
                    "diff",
                    "--summary",
                    "--from",
                    a,
                    "--to",
                    b,
                ],
            );
            // A commit and its own rewrite can match too, when the rewrite changed nothing
            // (squashing an empty commit into it): the original stays visible under a
            // descendant jj leaves in place, as it leaves the children of a divergently
            // rewritten commit. That is no copy.
            let rewritten_from = |new: &str, old: &str| {
                self.raw_jj(
                    0,
                    &[
                        "--ignore-working-copy",
                        "evolog",
                        "--no-graph",
                        "-r",
                        new,
                        "-T",
                        "commit.commit_id() ++ \"\\n\"",
                    ],
                )
                .lines()
                .any(|id| id == old)
            };
            diff.is_empty() && !rewritten_from(a, b) && !rewritten_from(b, a)
        });
        if !spurious.is_empty() {
            let details: Vec<String> = spurious
                .iter()
                .map(|c| {
                    format!(
                        "{c} (rewritten by {:?}: {:?})",
                        self.ledger.rewriters(c.split(' ').next().unwrap_or(c)),
                        self.ledger.history(c.split(' ').next().unwrap_or(c))
                    )
                })
                .collect();
            let changes = view.changes();
            let mut history = String::new();
            for change in &spurious {
                let change = change.split(' ').next().unwrap_or(change);
                for commit in &changes[change] {
                    history.push_str(&self.raw_jj(0, &["evolog", "-r", commit]));
                    for m in 0..self.nodes() {
                        history.push_str(&self.visibility_history(m, commit));
                    }
                    history.push('\n');
                }
            }
            self.fail(&format!(
                "spurious divergence: {}\n{history}\n{}",
                details.join(", "),
                self.raw_jj(0, &["op", "log", "-n", "40", "--no-graph"])
            ));
        }
    }

    /// The operations of machine `m`, oldest first, at which `commit` became visible or
    /// hidden: for explaining a failure.
    fn visibility_history(&self, m: usize, commit: &str) -> String {
        let ops = self.raw_jj(
            m,
            &[
                "op",
                "log",
                "--no-graph",
                "-n",
                "120",
                "-T",
                r#"id ++ " " ++ user ++ " " ++ description.first_line() ++ "\n""#,
            ],
        );
        let revset = format!("{commit} & ::visible_heads()");
        let mut out = format!("visibility of {commit} on {}:\n", self.machine(m));
        let mut visible = None;
        for line in ops.lines().rev() {
            let id = line.split(' ').next().unwrap_or_default();
            let output = self.fx.repo(m).jj_output(&[
                "--at-op",
                id,
                "log",
                "--no-graph",
                "-r",
                &revset,
                "-T",
                "commit_id",
            ]);
            let now = output.status.success() && !output.stdout.is_empty();
            if visible != Some(now) {
                writeln!(
                    out,
                    "  {} at {}",
                    if now { "visible" } else { "hidden" },
                    &line[..line.len().min(160)]
                )
                .unwrap();
                visible = Some(now);
            }
        }
        out
    }

    /// A bookmark or tag is conflicted only if two machines, git, or a command at an older
    /// operation changed it since the hive last converged.
    fn check_conflicts(&self, view: &View) {
        let spurious = self.ledger.spurious_conflicts(view, |conflicted| {
            let (kind, name) = conflicted.split_once(' ').unwrap();
            // The parents of each commit the name moved away from, then the commits it
            // might point to now.
            let template = concat!(
                r#"if(!remote, removed_targets.map(|c| c.parents().map(|p| p.commit_id())"#,
                r#".join(",")).join(";") ++ "\t" ++ added_targets.map(|c| c.commit_id())"#,
                r#".join(",") ++ "\n")"#,
            );
            let listed = self.raw_jj(
                0,
                &["--ignore-working-copy", kind, "list", name, "-T", template],
            );
            listed.lines().any(|line| {
                let Some((removed, added)) = line.split_once('\t') else {
                    return false;
                };
                let added: BTreeSet<&str> = added.split(',').collect();
                removed
                    .split(';')
                    .any(|parents| parents.split(',').collect::<BTreeSet<_>>() == added)
            })
        });
        if !spurious.is_empty() {
            self.fail(&format!("spurious conflicts: {}", spurious.join(", ")));
        }
    }

    /// After every workspace of every machine makes an operation and the hive syncs, every
    /// machine shows each other machine's workspaces, as `machine/workspace`, at their
    /// working-copy commits, and its `.git` has no refs for them.
    ///
    /// The workspaces take turns, each syncing the whole hive, ancestors first:
    /// snapshotting a working copy rebases every working copy built on it, so taking turns
    /// this way, each workspace's last operation comes after every rewrite of its working
    /// copy.
    fn check_other_workspaces(&mut self) {
        for (m, ws) in self.workspaces_ancestors_first() {
            // Update a stale working copy first, so the edit is not snapshotted at an older
            // operation.
            self.jj_in(m, ws, &["status"]);
            let n = self.next();
            self.write(m, ws, &format!("wc-{}", self.machine(m)), &format!("{n}\n"));
            self.jj_in(m, ws, &["status"]);
            self.sync_everything();
        }
        let expected: Vec<BTreeMap<String, String>> =
            (0..self.nodes()).map(|m| self.working_copies(m)).collect();
        for o in 0..self.nodes() {
            // Every other machine's workspace, including any on a hidden commit.
            let template = r#"name ++ "\t" ++ target.commit_id() ++ "\n""#;
            let listed = self.raw_jj(o, &["workspace", "list", "-T", template]);
            let mut shown: BTreeMap<String, BTreeMap<String, String>> = BTreeMap::new();
            for line in listed.lines() {
                if let Some((name, commit)) = line.split_once('\t')
                    && let Some((machine, ws)) = name.split_once('/')
                {
                    shown
                        .entry(machine.to_owned())
                        .or_default()
                        .insert(ws.to_owned(), commit.to_owned());
                }
            }
            let mut got: Vec<&BTreeMap<String, String>> = shown.values().collect();
            let mut want: Vec<&BTreeMap<String, String>> = (0..self.nodes())
                .filter(|&m| m != o)
                .map(|m| &expected[m])
                .collect();
            got.sort();
            want.sort();
            if got != want {
                self.fail(&format!(
                    "{} shows the other machines' workspaces as {shown:?}, not at their working copies {want:?}\n{}",
                    self.machine(o),
                    self.raw_jj(o, &["op", "log", "-n", "12"]),
                ));
            }
            let refs =
                self.fx
                    .repo(o)
                    .git(&["for-each-ref", "--format=%(refname)", "refs/remotes"]);
            if let Some(stray) = refs
                .lines()
                .find(|r| !r.starts_with("refs/remotes/origin/"))
            {
                self.fail(&format!("{}'s git has {stray}", self.machine(o)));
            }
        }
    }
}
