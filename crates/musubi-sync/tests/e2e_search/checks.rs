//! The properties checked whenever the hive fully converges: at the end of every sequence,
//! and when the `converge` rule fires.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::fs;

use futures::executor::block_on;
use musubi_jj::node::NodeRepo;
use musubi_sync::OpId;

use crate::reference::Reference;
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
        for m in 0..self.nodes() {
            self.check_imports(m);
        }
        let views: Vec<View> = (0..self.nodes()).map(|m| self.view_at_head(m)).collect();
        self.check_heads();
        self.check_translation();
        self.check_operations();
        self.check_tags();
        self.check_workspaces(&views);
        let mut reference = Reference::build(self);
        self.check_history(&mut reference);
        let beyond = reference.beyond_jj();
        self.check_divergence(&views[0], &mut reference, &beyond);
        self.check_conflicts(&reference, &beyond);
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

    /// What the protocol's model assumes of translation (protocol.md, "Translation layer"), on
    /// every machine: distinct local operations reachable from its op heads have distinct
    /// canonical forms, and each one's parents canonicalize to its canonical form's parents,
    /// leaving out those from before the join, which have none, as a join point's do; and every
    /// operation of the hive's history has a realization here that canonicalizes back to it, so
    /// realizing made no canonical operation of its own. Runs after `check_heads`, so every op
    /// head here is canonicalized already.
    ///
    /// A translation remembered wrongly would pass all that, so the check translates again from
    /// nothing, as a machine that lost its translation cache does, in a copy of the repository,
    /// and requires the same answers.
    fn check_translation(&self) {
        let hub = self.fx.hive.hub_head();
        for m in 0..self.nodes() {
            let node = self.fx.hive.members[m].adapter.repo();
            let repo = self.fx.repo(m);
            let dir = musubi_testutil::tempdir();
            let copy = dir.path().join("copy");
            musubi_testutil::copy_tree(repo.path(), &copy);
            fs::remove_file(copy.join(".jj/repo/musubi/translation")).ok();
            let failure = NodeRepo::open(&copy.join(".jj/repo"), &repo.settings())
                .map_err(|err| format!("reopening a copy: {err}"))
                .and_then(|mut fresh| translation_failure(node, &mut fresh, &hub))
                .err();
            if let Some(failure) = failure {
                self.fail(&format!("{}'s translation: {failure}", self.machine(m)));
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

    /// A change diverges only as jj diverges it given the same operations in one repository
    /// (`Reference::beyond_jj`), and never by the same rebase done twice, which the
    /// hub's sequencing exists to prevent: the ledger finds two alike commits of a change
    /// that no two commands explain, and the reference confirms that two merges rewrote one
    /// commit alike (`Reference::same_rebase_twice`).
    fn check_divergence(&self, view: &View, reference: &mut Reference, beyond: &[String]) {
        let alike = self.ledger.alike_commits(view, |a, b| {
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
        let mut spurious: Vec<String> = beyond
            .iter()
            .filter_map(|made| made.strip_suffix(" diverges"))
            .map(|change| format!("{change} (more than jj makes)"))
            .collect();
        for change in &alike {
            if reference.same_rebase_twice(change) {
                spurious.push(format!("{change} (the same rebase twice)"));
            }
        }
        if !spurious.is_empty() {
            let details: Vec<String> = spurious
                .iter()
                .map(|c| {
                    let change = c.split(' ').next().unwrap_or(c);
                    format!(
                        "{c} (rewritten by {:?}: {:?})",
                        self.ledger.rewriters(change),
                        self.ledger.history(change)
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
                "spurious divergence: {}\n{history}\nwhere jj's merges differ from the hive's:\n{}\n{}",
                details.join(", "),
                reference.deviations.join("\n"),
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

    /// A bookmark or tag is conflicted only as jj conflicts it given the same operations in
    /// one repository (`Reference::beyond_jj`).
    fn check_conflicts(&self, reference: &Reference, beyond: &[String]) {
        let spurious: Vec<&str> = beyond
            .iter()
            .filter_map(|made| made.strip_suffix(" conflicts"))
            .collect();
        if !spurious.is_empty() {
            self.fail(&format!(
                "spurious conflicts: {}\nwhere jj's merges differ from the hive's:\n{}",
                spurious.join(", "),
                reference.deviations.join("\n")
            ));
        }
    }

    /// The hive's history is one repository's: every machine realized each operation as
    /// the hive has it; its own operations are as the hive has them but for what musubi
    /// keeps visible for other machines, which makes nothing diverge or conflict; no
    /// operation but a merge made anything diverge or conflict that what it did doesn't
    /// explain; and no merge made more of either than jj's merge of the same parents. With
    /// these, divergence and conflicts at the head can be judged against the reference.
    fn check_history(&self, reference: &mut Reference) {
        let realizations = reference.check_realizations(self);
        if !realizations.is_empty() {
            self.fail(&format!(
                "realizations differ from the hive's operations: {}",
                realizations.join(", ")
            ));
        }
        if !reference.unexplained.is_empty() {
            self.fail(&format!(
                "operations made changes diverge or names conflict, unlike jj: {}\nwhere jj's merges differ from the hive's:\n{}",
                reference.unexplained.join("\n"),
                reference.deviations.join("\n")
            ));
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

/// What [`World::check_translation`] finds wrong with `node`'s translation, where `fresh`
/// is the same repository with no translation cache and `hub` the hive's head.
fn translation_failure(node: &NodeRepo, fresh: &mut NodeRepo, hub: &OpId) -> Result<(), String> {
    let err = |err: &dyn std::fmt::Display| err.to_string();
    let before: BTreeSet<OpId> = fresh
        .canonical_store()
        .operation_ids()
        .map_err(|e| err(&e))?
        .into_iter()
        .collect();
    let heads = fresh.canonical_heads().map_err(|e| err(&e))?;
    if heads != [hub.clone()] {
        return Err(format!("translated afresh, its op heads are {heads:?}"));
    }
    // The local operations reachable from the op heads, down to the join points.
    let op_store = fresh.loader().op_store().clone();
    let mut stack = fresh.local_heads().map_err(|e| err(&e))?;
    let mut seen: BTreeSet<OpId> = BTreeSet::new();
    let mut canonical_forms: BTreeMap<OpId, OpId> = BTreeMap::new();
    while let Some(local) = stack.pop() {
        if !seen.insert(local.clone()) || local == *op_store.root_operation_id() {
            continue;
        }
        let Some(canonical) = fresh.canonical_of(&local) else {
            return Err(format!("{local} is reachable but has no canonical form"));
        };
        if node
            .canonical_of(&local)
            .is_some_and(|known| known != canonical)
        {
            return Err(format!(
                "{local} is remembered as {}, but translates to {canonical}",
                node.canonical_of(&local).unwrap()
            ));
        }
        if let Some(other) = canonical_forms.insert(canonical.clone(), local.clone()) {
            return Err(format!(
                "{other} and {local} both have the canonical form {canonical}"
            ));
        }
        let parents = block_on(op_store.read_operation(&local))
            .map_err(|e| err(&e))?
            .parents;
        let expected = fresh
            .canonical_store()
            .parents(&canonical)
            .map_err(|e| err(&e))?;
        // A join point: its join operation's only parent is the root, and what came before it
        // here is not the hive's, though a command at an operation from then can give it
        // canonical forms.
        if expected == [fresh.canonical_store().root_operation_id().clone()]
            && parents != [op_store.root_operation_id().clone()]
        {
            continue;
        }
        // A parent with no canonical form is from before the join, which a merge leaves out.
        let hive_parents: Vec<OpId> = parents
            .iter()
            .filter_map(|parent| fresh.canonical_of(parent))
            .collect();
        if hive_parents != expected {
            return Err(format!(
                "{local}'s parents translate to {hive_parents:?}, but {canonical}'s are {expected:?}"
            ));
        }
        stack.extend(
            parents
                .into_iter()
                .filter(|parent| fresh.canonical_of(parent).is_some()),
        );
    }
    let history = fresh
        .canonical_store()
        .ancestors_until(std::slice::from_ref(hub), |_| false)
        .map_err(|e| err(&e))?;
    for canonical in &history {
        if !canonical_forms.contains_key(canonical) {
            return Err(format!(
                "{canonical} of the hive's history has no realization here"
            ));
        }
    }
    let after: BTreeSet<OpId> = fresh
        .canonical_store()
        .operation_ids()
        .map_err(|e| err(&e))?
        .into_iter()
        .collect();
    if let Some(new) = after.difference(&before).next() {
        return Err(format!(
            "translating afresh made the canonical operation {new}"
        ));
    }
    Ok(())
}
