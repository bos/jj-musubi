//! Copy membership: forgetting, expiry and replacement. Records the copy's independent
//! join inputs and name births before the fixture enrolls it, and tracks forgotten working
//! copies across syncs.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::repo::Repo as _;
use musubi_jj::node::NodeError;
use musubi_jj::op_id::LocalOp;

use crate::coverage::fired;

use crate::identity::{HistoryKey, SourceKey};

use super::MACHINES;
use super::MERGE_KEY_TEMPLATE;
use super::Naming;
use super::OP_KEY_TEMPLATE;
use super::Workspace;
use super::World;
use super::join_fingerprint;
use super::merge_key;
use super::native_head;

impl World {
    /// Machine `m` forgets machine `o`'s copy, as `musubi forget` does, which abandons its
    /// working-copy commits that are empty. Records what changed.
    pub fn forget_copy(&mut self, m: usize, o: usize) {
        let before = self.seen(m);
        let key = self.fx.machine_key(o);
        let name = self.machine(o);
        self.record(format!("{}: musubi forget {name}", self.machine(m)));
        match self.fx.node(m).forget_copy(&key, name) {
            Ok(true) => {
                let forget = self.newest_key(m);
                self.forgot.insert(key, forget);
            }
            Ok(false) => {}
            // As its hint says: restore the history it names, then forget again. jj's
            // reparenting can recreate an abandoned operation's exact id, so musubi can't tell
            // which of the hive's operations was dropped (races.md, "Known jj limitations").
            Err(NodeError::AmbiguousAbandon(target)) => {
                let err = NodeError::AmbiguousAbandon(target.clone()).to_string();
                self.integrate_named_history(m, &format!("musubi forget {name}"), &target, &err);
                return self.forget_copy(m, o);
            }
            Err(err) => self.fail(&format!(
                "musubi forget {name} failed on {}: {err}",
                self.machine(m)
            )),
        }
        let after = self.seen(m);
        let what = self.trace.last().cloned().unwrap_or_default();
        self.ledger.record(m, &what, &before, &after, false);
    }

    /// Machine `m` sets its copy's `musubi.forget-after` to `value`, as `musubi join` does,
    /// and records it in the hive, as its daemon does once idle. Records what changed.
    pub fn set_forget_after(&mut self, m: usize, value: &str) {
        let before = self.seen(m);
        self.record(format!(
            "{}: jj config set --repo musubi.forget-after {value}",
            self.machine(m)
        ));
        self.fx
            .repo(m)
            .jj(&["config", "set", "--repo", "musubi.forget-after", value]);
        if let Err(err) = self.fx.node(m).record_forget_after() {
            self.fail(&format!(
                "recording musubi.forget-after failed on {}: {err}",
                self.machine(m)
            ));
        }
        let after = self.seen(m);
        let what = self.trace.last().cloned().unwrap_or_default();
        self.ledger.record(m, &what, &before, &after, false);
    }

    /// Machine `m`'s daemon, two hours on by the environment's clock, forgets every other
    /// copy that has gone unused for longer than its `musubi.forget-after`. Records what
    /// changed.
    pub fn expire_idle(&mut self, m: usize) {
        let before = self.seen(m);
        self.record(format!(
            "{}: forget the copies unused two hours on",
            self.machine(m)
        ));
        let later = self.fx.env.clock().now() + std::time::Duration::from_secs(2 * 3600);
        let present = |world: &mut Self| -> BTreeSet<String> {
            match world.fx.node(m).activity() {
                Ok(active) => active.into_iter().map(|activity| activity.key).collect(),
                Err(err) => world.fail(&format!(
                    "listing copies' activity failed on {}: {err}",
                    world.machine(m)
                )),
            }
        };
        let active = present(self);
        if let Err(err) = self
            .fx
            .node(m)
            .expire_idle(later, std::time::Duration::ZERO)
        {
            self.fail(&format!(
                "forgetting unused copies failed on {}: {err}",
                self.machine(m)
            ));
        }
        let gone: Vec<String> = active.difference(&present(self)).cloned().collect();
        if !gone.is_empty() {
            let forget = self.newest_key(m);
            for key in gone {
                self.forgot.insert(key, forget.clone());
            }
        }
        let after = self.seen(m);
        let what = self.trace.last().cloned().unwrap_or_default();
        self.ledger.record(m, &what, &before, &after, false);
    }

    /// Machine `m`'s own working-copy commits, by workspace, each with its change id and
    /// whether it is visible, read in process, where the hive has forgotten the machine:
    /// `None` where it shows it.
    pub(super) fn forgotten_working_copies(
        &self,
        m: usize,
    ) -> Option<BTreeMap<String, (String, String, bool)>> {
        if self.fx.shown_machines().contains(&self.fx.machine_key(m)) {
            return None;
        }
        let repo = self.fx.load(m);
        let index = repo.index();
        let heads = repo.view().heads();
        let visible = |id: &CommitId| {
            futures::executor::block_on(index.has_id(id)).unwrap()
                && heads
                    .iter()
                    .any(|head| futures::executor::block_on(index.is_ancestor(id, head)).unwrap())
        };
        Some(
            repo.view()
                .wc_commit_ids()
                .iter()
                // The search names workspaces without a `/`: those with one are others'.
                .filter(|(name, _)| !name.as_str().contains('/'))
                .map(|(name, id)| {
                    let commit =
                        futures::executor::block_on(repo.store().get_commit_async(id)).unwrap();
                    let change = commit.change_id().hex();
                    (name.as_str().to_owned(), (id.hex(), change, visible(id)))
                })
                .collect(),
        )
    }

    /// Notes, for coverage, a sync of machine `m`, forgotten before it and after, that moved
    /// a working copy of its own from one hidden commit to another of the same change: as a
    /// forgotten copy rebases one whose parents other machines rewrote or abandoned
    /// (`replace_abandoned_working_copies`).
    pub(super) fn note_forgotten_rebase(
        &self,
        m: usize,
        before: Option<BTreeMap<String, (String, String, bool)>>,
    ) {
        let (Some(before), Some(after)) = (before, self.forgotten_working_copies(m)) else {
            return;
        };
        let rebased = after.iter().any(|(name, (commit, change, visible))| {
            !visible
                && before
                    .get(name)
                    .is_some_and(|(old, old_change, was_visible)| {
                        !was_visible && old != commit && old_change == change
                    })
        });
        if rebased {
            fired("forgotten:working_copy_rebased");
        }
    }

    /// The `merge_key` of machine `m`'s newest operation.
    fn newest_key(&self, m: usize) -> SourceKey {
        let args = [
            "--ignore-working-copy",
            "op",
            "log",
            "--no-graph",
            "-n",
            "1",
        ];
        let args: Vec<&str> = args.into_iter().chain(["-T", MERGE_KEY_TEMPLATE]).collect();
        SourceKey::from_template(&self.raw_jj(m, &args))
    }

    /// Drops from `forgot` each copy the hub's head shows again although its history has the
    /// forget: the copy worked since.
    pub(super) fn note_shown_again(&mut self) {
        if self.forgot.is_empty() {
            return;
        }
        let shown = self.fx.shown_machines();
        if !self.forgot.keys().any(|key| shown.contains(key)) {
            return;
        }
        let history = self.hub_merge_keys();
        self.forgot
            .retain(|key, forget| !(shown.contains(key) && history.contains(forget)));
    }

    /// A new copy of the hive on machine `m`, as `musubi clone` makes: an empty colocated
    /// repository at a path of its own, with the machine's jj config, joined to the hive on
    /// the root and synced, then on its local `trunk()`. A new machine's, if `m` is `nodes()`, or
    /// else in place of machine `m`'s copy, which has left the hive.
    pub fn clone_copy(&mut self, m: usize) {
        crate::coverage::interrupt_races();
        let n = self.next();
        let repo = if m == self.nodes() {
            let machine = MACHINES[m];
            let hostname = match self.naming {
                Naming::SharedHostname => "mac",
                Naming::Own | Naming::Default => machine,
            };
            self.fx.env.init_repo_with_hostname(machine, hostname)
        } else {
            let path = self
                .fx
                .env
                .root()
                .join(format!("{}-copy{n}", self.machine(m)));
            let repo = self.fx.repo(m).another_copy(&path);
            fs::create_dir_all(&path).unwrap();
            repo.jj(&["git", "init", "--colocate"]);
            repo
        };
        // Remotes stay local. Model the user configuring this new copy for Git access,
        // so fetch/push rules continue to cover newly joined and replacement copies.
        repo.jj(&[
            "git",
            "remote",
            "add",
            "origin",
            self.origin.bare.to_str().unwrap(),
        ]);
        if self.fx.hive.hub.store().pruned() > 0 {
            fired("join:after_prune");
        }
        self.record(format!(
            "{}: musubi clone into {}",
            self.machine(m),
            repo.path().display()
        ));
        let own: BTreeSet<HistoryKey> = repo
            .jj(&["op", "log", "--no-graph", "-T", OP_KEY_TEMPLATE])
            .lines()
            .map(HistoryKey::from_template)
            .collect();
        let join_input = native_head(&repo);
        let join_point = join_input.clone();
        self.fx.add(repo);
        let node = self.fx.hive.members.last().unwrap().adapter.repo();
        let joined = node.canonical_of(&LocalOp(join_point.clone())).unwrap();
        let join_key = merge_key(&node.canonical_store().read_operation(&joined).unwrap());
        let store = node.loader().op_store();
        let joined_from = futures::executor::block_on(store.read_operation(&join_point)).unwrap();
        let join_bindings = futures::executor::block_on(store.read_view(&joined_from.view_id))
            .unwrap()
            .wc_commit_ids
            .into_iter()
            .map(|(name, target)| {
                (
                    format!("{}/{}", node.machine().key(), name.as_str()),
                    target,
                )
            })
            .collect();
        let join_point = join_fingerprint(&joined_from);
        let primary = vec![Workspace {
            name: "default".to_owned(),
            path: None,
        }];
        if m < self.dirty.len() {
            self.fx.repos.swap_remove(m);
            self.fx.hive.members.swap_remove(m);
            self.dirty[m] = false;
            self.workspaces[m] = primary;
            self.seen[m] = None;
            // Its abandons that never reached the hive, whose operations the hub or another
            // machine still has, are gone with it; the rest stay checked.
            let exact = !self.abandoned.is_empty();
            let mut others: Vec<_> = (0..self.nodes())
                .filter(|&o| o != m)
                .map(|o| self.operation_history(o, exact))
                .collect();
            others.push(self.hub_operation_history());
            self.abandoned.retain(|op| {
                op.by != m || !others.iter().any(|history| history.proves_present(op))
            });
        } else {
            self.dirty.push(false);
            self.workspaces.push(primary);
            self.seen.push(None);
            self.evidence.baseline_ids.push(BTreeSet::new());
            self.evidence.baseline_keys.push(BTreeSet::new());
            self.evidence.join_points.push(join_point.clone());
            self.evidence.join_inputs.push(join_input.clone());
        }
        self.evidence.join_points[m] = join_point;
        self.evidence.join_inputs[m] = join_input;
        self.logical_extras.resize_with(self.nodes(), BTreeSet::new);
        self.logical_extras[m].clear();
        for ws in &self.workspaces[m] {
            let key = format!("{}/{}", self.fx.machine_key(m), ws.name);
            self.evidence.workspace_births.insert(key.clone());
            self.evidence.initial_workspace_keys.insert(key);
        }
        self.evidence
            .workspace_joins
            .insert(join_key, join_bindings);
        self.evidence.baseline_merge_keys.extend(self.merge_keys(m));
        self.evidence
            .operation_sources
            .retain(|(copy, _), _| *copy != m);
        self.evidence.workspace_trim_inputs.remove(&m);
        self.evidence
            .operation_seen
            .resize_with(self.nodes(), BTreeSet::new);
        self.evidence.operation_seen[m].clear();
        self.sync_counted(m);
        // The hive's history from before it was set up, and its own from before it joined,
        // are its baseline, as each machine's are. It may have only some of the hive's yet,
        // as from a hive made again, which the machines that have it fill again later.
        let keys: BTreeSet<HistoryKey> = own.union(&self.evidence.hive_baseline).cloned().collect();
        self.evidence.baseline_ids[m] = self
            .op_ids_and_keys(m, None)
            .into_iter()
            .filter(|(_, key)| keys.contains(key))
            .map(|(id, _)| id)
            .collect();
        self.evidence.baseline_keys[m] = keys;
        self.restart_imports(m);
        // As `musubi clone` checks out the destination's local `trunk()`.
        let trunk = self.raw_jj(
            m,
            &[
                "log",
                "--ignore-working-copy",
                "--no-graph",
                "-n1",
                "-r",
                "trunk() ~ root()",
                "-T",
                "commit_id",
            ],
        );
        if !trunk.is_empty() {
            self.jj(m, &["new", &trunk]);
        }
    }
}
