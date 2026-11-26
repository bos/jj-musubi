//! Copy membership: forgetting, expiry and replacement. Records the copy's independent
//! join inputs and name births before the fixture enrolls it.

use std::collections::BTreeSet;
use std::fs;

use crate::coverage::fired;

use crate::identity::HistoryKey;

use super::MACHINES;
use super::Naming;
use super::OP_KEY_TEMPLATE;
use super::Workspace;
use super::World;
use super::join_fingerprint;
use super::native_head;

impl World {
    /// Machine `m` forgets machine `o`'s copy, as `musubi forget` does, which abandons its
    /// working-copy commits that are empty. Records what changed.
    pub fn forget_copy(&mut self, m: usize, o: usize) {
        let before = self.seen(m);
        let key = self.fx.machine_key(o);
        let name = self.machine(o);
        self.record(format!("{}: musubi forget {name}", self.machine(m)));
        if let Err(err) = self.fx.node(m).forget_copy(&key, name) {
            self.fail(&format!(
                "musubi forget {name} failed on {}: {err}",
                self.machine(m)
            ));
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

    /// Machine `m` sets `musubi.machine-name` to `name`, as `jj config set --user` does,
    /// and records it in the hive, as its daemon does once idle. Records what changed.
    pub fn rename(&mut self, m: usize, name: &str) {
        let before = self.seen(m);
        self.record(format!(
            "{}: jj config set --user musubi.machine-name {name}",
            self.machine(m)
        ));
        let node = self.fx.node(m);
        let mut config = node.loader().settings().config().clone();
        let text = format!("musubi.machine-name = {name:?}");
        config.add_layer(
            jj_lib::config::ConfigLayer::parse(jj_lib::config::ConfigSource::User, &text).unwrap(),
        );
        let settings = node.loader().settings().with_new_config(config).unwrap();
        node.set_settings(settings);
        if let Err(err) = self.fx.node(m).record_name() {
            self.fail(&format!(
                "recording musubi.machine-name failed on {}: {err}",
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
        let after = self.seen(m);
        let what = self.trace.last().cloned().unwrap_or_default();
        self.ledger.record(m, &what, &before, &after, false);
    }

    /// A new copy of the hive on machine `m`, as `musubi clone` makes: an empty colocated
    /// repository at a path of its own, with the machine's jj config, joined to the hive on
    /// the root and synced, then on its local `trunk()`. A new machine's, if `m` is `nodes()`, or
    /// else in place of machine `m`'s copy, which has left the hive.
    pub fn clone_copy(&mut self, m: usize) {
        self.new_copy(m, false, None);
    }

    /// An independently fetched Git copy joins with its recorded upstream state, which
    /// can differ from the hive's. Subsequent commands and syncs keep checking both views.
    pub fn join_existing_copy(&mut self, m: usize) {
        self.new_copy(m, true, None);
    }

    fn new_copy(&mut self, m: usize, existing: bool, like: Option<usize>) {
        let n = self.next();
        let repo = if m == self.nodes() {
            let machine = MACHINES[m];
            let hostname = match self.naming {
                Naming::SharedHostname => "mac",
                Naming::Own | Naming::Default => like.map_or(machine, |x| MACHINES[x]),
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
        if existing {
            repo.jj(&["git", "fetch", "--remote", "origin"]);
            let main = repo.jj(&[
                "log",
                "--no-graph",
                "-r",
                "present(main@origin)",
                "-T",
                "commit_id",
            ]);
            if !main.is_empty() {
                repo.jj(&["bookmark", "track", "main", "--remote", "origin"]);
                fired("join:with_history");
            }
        }
        let command = if existing { "join" } else { "clone" };
        self.record(format!(
            "{}: musubi {command} at {}",
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
        let store = node.loader().op_store();
        let joined_from = futures::executor::block_on(store.read_operation(&join_point)).unwrap();
        let join_point = join_fingerprint(&joined_from);
        let primary = vec![Workspace {
            name: "default".to_owned(),
            path: None,
            edited: false,
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
            self.evidence.workspace_births.insert(key);
        }
        self.evidence.baseline_merge_keys.extend(self.merge_keys(m));
        self.evidence
            .operation_sources
            .retain(|(copy, _), _| *copy != m);
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
        if existing {
            // The command's best-effort repair is an ordinary native fetch, not a change
            // to canonical merging. The independent import and replay checks still apply.
            let remotes = self.fx.node(m).conflicted_git_bookmarks().unwrap();
            if remotes.contains_key("origin") {
                fired("join:fetch_conflict");
                self.jj(m, &["git", "fetch", "--remote", "origin"]);
                self.sync_counted(m);
            }
            return;
        }
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
