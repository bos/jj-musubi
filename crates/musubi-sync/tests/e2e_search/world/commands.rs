//! User actions: jj and git commands, edits and workspace changes. An observation through
//! a jj command is an action too: it can snapshot, import and merge. Each action records
//! its native evidence before subsequent syncs can rewrite it.

use std::collections::BTreeSet;
use std::fs;
use std::process::Output;

use jj_lib::backend::CommitId;
use jj_lib::op_store::RefTarget;
use musubi_jj::node::ACCEPTED_PUSH;
use musubi_jj::op_id::CanonicalOp;
use musubi_jj::op_id::LocalOp;
use musubi_sync::OpId;

use crate::identity::SourceKey;
use crate::ledger::Seen;
use crate::view::Commit;
use crate::view::TEMPLATE;
use crate::view::View;

use super::FILES;
use super::OperationHistory;
use super::PastOp;
use super::Workspace;
use super::World;
use super::operation_header;

/// The three native command boundaries. Preparation and completion differ: an
/// observation can snapshot too; a historical command creates another operation head.
enum Command<'a> {
    Observe,
    InWorkspace {
        ws: usize,
        args: &'a [&'a str],
        refusals: &'a [&'a str],
    },
    AtOperation {
        op: &'a str,
        args: &'a [&'a str],
    },
}

enum CommandResult {
    Observed(View),
    Ran(String),
    AtOperation,
}

/// Captured inputs and the variant-specific completion of one native execution.
struct CommandExecution<'a> {
    history_before: BTreeSet<SourceKey>,
    before: Seen,
    present: Option<OperationHistory>,
    completion: Completion<'a>,
}

enum Completion<'a> {
    Observed(View),
    InWorkspace {
        output: Output,
        invocation: String,
        place: String,
        stale: bool,
        refusals: &'a [&'a str],
    },
    AtOperation {
        output: Output,
        invocation: String,
        heads_before: Vec<String>,
    },
}

impl World {
    /// Operations made since setup that machine `m` can run a command at, other than its
    /// current head. (`jj op log` merges concurrent operations first, like any command.)
    pub fn older_ops(&mut self, m: usize) -> Vec<PastOp> {
        // Through a recorded command: it merges concurrent operations first.
        self.jj(m, &["op", "log", "--no-graph", "-n", "8", "-T", "id"]);
        let descriptions = self.op_descriptions(m, 8);
        self.op_ids_and_keys(m, Some(8))
            .into_iter()
            .enumerate()
            .skip(1)
            .filter(|(_, (id, key))| {
                !self.evidence.baseline_ids[m].contains(id)
                    && !self.evidence.baseline_keys[m].contains(key)
            })
            .map(|(back, (id, _))| PastOp {
                description: descriptions[&id].clone(),
                id,
                back,
            })
            .collect()
    }

    /// Those of `older_ops` that `jj op abandon` can abandon: not merges, which it refuses,
    /// and none the hive has, whose abandon stops the copy syncing for good.
    pub fn abandonable_ops(&mut self, m: usize) -> Vec<PastOp> {
        let older = self.older_ops(m);
        let merges: BTreeSet<String> = self
            .raw_jj(
                m,
                &[
                    "--ignore-working-copy",
                    "op",
                    "log",
                    "--no-graph",
                    "-n",
                    "8",
                    "-T",
                    r#"if(parents.len() > 1, id ++ "\n")"#,
                ],
            )
            .lines()
            .map(str::to_owned)
            .collect();
        older
            .into_iter()
            .filter(|op| {
                !merges.contains(&op.id)
                    && !self.hive_has(m, &op.id)
                    && !self.abandon_rewrites_the_hives(m, &op.id)
            })
            .collect()
    }

    /// Whether `jj op abandon` of `op` rewrites an operation the hive has. It rewrites every
    /// operation reachable from the op heads that isn't below the abandoned one's parents, so
    /// the operations of the hive on another branch of the history, as one `--at-op` command or
    /// a second workspace leaves, are put on other parents. musubi can't tell its own such
    /// operation from one that is new, so a copy where that happens stops syncing as it does
    /// for one that abandoned operations the hive has. A realization the abandon only puts on
    /// more history is put back instead (`op_abandon_of_pre_join_history_is_harmless`), but
    /// the import check doesn't follow that move, so the search takes neither.
    fn abandon_rewrites_the_hives(&mut self, m: usize, op: &str) -> bool {
        use jj_lib::object_id::ObjectId as _;
        let store = self.fx.hive.members[m]
            .adapter
            .repo()
            .loader()
            .op_store()
            .clone();
        let ancestors = |starts: Vec<OpId>| {
            let mut seen = BTreeSet::new();
            let mut stack = starts;
            while let Some(id) = stack.pop() {
                if id == *store.root_operation_id() || !seen.insert(id.clone()) {
                    continue;
                }
                let body = futures::executor::block_on(store.read_operation(&id)).unwrap();
                stack.extend(body.parents);
            }
            seen
        };
        let id = OpId::try_from_hex(op).unwrap();
        let heads: Vec<OpId> = self
            .op_heads(m)
            .iter()
            .map(|head| OpId::try_from_hex(head).unwrap())
            .collect();
        let parents = futures::executor::block_on(store.read_operation(&id))
            .unwrap()
            .parents;
        let below = ancestors(parents);
        let rewritten: Vec<OpId> = ancestors(heads)
            .into_iter()
            .filter(|other| *other != id && !below.contains(other))
            .collect();
        rewritten.iter().any(|other| self.hive_has(m, &other.hex()))
    }

    /// Whether the hive has machine `m`'s operation `op`, as published, or as below an
    /// operation the hub accepted from `m`, which it may have lost since.
    fn hive_has(&mut self, m: usize, op: &str) -> bool {
        self.observe_published_operations();
        let repo = self.fx.hive.members[m].adapter.repo();
        let id = OpId::try_from_hex(op).unwrap();
        let body =
            futures::executor::block_on(repo.loader().op_store().read_operation(&id)).unwrap();
        if self
            .evidence
            .published_headers
            .contains(&operation_header(&body))
        {
            return true;
        }
        let Some(canonical) = repo.canonical_of(&LocalOp(id)) else {
            return false;
        };
        let store = repo.canonical_store();
        let musubi = self.fx.repo(m).repo_path().join("musubi");
        ["accepted_base", ACCEPTED_PUSH]
            .into_iter()
            .filter_map(|name| fs::read_to_string(musubi.join(name)).ok())
            .filter_map(|hex| OpId::try_from_hex(hex.trim()))
            .map(CanonicalOp)
            .any(|accepted| {
                store.has_operation(&accepted)
                    && store.is_ancestor_of(&canonical, &accepted).unwrap()
            })
    }

    /// What machine `m` sees, through a `jj` command: like the command the rule is about to
    /// run, it snapshots, imports, and merges first, so the commits it lists are exactly
    /// those the next command can see. Recorded, since it may change things.
    pub fn observe(&mut self, m: usize) -> View {
        let Ok(CommandResult::Observed(view)) = self.recorded_command(m, Command::Observe) else {
            unreachable!("an observation returns its view");
        };
        view
    }

    /// Has each machine with edits no `jj` command has snapshotted look, snapshotting them.
    /// Returns whether any did.
    pub fn snapshot_pending(&mut self) -> bool {
        let pending: Vec<usize> = (0..self.nodes()).filter(|&m| self.dirty[m]).collect();
        for &m in &pending {
            self.observe(m);
        }
        !pending.is_empty()
    }

    /// Runs a `jj` command as a user would, in workspace `ws` of machine `m`; it must
    /// succeed. Records which changes, bookmarks, and tags it changed.
    pub fn jj_in(&mut self, m: usize, ws: usize, args: &[&str]) -> String {
        match self.try_jj_in(m, ws, args, &[]) {
            Ok(out) => out,
            Err(stderr) => self.fail(&stderr),
        }
    }

    pub fn jj(&mut self, m: usize, args: &[&str]) -> String {
        self.jj_in(m, 0, args)
    }

    /// Like `jj_in`, but a failure whose message contains one of `refusals` (a refusal jj
    /// makes before changing anything) is returned rather than failing the test.
    pub fn try_jj_in(
        &mut self,
        m: usize,
        ws: usize,
        args: &[&str],
        refusals: &[&str],
    ) -> Result<String, String> {
        let CommandResult::Ran(output) =
            self.recorded_command(m, Command::InWorkspace { ws, args, refusals })?
        else {
            unreachable!("a workspace command returns its stdout");
        };
        Ok(output)
    }

    /// Runs a command at an older operation `op` of machine `m`, creating a concurrent
    /// operation, and records what it changed relative to `op`.
    pub fn jj_at_op(&mut self, m: usize, op: &str, args: &[&str]) {
        let Ok(CommandResult::AtOperation) =
            self.recorded_command(m, Command::AtOperation { op, args })
        else {
            unreachable!("a historical command records its new operation heads");
        };
    }

    /// Runs `jj undo` on machine `m`. jj refuses to undo another workspace's operation unless
    /// told to, so when it refuses one, which `checks` confirm is not this workspace's own, the
    /// user says so.
    pub fn undo(&mut self, m: usize) {
        let latest = self.head_op_workspace(m);
        let refusal = "Refusing to undo operation";
        match self.try_jj_in(m, 0, &["undo"], &[refusal]) {
            Ok(_) => self.check_undid_own_operation(m),
            Err(_) => {
                self.check_refused_foreign_operation(m, &latest);
                self.jj(m, &["undo", "--allow-cross-workspace"]);
            }
        }
    }

    /// Runs one complete actor action: capture inputs, execute, record native sources,
    /// then finish ledger and return bookkeeping. Keep each variant's chronology explicit.
    fn recorded_command(
        &mut self,
        m: usize,
        command: Command<'_>,
    ) -> Result<CommandResult, String> {
        let CommandExecution {
            history_before,
            before,
            present,
            completion,
        } = match command {
            Command::Observe => {
                let history_before = self.command_history(m);
                let before = self.seen(m);
                let exposed = self.exposed_to_duplicate_commit_bug(m, 0);
                self.dirty[m] = false;
                let present = self.abandoned_present(m);
                // A failed native observation or parse fails before source recording.
                let args = ["log", "--no-graph", "-r", "all()", "-T", TEMPLATE];
                let what = format!("{}: (looking)", self.machine(m));
                let output = self.jj_past_known_bug(m, &args, &what, exposed);
                if !output.status.success() {
                    self.fail(&format!(
                        "`jj {}` failed on {}:\n{}",
                        args.join(" "),
                        self.machine(m),
                        String::from_utf8_lossy(&output.stderr)
                    ));
                }
                let view = View::parse(&String::from_utf8(output.stdout).unwrap());
                CommandExecution {
                    history_before,
                    before,
                    present,
                    completion: Completion::Observed(view),
                }
            }
            Command::InWorkspace { ws, args, refusals } => {
                let history_before = self.command_history(m);
                let before = self.seen(m);
                let present = self.abandoned_present(m);
                let stale = self.is_stale(m, ws);
                let exposed = self.exposed_to_duplicate_commit_bug(m, ws);
                let path = self.workspaces[m][ws]
                    .path
                    .as_ref()
                    .map(|p| p.to_string_lossy().into_owned());
                let mut full: Vec<&str> = vec![];
                match &path {
                    Some(path) => full.extend(["-R", path.as_str()]),
                    None => self.dirty[m] = false,
                }
                full.extend_from_slice(args);
                let place = match &path {
                    Some(_) => format!("{} ({})", self.machine(m), self.workspaces[m][ws].name),
                    None => self.machine(m).to_owned(),
                };
                let what = format!("{place}: jj {}", args.join(" "));
                self.record(what.clone());
                let output = self.jj_past_known_bug(m, &full, &what, exposed);
                CommandExecution {
                    history_before,
                    before,
                    present,
                    completion: Completion::InWorkspace {
                        output,
                        invocation: full.join(" "),
                        place,
                        stale,
                        refusals,
                    },
                }
            }
            Command::AtOperation { op, args } => {
                let before = Seen::of(&[self.view_at(m, op)]);
                let present = self.abandoned_present(m);
                let heads_before = self.op_heads(m);
                let history_before = self.command_history(m);
                let mut full = vec!["--at-op", op];
                full.extend_from_slice(args);
                // The operation's id differs between runs of a case; what it did does not.
                self.record(format!(
                    "{}: jj --at-op {} ({:?}) {}",
                    self.machine(m),
                    &op[..12],
                    self.op_description(m, op),
                    args.join(" ")
                ));
                let output = self.fx.repo(m).jj_output(&full);
                CommandExecution {
                    history_before,
                    before,
                    present,
                    completion: Completion::AtOperation {
                        output,
                        invocation: full.join(" "),
                        heads_before,
                    },
                }
            }
        };

        // Include snapshots and imports even when the requested work then failed.
        self.record_commands(m, &history_before);
        match completion {
            Completion::Observed(view) => {
                self.forgive_jj_returns(m, present);
                self.learn(&view);
                let after = Seen::of(std::slice::from_ref(&view));
                let what = format!("{}: (looking)", self.machine(m));
                self.ledger.record(m, &what, &before, &after, false);
                let heads = self.op_heads(m);
                self.seen[m] = Some((heads, after));
                Ok(CommandResult::Observed(view))
            }
            Completion::InWorkspace {
                output,
                invocation,
                place,
                stale,
                refusals,
            } => {
                let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
                if !output.status.success() {
                    if refusals.iter().any(|r| stderr.contains(r)) {
                        let first = stderr.lines().next().unwrap_or("").to_owned();
                        self.record(format!("  (refused: {first})"));
                        return Err(stderr);
                    }
                    // A command imports before it fails: judge that first.
                    self.check_imports(m);
                    self.fail(&format!("`jj {invocation}` failed on {place}:\n{stderr}"));
                }
                let after = self.seen(m);
                let what = self.trace.last().cloned().unwrap_or_default();
                // A stale workspace snapshots at its older operation before updating,
                // which can leave the working-copy change divergent, as on one machine.
                self.ledger.record(m, &what, &before, &after, stale);
                self.forgive_jj_returns(m, present);
                Ok(CommandResult::Ran(
                    String::from_utf8(output.stdout).unwrap(),
                ))
            }
            Completion::AtOperation {
                output,
                invocation,
                heads_before,
            } => {
                if !output.status.success() {
                    self.fail(&format!(
                        "`jj {invocation}` failed on {}:\n{}",
                        self.machine(m),
                        String::from_utf8_lossy(&output.stderr)
                    ));
                }
                let new_heads: Vec<String> = self
                    .op_heads(m)
                    .into_iter()
                    .filter(|h| !heads_before.contains(h))
                    .collect();
                let views: Vec<View> = new_heads.iter().map(|h| self.view_at(m, h)).collect();
                let after = Seen::of(&views);
                let what = self.trace.last().cloned().unwrap_or_default();
                self.ledger.record(m, &what, &before, &after, true);
                self.forgive_jj_returns(m, present);
                Ok(CommandResult::AtOperation)
            }
        }
    }

    /// How far a recorded command in workspace `ws` of machine `m` is in the situation jj's
    /// duplicate-commit bug needs, which alone may excuse its failure: files written that the
    /// command will snapshot, and a working copy recorded at an operation left behind, as by
    /// `jj op abandon`. Read before the command, which takes the edits.
    fn exposed_to_duplicate_commit_bug(&mut self, m: usize, ws: usize) -> Exposure {
        let edited = std::mem::take(&mut self.workspaces[m][ws].edited);
        Exposure {
            edited,
            left_behind: edited && self.working_copy_left_behind(m, ws),
        }
    }

    /// Runs a recorded `jj` command, `what` in the trace: a command in a workspace or a look,
    /// the only ones this covers. Any other `jj` the test runs (`raw_jj`, the checks', the
    /// setup's) fails as before. When the command fails with jj's known duplicate-commit bug
    /// in the situation it needs (races.md, "Known jj limitations"), which a rerun a second
    /// later recovers from, this runs it again as a user would, at the next seed's later time,
    /// and the trace records it again. The failed attempt leaves jj's own snapshot at the
    /// working copy's operation beside the head, and no merge. A user can sync from that
    /// state, so first it is judged as after any command: its imports, and that every op head
    /// loads. The rerun merges it as any command would, and the caller's capture, from before
    /// the first attempt, takes both runs' operations as the command's, as it takes those of
    /// one run that snapshots and merges.
    fn jj_past_known_bug(
        &mut self,
        m: usize,
        args: &[&str],
        what: &str,
        exposed: Exposure,
    ) -> Output {
        let output = self.fx.repo(m).jj_output(args);
        if !is_jj_duplicate_commit_bug(exposed, output.status.code(), &output.stderr) {
            return output;
        }
        self.record(format!(
            "{}: {}; running it again",
            self.machine(m),
            super::JJ_DUPLICATE_COMMIT_BUG
        ));
        self.check_imports(m);
        self.check_loads_of(m);
        self.record(what.to_owned());
        self.fx.repo(m).jj_output(args)
    }

    pub fn write(&mut self, m: usize, ws: usize, file: &str, contents: &str) {
        self.workspaces[m][ws].edited = true;
        let dir = self.workspaces[m][ws]
            .path
            .clone()
            .unwrap_or_else(|| self.fx.repo(m).path().to_owned());
        let path = dir.join(file);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    pub fn commit(&mut self, m: usize, ws: usize, file: usize) {
        let n = self.next();
        let message = format!("c{n} on {}", self.machine(m));
        self.write(m, ws, FILES[file], &format!("{message}\n"));
        self.record(format!("{}: write {}", self.machine(m), FILES[file]));
        self.jj_in(m, ws, &["commit", "-m", &message]);
    }

    /// Edits a file without running `jj`, so the edit is not snapshotted yet.
    pub fn edit(&mut self, m: usize, file: usize) {
        let n = self.next();
        let contents = format!("edit {n} on {}\n", self.machine(m));
        self.write(m, 0, FILES[file], &contents);
        self.dirty[m] = true;
        self.record(format!(
            "{}: write {} (not snapshotted)",
            self.machine(m),
            FILES[file]
        ));
    }

    /// A fresh description.
    pub fn message(&mut self, m: usize) -> String {
        let n = self.next();
        format!("d{n} on {}", self.machine(m))
    }

    fn git(&mut self, m: usize, args: &[&str]) -> String {
        self.record(format!("{}: git {}", self.machine(m), args.join(" ")));
        self.fx.repo(m).git(args)
    }

    /// Moves a physical branch, recording the rewrite target and the import frontier.
    pub fn move_git_branch(&mut self, m: usize, name: &str, target: &Commit) {
        self.ledger.git_move(Some(&target.change));
        let git_ref = format!("refs/heads/{name}");
        let to = RefTarget::normal(CommitId::try_from_hex(&target.id).unwrap());
        self.git_moves(m, &git_ref, to);
        self.git(m, &["update-ref", &git_ref, &target.id]);
    }

    /// Deletes a physical branch after capturing the import frontier it changes.
    pub fn delete_git_branch(&mut self, m: usize, name: &str) {
        let git_ref = format!("refs/heads/{name}");
        self.git_moves(m, &git_ref, RefTarget::absent());
        self.git(m, &["update-ref", "-d", &git_ref]);
    }

    pub fn add_workspace(&mut self, m: usize, name: &str) {
        self.evidence
            .workspace_births
            .insert(format!("{}/{name}", self.fx.machine_key(m)));
        let n = self.next();
        let path = self
            .fx
            .env
            .root()
            .join(format!("{}-ws{n}", self.machine(m)));
        self.jj(
            m,
            &["workspace", "add", "--name", name, path.to_str().unwrap()],
        );
        self.workspaces[m].push(Workspace {
            name: name.to_owned(),
            path: Some(path),
            edited: false,
        });
    }

    pub fn rename_workspace(&mut self, m: usize, ws: usize, name: &str) {
        self.evidence
            .workspace_births
            .insert(format!("{}/{name}", self.fx.machine_key(m)));
        self.logical_extras[m].remove(&self.workspaces[m][ws].name);
        let old = self.workspaces[m][ws].name.clone();
        self.jj_in(m, ws, &["workspace", "rename", name]);
        self.workspaces[m][ws].name = name.to_owned();
        self.check_own_workspaces_listed(m, &format!("`jj workspace rename {name}`"), &old);
    }

    pub fn forget_workspace(&mut self, m: usize, ws: usize) {
        let name = self.workspaces[m][ws].name.clone();
        self.jj(m, &["workspace", "forget", &name]);
        self.logical_extras[m].remove(&name);
        self.workspaces[m].remove(ws);
        self.check_own_workspaces_listed(m, &format!("`jj workspace forget {name}`"), &name);
    }

    /// After `command` renamed or forgot machine `m`'s workspace `gone`, before any sync:
    /// its latest operation lists its workspaces, and not `gone`. A later merge may bring a
    /// name back, which `check_workspaces` allows for names the copy created; this catches
    /// a rename or forget that never took effect. Read in process, so it changes nothing.
    fn check_own_workspaces_listed(&self, m: usize, command: &str, gone: &str) {
        let store = self.fx.hive.members[m].adapter.repo().loader().op_store();
        let head = jj_lib::op_store::OperationId::try_from_hex(self.latest_op_head(m)).unwrap();
        let view = futures::executor::block_on(async {
            let op = store.read_operation(&head).await.unwrap();
            store.read_view(&op.view_id).await.unwrap()
        });
        let listed: BTreeSet<&str> = view
            .wc_commit_ids
            .keys()
            .map(|name| name.as_str())
            .filter(|name| !name.contains('/'))
            .collect();
        let missing: Vec<&str> = self.workspaces[m]
            .iter()
            .map(|ws| ws.name.as_str())
            .filter(|name| !listed.contains(name))
            .collect();
        let mut wrong = vec![];
        if listed.contains(gone) {
            wrong.push(format!("still {gone:?}"));
        }
        if !missing.is_empty() {
            wrong.push(format!("not {missing:?}"));
        }
        if !wrong.is_empty() {
            self.fail(&format!(
                "after {command}, {} lists workspaces {listed:?}: {}",
                self.machine(m),
                wrong.join(", ")
            ));
        }
    }
}

/// What a command was exposed to, read before it ran.
#[derive(Clone, Copy)]
struct Exposure {
    /// Files were written in its workspace that it snapshots.
    edited: bool,
    /// Its workspace's working copy was recorded at an operation no op head descends from.
    left_behind: bool,
}

/// Whether a `jj` command failed with jj 0.47.1's duplicate-commit bug: snapshotting edits at
/// an operation left behind, then merging that with the op head, recreated in the same
/// second a commit the snapshot wrote, so the command failed as it loaded the repository,
/// before doing its work. Both the situation and the message are required, so that no other
/// failure is excused, such as a musubi defect that made jj rebase twice in one command: an
/// internal error, and these as the last lines.
fn is_jj_duplicate_commit_bug(exposed: Exposure, code: Option<i32>, stderr: &[u8]) -> bool {
    if !(exposed.edited && exposed.left_behind) || code != Some(255) {
        return false;
    }
    let stderr = String::from_utf8_lossy(stderr);
    let lines: Vec<&str> = stderr.lines().collect();
    let [
        ..,
        "Concurrent modification detected, resolving automatically.",
        "Internal error: Failed to load the repo",
        cause,
    ] = lines.as_slice()
    else {
        return false;
    };
    cause
        .strip_prefix("Caused by: Newly-created commit ")
        .and_then(|rest| rest.strip_suffix(" already exists"))
        .is_some_and(|id| id.len() == 40 && id.bytes().all(|b| b.is_ascii_hexdigit()))
}

#[test]
fn only_the_duplicate_commit_bug_is_excused() {
    let exposed = Exposure {
        edited: true,
        left_behind: true,
    };
    let id = "920e8bef9a7837a6d06b34a9b409148ea932cec3";
    let bug = format!(
        "Rebased 1 descendant commits onto updated working copy.\n\
         Concurrent modification detected, resolving automatically.\n\
         Internal error: Failed to load the repo\n\
         Caused by: Newly-created commit {id} already exists\n"
    );
    assert!(is_jj_duplicate_commit_bug(
        exposed,
        Some(255),
        bug.as_bytes()
    ));
    // The same failure without the situation the bug needs: no edits to snapshot, or a
    // working copy at an operation the head descends from.
    for other in [
        Exposure {
            edited: false,
            ..exposed
        },
        Exposure {
            left_behind: false,
            ..exposed
        },
    ] {
        assert!(!is_jj_duplicate_commit_bug(
            other,
            Some(255),
            bug.as_bytes()
        ));
    }
    // Another exit status, no merge before the failure, another failure or cause, a short
    // commit id, or more after it.
    assert!(!is_jj_duplicate_commit_bug(
        exposed,
        Some(1),
        bug.as_bytes()
    ));
    for other in [
        bug.replace(
            "Concurrent modification detected, resolving automatically.\n",
            "",
        ),
        bug.replace(
            "Failed to load the repo",
            "Failed to snapshot the working copy",
        ),
        bug.replace(" already exists", " is missing"),
        bug.replace(id, &id[..12]),
        format!("{bug}Hint: something else\n"),
    ] {
        assert!(
            !is_jj_duplicate_commit_bug(exposed, Some(255), other.as_bytes()),
            "{other}"
        );
    }
}

/// A forget or rename that left the old name listed, or a workspace the machine has a
/// directory for no longer listed, fails at once; one that took effect passes.
#[test]
fn a_forget_or_rename_that_did_not_take_effect_fails() {
    use super::{Naming, Setup};

    let mut world = World::new(Setup {
        nodes: 1,
        naming: Naming::Own,
        prejoin: false,
        secondary: true,
    });
    let failure = |world: &World, gone: &str| {
        let failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            world.check_own_workspaces_listed(0, "the command", gone);
        }))
        .expect_err("the check fails");
        failed.downcast_ref::<String>().unwrap().clone()
    };
    // As if `jj workspace forget second` had done nothing.
    let message = failure(&world, "second");
    assert!(message.contains("still \"second\""), "{message}");
    // As if a rename had dropped a workspace without giving it its new name.
    world.workspaces[0][1].name = "renamed".to_owned();
    let message = failure(&world, "second");
    assert!(message.contains("not [\"renamed\"]"), "{message}");
    world.workspaces[0][1].name = "second".to_owned();
    world.rename_workspace(0, 1, "renamed");
    world.forget_workspace(0, 1);
}
