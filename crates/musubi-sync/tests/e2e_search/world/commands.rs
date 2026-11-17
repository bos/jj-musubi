//! User actions: jj and git commands, edits and workspace changes. An observation through
//! a jj command is an action too: it can snapshot, import and merge. Each action records
//! its native evidence before subsequent syncs can rewrite it.

use std::collections::BTreeSet;
use std::fs;
use std::process::Output;

use crate::identity::SourceKey;
use crate::ledger::Seen;
use crate::view::Commit;
use crate::view::TEMPLATE;
use crate::view::View;

use super::CommandOutcome;
use super::FILES;
use super::OperationHistory;
use super::Workspace;
use super::World;

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
    pub fn older_ops(&mut self, m: usize) -> Vec<String> {
        // Through a recorded command: it merges concurrent operations first.
        self.jj(m, &["op", "log", "--no-graph", "-n", "8", "-T", "id"]);
        self.op_ids_and_keys(m, Some(8))
            .into_iter()
            .skip(1)
            .filter(|(id, key)| {
                !self.evidence.baseline_ids[m].contains(id)
                    && !self.evidence.baseline_keys[m].contains(key)
            })
            .map(|(id, _)| id)
            .collect()
    }

    /// Those of `older_ops` that `jj op abandon` can abandon: not merges, which it refuses.
    pub fn abandonable_ops(&mut self, m: usize) -> Vec<String> {
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
            .filter(|op| !merges.contains(op))
            .collect()
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

    /// Runs one complete actor action: capture inputs, execute, record native sources,
    /// then finish ledger and return bookkeeping. Keep each variant's chronology explicit.
    fn recorded_command(
        &mut self,
        m: usize,
        command: Command<'_>,
    ) -> Result<CommandResult, String> {
        match &command {
            Command::Observe => {}
            Command::InWorkspace { args, .. }
                if matches!(args.first(), Some(&"describe" | &"squash")) => {}
            _ => crate::coverage::interrupt_races(),
        }
        let CommandExecution {
            history_before,
            before,
            present,
            completion,
        } = match command {
            Command::Observe => {
                let history_before = self.command_history(m);
                let before = self.seen(m);
                self.dirty[m] = false;
                let present = self.abandoned_present(m);
                // A failed native observation or parse fails before source recording.
                let view = View::parse(
                    &self.raw_jj(m, &["log", "--no-graph", "-r", "all()", "-T", TEMPLATE]),
                );
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
                self.record(format!("{place}: jj {}", args.join(" ")));
                let output = self.fx.repo(m).jj_output(&full);
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
                self.record(format!(
                    "{}: jj --at-op {} {}",
                    self.machine(m),
                    &op[..12],
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
        let succeeded = match &completion {
            Completion::Observed(_) => true,
            Completion::InWorkspace { output, .. } | Completion::AtOperation { output, .. } => {
                output.status.success()
            }
        };
        let outcome = if succeeded {
            CommandOutcome::Succeeded
        } else {
            crate::coverage::interrupt_races();
            CommandOutcome::Failed
        };
        self.record_commands(m, &history_before, outcome);
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

    pub fn write(&mut self, m: usize, ws: usize, file: &str, contents: &str) {
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
        crate::coverage::interrupt_races();
        self.record(format!("{}: git {}", self.machine(m), args.join(" ")));
        self.fx.repo(m).git(args)
    }

    /// Moves a physical branch, recording the rewrite target and the import frontier.
    pub fn move_git_branch(&mut self, m: usize, name: &str, target: &Commit) {
        self.ledger.git_move(Some(&target.change));
        let git_ref = format!("refs/heads/{name}");
        self.git_moves(m, &git_ref);
        self.git(m, &["update-ref", &git_ref, &target.id]);
    }

    /// Deletes a physical branch after capturing the import frontier it changes.
    pub fn delete_git_branch(&mut self, m: usize, name: &str) {
        let git_ref = format!("refs/heads/{name}");
        self.git_moves(m, &git_ref);
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
        });
    }

    pub fn rename_workspace(&mut self, m: usize, ws: usize, name: &str) {
        self.evidence
            .workspace_births
            .insert(format!("{}/{name}", self.fx.machine_key(m)));
        self.logical_extras[m].remove(&self.workspaces[m][ws].name);
        self.jj_in(m, ws, &["workspace", "rename", name]);
        self.workspaces[m][ws].name = name.to_owned();
    }

    pub fn forget_workspace(&mut self, m: usize, ws: usize) {
        let name = self.workspaces[m][ws].name.clone();
        self.jj(m, &["workspace", "forget", &name]);
        self.logical_extras[m].remove(&name);
        self.workspaces[m].remove(ws);
    }
}
