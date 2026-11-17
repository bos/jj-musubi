//! What a rule may read of a machine: operation heads, views, candidate commands and
//! workspace state. Staleness probes preserve the actor's original command-seed chronology;
//! observer settings use an independent RNG. Commands that can change the repo live in
//! `commands`, including `observe`.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;

use jj_lib::object_id::ObjectId as _;
use jj_lib::settings::UserSettings;
use jj_lib::workspace::WorkspaceLoaderFactory as _;
use musubi_jj::op_id::CanonicalOp;
use musubi_sync::OpId;

use crate::ledger::Seen;
use crate::view::TEMPLATE;
use crate::view::View;

use crate::identity::{HistoryKey, NativeOperation};

use super::BOOKMARKS;
use super::OP_KEY_TEMPLATE;
use super::StaleObservation;
use super::WORKSPACES;
use super::World;

impl World {
    /// Runs `jj`, which must succeed, recording nothing.
    pub fn raw_jj(&self, m: usize, args: &[&str]) -> String {
        let output = self.fx.repo(m).jj_output(args);
        if !output.status.success() {
            self.fail(&format!(
                "`jj {}` failed on {}:\n{}",
                args.join(" "),
                self.machine(m),
                String::from_utf8_lossy(&output.stderr)
            ));
        }
        String::from_utf8(output.stdout).unwrap()
    }

    /// The local op heads, read from the op heads store without loading the repository.
    pub fn op_heads(&self, m: usize) -> Vec<String> {
        let dir = self.fx.repo(m).repo_path().join("op_heads/heads");
        let mut heads: Vec<String> = fs::read_dir(&dir)
            .unwrap()
            .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
            .collect();
        heads.sort();
        heads
    }

    /// What machine `m` saw at an operation, read-only: no snapshot, import, or merge.
    pub fn view_at(&self, m: usize, op: &str) -> View {
        View::parse(&self.raw_jj(
            m,
            &[
                "--at-op",
                op,
                "log",
                "--no-graph",
                "-r",
                "all()",
                "-T",
                TEMPLATE,
            ],
        ))
    }

    /// The view at machine `m`'s latest op head, without perturbing anything.
    pub fn view_at_head(&self, m: usize) -> View {
        let head = self.latest_op_head(m);
        self.view_at(m, &head)
    }

    /// Machine `m`'s op head that ended last, by its view where two ended together. Not
    /// the first by id: jj records each command's arguments in its operation, temporary
    /// paths and all, so ids differ from one run of a case to the next.
    pub fn latest_op_head(&self, m: usize) -> String {
        let store = self.fx.hive.members[m].adapter.repo().loader().op_store();
        let key = |head: &String| {
            let id = jj_lib::op_store::OperationId::try_from_hex(head).unwrap();
            match futures::executor::block_on(store.read_operation(&id)) {
                Ok(op) => (op.metadata.time.end.timestamp, op.view_id.hex()),
                Err(err) => self.fail(&format!(
                    "reading {}'s op head {head}: {err}",
                    self.machine(m)
                )),
            }
        };
        self.op_heads(m)
            .into_iter()
            .max_by_key(key)
            .expect("a repository has an op head")
    }

    /// What machine `m` sees at all its op heads, remembered while they do not change.
    pub(super) fn seen(&mut self, m: usize) -> Seen {
        let heads = self.op_heads(m);
        if let Some((cached, seen)) = &self.seen[m]
            && *cached == heads
        {
            return seen.clone();
        }
        let views: Vec<View> = heads.iter().map(|h| self.view_at(m, h)).collect();
        for view in &views {
            self.learn(view);
        }
        let seen = Seen::of(&views);
        self.seen[m] = Some((heads, seen.clone()));
        seen
    }

    /// Whether workspace `ws` of machine `m` is stale: its working-copy commit has changed
    /// since the operation its working copy was last updated at. With several op heads,
    /// assumed so.
    pub(super) fn is_stale(&self, m: usize, ws: usize) -> bool {
        let observed = self.stale_observation(m, ws);
        if std::env::var_os("MUSUBI_SEARCH_VERIFY_OBSERVATIONS").is_some() {
            // The native probes reserve their own seeds. Comparing before replacing them
            // leaves the rest of the case's actor chronology exactly as it was.
            assert_eq!(observed, self.native_stale_observation(m, ws));
        } else {
            self.fx
                .repo(m)
                .reserve_command_seeds(observed.command_seeds);
        }
        observed.stale
    }

    /// A settings clone shares the actor's RNG, and TestRepo::settings takes an actor
    /// seed. Rebuild the complete configuration with an independent RNG and the same
    /// hermetic home, including when observing a replacement copy.
    pub(crate) fn observer_settings(&self, m: usize) -> UserSettings {
        let actor = self.fx.hive.members[m].adapter.repo().loader().settings();
        UserSettings::from_config_and_home_dir(
            actor.config().clone(),
            Some(self.fx.env.root().join("home")),
        )
        .unwrap()
    }

    pub(super) fn stale_observation(&self, m: usize, ws: usize) -> StaleObservation {
        let heads = self.op_heads(m);
        let [head] = heads.as_slice() else {
            return StaleObservation {
                stale: true,
                command_seeds: 0,
            };
        };
        let unavailable = StaleObservation {
            stale: true,
            command_seeds: 1,
        };
        let path = self.workspaces[m][ws]
            .path
            .as_deref()
            .unwrap_or_else(|| self.fx.repo(m).path());
        let Ok(loader) = jj_lib::workspace::DefaultWorkspaceLoaderFactory.create(path) else {
            return unavailable;
        };
        let Ok(workspace) = loader.load(
            &self.observer_settings(m),
            &jj_lib::default_backend_factories::default_backend_factories(),
            &jj_lib::default_backend_factories::default_working_copy_factories(),
        ) else {
            return unavailable;
        };
        let store = workspace.repo_loader().op_store();
        let view_at = |id: &OpId| {
            futures::executor::block_on(async {
                let op = store.read_operation(id).await.ok()?;
                store.read_view(&op.view_id).await.ok()
            })
        };
        // `debug working-copy` loads the current repo before printing its recorded
        // operation. Failure there takes just its first command seed.
        let Some(current) = OpId::try_from_hex(head).and_then(|id| view_at(&id)) else {
            return unavailable;
        };
        let recorded = view_at(workspace.working_copy().operation_id());
        let name = jj_lib::ref_name::WorkspaceName::new(&self.workspaces[m][ws].name);
        // jj's `<workspace>@` revset reads this exact binding. A missing binding (or
        // unavailable old operation) prints no commit id, so compare optional targets.
        let before = recorded
            .as_ref()
            .and_then(|view| view.wc_commit_ids.get(name));
        StaleObservation {
            stale: before != current.wc_commit_ids.get(name),
            command_seeds: 3,
        }
    }

    /// Independent native oracle for validating the in-process observer across the search.
    pub(super) fn native_stale_observation(&self, m: usize, ws: usize) -> StaleObservation {
        let heads = self.op_heads(m);
        let [head] = heads.as_slice() else {
            return StaleObservation {
                stale: true,
                command_seeds: 0,
            };
        };
        let mut place = vec![];
        if let Some(path) = &self.workspaces[m][ws].path {
            place.extend(["-R".to_owned(), path.to_string_lossy().into_owned()]);
        }
        let jj = |args: &[&str]| {
            let mut full: Vec<&str> = place.iter().map(String::as_str).collect();
            full.extend_from_slice(args);
            let output = self.fx.repo(m).jj_output(&full);
            String::from_utf8_lossy(&output.stdout).into_owned()
        };
        let state = jj(&["--ignore-working-copy", "debug", "working-copy"]);
        let Some(updated_at) = state
            .split_once("Current operation: OperationId(\"")
            .and_then(|(_, rest)| rest.split_once('"'))
            .map(|(op, _)| op.to_owned())
        else {
            return StaleObservation {
                stale: true,
                command_seeds: 1,
            };
        };
        let wc = format!("{}@", self.workspaces[m][ws].name);
        let at = |op: &str| {
            jj(&[
                "--ignore-working-copy",
                "--at-op",
                op,
                "log",
                "--no-graph",
                "-r",
                &wc,
                "-T",
                "commit_id",
            ])
        };
        StaleObservation {
            stale: at(&updated_at) != at(head),
            command_seeds: 3,
        }
    }

    /// Machine `m`'s operations, newest first, or only the first `limit`, by id with their
    /// keys, as `op_keys` has them.
    pub(super) fn op_ids_and_keys(
        &self,
        m: usize,
        limit: Option<usize>,
    ) -> Vec<(String, HistoryKey)> {
        let template = format!(r#"id ++ " " ++ {OP_KEY_TEMPLATE}"#);
        let limit = limit.map(|n| n.to_string());
        let mut args = vec![
            "--ignore-working-copy",
            "op",
            "log",
            "--no-graph",
            "-T",
            &template,
        ];
        if let Some(limit) = &limit {
            args.extend(["-n", limit]);
        }
        self.raw_jj(m, &args)
            .lines()
            .filter_map(|line| line.split_once(' '))
            .map(|(id, key)| (id.to_owned(), HistoryKey::from_template(key)))
            .collect()
    }

    /// Whether `jj undo` on machine `m` would undo an ordinary operation made since setup:
    /// one op head, not a merge (jj refuses to undo those), not itself an undo or redo
    /// (repeated undos walk further back, eventually into the setup), not a workspace
    /// operation, and no pending edit (whose snapshot would be undone instead).
    pub fn can_undo(&self, m: usize) -> bool {
        if self.dirty[m] {
            return false;
        }
        let heads = self.op_heads(m);
        if heads.len() != 1 || self.evidence.baseline_ids[m].contains(&heads[0]) {
            return false;
        }
        let info = self.raw_jj(
            m,
            &[
                "--at-op",
                &heads[0],
                "op",
                "log",
                "--no-graph",
                "-n",
                "1",
                "-T",
                r#"parents.len() ++ " " ++ description"#,
            ],
        );
        let (parents, description) = info.split_once(' ').unwrap_or((&info, ""));
        // Undoing a workspace operation strands a working copy: after undoing a rename,
        // the working copy's recorded name is no longer in the view, and jj says the
        // command "requires a working copy". jj's own behavior; jj refuses it too unless
        // told `--allow-cross-workspace`, which the `undo` rule uses after checking that
        // jj refuses other workspaces' and machines' operations.
        parents == "1"
            && !matches!(
                NativeOperation::from_description(description),
                NativeOperation::Undo | NativeOperation::Redo
            )
            && !description.to_lowercase().contains("workspace")
    }

    /// The workspace that made the head operation, as `jj op log` shows it: `default@`,
    /// `beta/default@` for another machine's, or nothing for an operation musubi made.
    pub fn head_op_workspace(&self, m: usize) -> String {
        let head = self.latest_op_head(m);
        let template = "workspace_name";
        self.raw_jj(
            m,
            &[
                "--at-op",
                &head,
                "op",
                "log",
                "--no-graph",
                "-n",
                "1",
                "-T",
                template,
            ],
        )
    }

    /// If machine `m`'s latest operation is an undo, the workspace that made the operation
    /// it undid, as `jj op log` shows it. (Without anything to change, `jj undo` writes no
    /// operation.)
    pub fn undone_workspace(&self, m: usize) -> Option<String> {
        let template =
            r#"description.first_line() ++ "\t" ++ parents.map(|p| p.workspace_name()).join(",")"#;
        let latest = self.raw_jj(
            m,
            &[
                "--ignore-working-copy",
                "op",
                "log",
                "--no-graph",
                "-n",
                "1",
                "-T",
                template,
            ],
        );
        let (description, parents) = latest.split_once('\t')?;
        description
            .starts_with("undo: restore to operation")
            .then(|| parents.trim().to_owned())
    }

    pub fn git_branches(&self, m: usize) -> Vec<String> {
        self.fx
            .repo(m)
            .git(&["for-each-ref", "--format=%(refname:lstrip=2)", "refs/heads"])
            .lines()
            .map(str::to_owned)
            .collect()
    }

    /// Whether node `m` has yet to realize the hub's head.
    pub fn behind_hub(&self, m: usize) -> bool {
        let head = CanonicalOp(self.fx.hive.hub.store().head().1.clone());
        self.fx.hive.members[m]
            .adapter
            .repo()
            .local_of(&head)
            .is_none()
    }

    /// Whether machine `m`'s git has the `origin` remote: configured explicitly for each machine,
    /// including a new copy before it joins.
    pub fn has_origin(&self, m: usize) -> bool {
        self.fx
            .repo(m)
            .git(&["remote"])
            .lines()
            .any(|r| r == "origin")
    }

    /// Each workspace's working-copy commit on machine `m`, by name.
    pub fn working_copies(&self, m: usize) -> BTreeMap<String, String> {
        self.workspaces[m]
            .iter()
            .map(|ws| ws.name.clone())
            .chain(self.logical_extras[m].iter().cloned())
            .map(|name| {
                let id = self.raw_jj(
                    m,
                    &[
                        "log",
                        "--ignore-working-copy",
                        "--no-graph",
                        "-r",
                        &format!("{name}@"),
                        "-T",
                        "commit_id",
                    ],
                );
                (name, id)
            })
            .collect()
    }

    /// The first line of the description of machine `m`'s operation `op`, read at that
    /// operation: no snapshot, import, or merge.
    pub fn op_description(&self, m: usize, op: &str) -> String {
        let described = self.raw_jj(
            m,
            &[
                "--at-op",
                op,
                "op",
                "log",
                "--no-graph",
                "-n",
                "1",
                "-T",
                "description.first_line()",
            ],
        );
        described.trim_end().to_owned()
    }

    /// The first line of the description of each of machine `m`'s newest `limit` operations,
    /// by id.
    pub(super) fn op_descriptions(&self, m: usize, limit: usize) -> BTreeMap<String, String> {
        let limit = limit.to_string();
        self.raw_jj(
            m,
            &[
                "--ignore-working-copy",
                "op",
                "log",
                "--no-graph",
                "-n",
                &limit,
                "-T",
                r#"id ++ " " ++ description.first_line() ++ "\n""#,
            ],
        )
        .lines()
        .filter_map(|line| line.split_once(' '))
        .map(|(id, description)| (id.to_owned(), description.to_owned()))
        .collect()
    }

    /// The lines `jj` prints for `args` at each of machine `m`'s op heads, read at that
    /// operation, as `view_at` reads: without `--at-op`, jj would merge divergent op heads
    /// first, a change no command records, before a rule that reads this can still reject.
    fn lines_at_heads(&self, m: usize, args: &[&str]) -> Vec<BTreeSet<String>> {
        self.op_heads(m)
            .iter()
            .map(|head| {
                let mut full = vec!["--at-op", head];
                full.extend_from_slice(args);
                self.raw_jj(m, &full).lines().map(str::to_owned).collect()
            })
            .collect()
    }

    /// The workspace names machine `m` lists at each of its op heads.
    fn workspace_names_at_heads(&self, m: usize) -> Vec<BTreeSet<String>> {
        self.lines_at_heads(m, &["workspace", "list", "-T", "name ++ \"\\n\""])
    }

    /// The local bookmark names machine `m` has at any op head, whatever they point at. Not
    /// only the view's bookmarks: a conflicted bookmark can have no side that is a commit,
    /// which `jj log` never shows but `jj bookmark create` refuses. jj makes one where a
    /// conflict is resolved and deleted concurrently: from `main` at {A, B, C}, moving it to A on
    /// one machine and deleting it on another leaves {-B, -C} and absent sides, as plain jj
    /// does for the same two operations in one repository.
    fn bookmark_names_at_heads(&self, m: usize) -> BTreeSet<String> {
        self.lines_at_heads(
            m,
            &[
                "bookmark",
                "list",
                "-T",
                r#"if(!remote && present, name ++ "\n")"#,
            ],
        )
        .into_iter()
        .flatten()
        .collect()
    }

    /// Bookmark names from the pool that machine `m` has neither locally, at any op head, nor
    /// on a real remote (`view`'s `remote_names`): `jj bookmark create` refuses those.
    pub fn free_bookmark_names(&self, m: usize, view: &View) -> Vec<String> {
        let existing = self.bookmark_names_at_heads(m);
        let remote = view.remote_names();
        BOOKMARKS
            .iter()
            .map(|name| (*name).to_owned())
            .filter(|name| !existing.contains(name) && !remote.contains(name))
            .collect()
    }

    /// Workspace names from the pool that machine `m` does not use at any op head, so that
    /// none is in use once a command merges them.
    pub fn free_workspace_names(&self, m: usize) -> Vec<String> {
        let mut pool: Vec<String> = WORKSPACES.iter().map(|w| (*w).to_owned()).collect();
        pool.push(self.machine(m).to_owned());
        // Operation preconditions use jj's actual occupied names. Certification of those
        // names remains a separate invariant, so this never authorizes a spurious name.
        let occupied: BTreeSet<String> = self
            .workspace_names_at_heads(m)
            .into_iter()
            .flatten()
            .collect();
        pool.into_iter()
            .filter(|name| !occupied.contains(name))
            .collect()
    }

    /// Other machines' workspaces as machine `m` shows them, `machine/workspace`: those it
    /// shows at every op head, so that it still does once a command merges them.
    pub fn foreign_workspace_names(&self, m: usize) -> Vec<String> {
        let mut heads = self.workspace_names_at_heads(m).into_iter();
        let first = heads.next().expect("a repository has an op head");
        let shown = heads.fold(first, |shown, names| &shown & &names);
        shown
            .into_iter()
            .filter(|name| name.contains('/'))
            .collect()
    }
}
