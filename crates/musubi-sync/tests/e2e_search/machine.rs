//! The Hegel state machine. Rule groups are kept separate (local work, workspaces, the
//! remote, git-side work, sync, faults), so the inconsistent states between them get
//! explored: a machine can work on a stale view, git can move a branch jj has not imported,
//! a node can stop halfway through a sync, and so on.
//!
//! Each rule is eligible only when it has work to do: it draws a machine, computes its
//! candidates from what that machine can see (with a helper of `View`), and rejects the
//! step if there are none.

use std::cell::RefCell;
use std::rc::Rc;

use hegel::TestCase;
use hegel::generators as gs;

use crate::coverage::fired;
use crate::world::BOOKMARKS;
use crate::world::FILES;
use crate::world::TAGS;
use crate::world::World;

/// Faults per sequence, so that a short walk still reaches recovery.
const MAX_FAULTS: usize = 3;
/// `jj undo` per sequence: it discards work, so a sequence full of undos explores little.
const MAX_UNDOS: usize = 2;
/// Full convergence checks per sequence; the end of the sequence always has one.
const MAX_CONVERGES: usize = 1;

/// Refusals `jj git push` makes before pushing anything, for reasons the candidates do not
/// predict (a commit without a description, a conflict, or a remote that moved since the
/// last fetch).
const PUSH_REFUSALS: &[&str] = &[
    "Won't push",
    "Refusing to push",
    "unexpectedly moved",
    "Non-tracking remote bookmark",
];

pub struct Search {
    pub world: Rc<RefCell<World>>,
    pub faults: usize,
    pub undos: usize,
    pub converges: usize,
}

fn pick(tc: &TestCase, len: usize) -> usize {
    tc.draw(gs::integers::<usize>().max_value(len - 1))
}

/// One of `candidates`, rejecting the step if there are none.
fn choose(tc: &TestCase, candidates: &[String]) -> String {
    tc.assume(!candidates.is_empty());
    candidates[pick(tc, candidates.len())].clone()
}

fn strs(args: &[String]) -> Vec<&str> {
    args.iter().map(String::as_str).collect()
}

impl Search {
    fn machine(&self, tc: &TestCase) -> usize {
        let nodes = self.world.borrow().nodes();
        pick(tc, nodes)
    }

    fn note(&self, tc: &TestCase) {
        if let Some(last) = self.world.borrow().trace.last() {
            tc.note(last);
        }
    }

    fn fault(&mut self, tc: &TestCase, rule: &'static str) -> usize {
        tc.assume(self.faults < MAX_FAULTS);
        let m = self.machine(tc);
        self.faults += 1;
        fired(rule);
        m
    }

    /// A machine with a secondary workspace, and that workspace.
    fn secondary(&self, tc: &TestCase) -> (usize, usize) {
        let m = self.machine(tc);
        let count = self.world.borrow().workspaces[m].len();
        tc.assume(count > 1);
        (m, 1 + pick(tc, count - 1))
    }
}

#[hegel::state_machine]
impl Search {
    // Local work, through the jj CLI.

    #[rule(weight = 4)]
    fn commit(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let file = pick(&tc, FILES.len());
        fired("commit");
        self.world.borrow_mut().commit(m, 0, file);
        self.note(&tc);
    }

    #[rule]
    fn edit_unsnapshotted(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let file = pick(&tc, FILES.len());
        fired("edit_unsnapshotted");
        self.world.borrow_mut().edit(m, file);
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn describe(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let commit = choose(&tc, &world.observe(m).mutable());
        fired("describe");
        let message = world.message(m);
        world.jj(m, &["describe", &commit, "-m", &message]);
        drop(world);
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn new_commit(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let parent = choose(&tc, &world.observe(m).bases());
        fired("new_commit");
        world.jj(m, &["new", &parent]);
        drop(world);
        self.note(&tc);
    }

    #[rule]
    fn new_merge(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let view = world.observe(m);
        let first = choose(&tc, &view.bases());
        let second = choose(&tc, &view.unrelated(&first));
        fired("new_merge");
        world.jj(m, &["new", &first, &second]);
        drop(world);
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn rebase_revision(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let view = world.observe(m);
        let revision = choose(&tc, &view.mutable());
        let onto = choose(&tc, &view.rebase_revision_destinations(&revision));
        fired("rebase_revision");
        world.jj(m, &["rebase", "-r", &revision, "-o", &onto]);
        drop(world);
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn rebase_source(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let view = world.observe(m);
        let source = choose(&tc, &view.mutable());
        let onto = choose(&tc, &view.rebase_source_destinations(&source));
        fired("rebase_source");
        world.jj(m, &["rebase", "-s", &source, "-o", &onto]);
        drop(world);
        self.note(&tc);
    }

    #[rule]
    fn squash(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let commit = choose(&tc, &world.observe(m).squashable());
        fired("squash");
        world.jj(m, &["squash", "-r", &commit, "--use-destination-message"]);
        drop(world);
        self.note(&tc);
    }

    /// Squashes one commit's work into another, which another machine may be squashing
    /// into too.
    #[rule]
    fn squash_into(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let view = world.observe(m);
        let mutable = view.mutable();
        let into = choose(&tc, &mutable);
        let from: Vec<String> = mutable.into_iter().filter(|c| *c != into).collect();
        let from = choose(&tc, &from);
        fired("squash_into");
        world.jj(
            m,
            &[
                "squash",
                "--from",
                &from,
                "--into",
                &into,
                "--use-destination-message",
            ],
        );
        drop(world);
        self.note(&tc);
    }

    #[rule]
    fn abandon(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let commit = choose(&tc, &world.observe(m).mutable());
        fired("abandon");
        world.jj(m, &["abandon", &commit]);
        drop(world);
        self.note(&tc);
    }

    /// Resolves a conflicted commit (rebases of shared files make them), taking one side.
    #[rule]
    fn resolve(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let commit = choose(&tc, &world.observe(m).conflicted());
        let tool = [":ours", ":theirs"][pick(&tc, 2)];
        fired("resolve");
        world.jj(m, &["resolve", "-r", &commit, "--tool", tool]);
        drop(world);
        self.note(&tc);
    }

    /// Abandons another machine's working-copy commit.
    #[rule]
    fn abandon_other_wc(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let commit = choose(&tc, &world.observe(m).other_working_copies());
        fired("abandon_other_wc");
        world.jj(m, &["abandon", &commit]);
        drop(world);
        self.note(&tc);
    }

    /// Rewrites a commit under another machine's working copy, which that machine must
    /// follow, possibly with edits it has not snapshotted.
    #[rule(weight = 2)]
    fn rewrite_under_other_wc(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let view = world.observe(m);
        let commit = choose(&tc, &view.under_other_working_copies());
        if tc.draw(gs::booleans()) {
            let onto = choose(&tc, &view.rebase_source_destinations(&commit));
            fired("rewrite_under_other_wc");
            world.jj(m, &["rebase", "-s", &commit, "-o", &onto]);
        } else {
            fired("rewrite_under_other_wc");
            let message = world.message(m);
            world.jj(m, &["describe", &commit, "-m", &message]);
        }
        drop(world);
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn bookmark_create(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let view = world.observe(m);
        let existing = view.bookmarks();
        let remote = view.remote_names();
        let free: Vec<String> = BOOKMARKS
            .iter()
            .map(|b| (*b).to_owned())
            .filter(|b| !existing.contains(b) && !remote.contains(b))
            .collect();
        let name = choose(&tc, &free);
        let target = choose(&tc, &view.targets());
        fired("bookmark_create");
        // A tracked remote bookmark on a hidden commit is not in the view.
        let _refused = world.try_jj_in(
            m,
            0,
            &["bookmark", "create", &name, "-r", &target],
            &["Tracked remote bookmarks exist"],
        );
        drop(world);
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn bookmark_move(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let view = world.observe(m);
        let name = choose(&tc, &view.bookmarks());
        let target = choose(&tc, &view.targets());
        fired("bookmark_move");
        world.jj(
            m,
            &[
                "bookmark",
                "move",
                &name,
                "--to",
                &target,
                "--allow-backwards",
            ],
        );
        drop(world);
        self.note(&tc);
    }

    #[rule]
    fn bookmark_delete(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let name = choose(&tc, &world.observe(m).bookmarks());
        fired("bookmark_delete");
        world.jj(m, &["bookmark", "delete", &name]);
        drop(world);
        self.note(&tc);
    }

    #[rule]
    fn bookmark_set(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let name = BOOKMARKS[pick(&tc, BOOKMARKS.len())];
        let mut world = self.world.borrow_mut();
        let target = choose(&tc, &world.observe(m).targets());
        fired("bookmark_set");
        world.jj(
            m,
            &["bookmark", "set", name, "-r", &target, "--allow-backwards"],
        );
        drop(world);
        self.note(&tc);
    }

    #[rule]
    fn tag_set(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let name = TAGS[pick(&tc, TAGS.len())];
        let mut world = self.world.borrow_mut();
        let target = choose(&tc, &world.observe(m).targets());
        fired("tag_set");
        world.jj(m, &["tag", "set", name, "-r", &target, "--allow-move"]);
        drop(world);
        self.note(&tc);
    }

    #[rule]
    fn tag_delete(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let name = choose(&tc, &world.observe(m).tags());
        fired("tag_delete");
        world.jj(m, &["tag", "delete", &name]);
        drop(world);
        self.note(&tc);
    }

    #[rule]
    fn undo(&mut self, tc: TestCase) {
        tc.assume(self.undos < MAX_UNDOS);
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        tc.assume(world.can_undo(m));
        self.undos += 1;
        fired("undo");
        // jj refuses to undo another workspace's operation unless told to, and another
        // machine's operations are another workspace's even when the names match.
        let made_in = world.head_op_workspace(m);
        let made_in = made_in.trim_end_matches('@').trim_matches('"');
        let own = made_in.is_empty() || made_in == world.workspaces[m][0].name;
        let refusal = "Refusing to undo operation";
        match world.try_jj_in(m, 0, &["undo"], &[refusal]) {
            Ok(_) if !own => world.fail(&format!("`jj undo` undid an operation made in {made_in}")),
            Ok(_) => {}
            Err(_) if own => world.fail("`jj undo` refused this workspace's own operation"),
            Err(_) => {
                world.jj(m, &["undo", "--allow-cross-workspace"]);
            }
        }
        drop(world);
        self.note(&tc);
    }

    /// A command based at an older operation, as a long-running command or `--at-op`
    /// produces: a concurrent operation on one machine.
    #[rule(weight = 2)]
    fn at_op(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let ops = world.older_ops(m);
        let op = choose(&tc, &ops);
        let view = world.view_at(m, &op);
        let args: Vec<String> = match pick(&tc, 4) {
            0 => {
                let commit = choose(&tc, &view.mutable());
                let message = world.message(m);
                vec!["describe".into(), commit, "-m".into(), message]
            }
            1 => vec!["abandon".into(), choose(&tc, &view.mutable())],
            2 => vec!["new".into(), choose(&tc, &view.bases())],
            _ => {
                let name = BOOKMARKS[pick(&tc, BOOKMARKS.len())];
                let target = choose(&tc, &view.targets());
                vec![
                    "bookmark".into(),
                    "set".into(),
                    name.into(),
                    "-r".into(),
                    target,
                    "--allow-backwards".into(),
                ]
            }
        };
        fired("at_op");
        world.jj_at_op(m, &op, &strs(&args));
        drop(world);
        self.note(&tc);
    }

    /// Any `jj` command: snapshots, imports git refs, merges concurrent operations, and
    /// updates a stale working copy.
    #[rule]
    fn status(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        fired("status");
        self.world.borrow_mut().jj(m, &["status"]);
        self.note(&tc);
    }

    // Workspaces: per machine; other machines only ever see their commits.

    #[rule]
    fn workspace_add(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        tc.assume(world.workspaces[m].len() < 3);
        let name = choose(&tc, &world.free_workspace_names(m));
        fired("workspace_add");
        world.add_workspace(m, &name);
        drop(world);
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn workspace_commit(&mut self, tc: TestCase) {
        let (m, ws) = self.secondary(&tc);
        let file = pick(&tc, FILES.len());
        fired("workspace_commit");
        self.world.borrow_mut().commit(m, ws, file);
        self.note(&tc);
    }

    #[rule]
    fn workspace_rename(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let ws = pick(&tc, world.workspaces[m].len());
        let name = choose(&tc, &world.free_workspace_names(m));
        fired("workspace_rename");
        world.rename_workspace(m, ws, &name);
        drop(world);
        self.note(&tc);
    }

    #[rule]
    fn workspace_forget(&mut self, tc: TestCase) {
        let (m, ws) = self.secondary(&tc);
        fired("workspace_forget");
        self.world.borrow_mut().forget_workspace(m, ws);
        self.note(&tc);
    }

    /// Tries to forget a workspace that only another machine has: jj warns that there is
    /// no such workspace, and nothing changes.
    #[rule]
    fn forget_other_workspace(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let name = choose(&tc, &world.foreign_workspace_names(m));
        fired("forget_other_workspace");
        world.jj(m, &["workspace", "forget", &name]);
        drop(world);
        self.note(&tc);
    }

    // The shared remote.

    /// Someone outside the hive pushes to origin's `main`.
    #[rule]
    fn origin_advance(&mut self, tc: TestCase) {
        fired("origin_advance");
        let mut world = self.world.borrow_mut();
        let message = world.origin.advance();
        world.record(format!("origin: push {message}"));
        drop(world);
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn fetch(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        fired("fetch");
        self.world.borrow_mut().jj(m, &["git", "fetch"]);
        self.note(&tc);
    }

    #[rule]
    fn push(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let name = choose(&tc, &world.observe(m).pushable_bookmarks());
        fired("push");
        let pushed = world.try_jj_in(m, 0, &["git", "push", "--bookmark", &name], PUSH_REFUSALS);
        if pushed.is_ok() {
            fired("push:accepted");
        }
        drop(world);
        self.note(&tc);
    }

    // Git-side work in the colocated repository, which jj imports on its next command.

    #[rule(weight = 2)]
    fn git_set_branch(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let name = BOOKMARKS[pick(&tc, BOOKMARKS.len())];
        let mut world = self.world.borrow_mut();
        let view = world.view_at_head(m);
        let target = choose(&tc, &view.targets());
        let change = view
            .commits
            .iter()
            .find(|c| c.id == target)
            .map(|c| c.change.clone());
        fired("git_set_branch");
        world.ledger.git_move(name, change.as_deref());
        world.git(m, &["update-ref", &format!("refs/heads/{name}"), &target]);
        drop(world);
        self.note(&tc);
    }

    #[rule]
    fn git_delete_branch(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let branch = choose(&tc, &world.git_branches(m));
        fired("git_delete_branch");
        world.ledger.git_move(&branch, None);
        world.git(m, &["update-ref", "-d", &format!("refs/heads/{branch}")]);
        drop(world);
        self.note(&tc);
    }

    // Sync: one node at a time, so machines see each other's work partially.

    #[rule(weight = 5)]
    fn sync(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        fired("sync");
        self.world.borrow_mut().sync(m);
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn sync_partial(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let steps = tc.draw(gs::integers::<usize>().min_value(1).max_value(4));
        fired("sync_partial");
        self.world.borrow_mut().sync_partial(m, steps, None);
        self.note(&tc);
    }

    /// Full convergence in the middle of a sequence, with every property checked; the
    /// ledger starts afresh.
    #[rule]
    fn converge(&mut self, tc: TestCase) {
        tc.assume(self.converges < MAX_CONVERGES);
        self.converges += 1;
        fired("converge");
        self.world.borrow_mut().converge();
        self.note(&tc);
    }

    // Faults.

    #[rule]
    fn restart(&mut self, tc: TestCase) {
        let m = self.fault(&tc, "restart");
        self.world.borrow_mut().restart(m);
        self.note(&tc);
    }

    #[rule]
    fn crash(&mut self, tc: TestCase) {
        let m = self.fault(&tc, "crash");
        self.world.borrow_mut().crash(m, false);
        self.note(&tc);
    }

    #[rule]
    fn lose_cache(&mut self, tc: TestCase) {
        let m = self.fault(&tc, "lose_cache");
        self.world.borrow_mut().crash(m, true);
        self.note(&tc);
    }

    #[rule]
    fn restart_hub(&mut self, tc: TestCase) {
        tc.assume(self.faults < MAX_FAULTS);
        self.faults += 1;
        fired("restart_hub");
        self.world.borrow_mut().restart_hub();
        self.note(&tc);
    }

    /// A sync in which the reply to one request is lost after the hub handled it.
    #[rule]
    fn lose_reply(&mut self, tc: TestCase) {
        let m = self.fault(&tc, "lose_reply");
        let steps = tc.draw(gs::integers::<usize>().min_value(1).max_value(4));
        let lost = tc.draw(gs::integers::<usize>().max_value(4));
        self.world.borrow_mut().sync_partial(m, steps, Some(lost));
        self.note(&tc);
    }

    #[invariant(always_run)]
    fn repositories_load(&mut self, _: TestCase) {
        self.world.borrow_mut().check_loads();
    }
}
