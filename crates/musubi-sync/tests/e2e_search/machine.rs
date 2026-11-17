//! The Hegel state machine. Rule groups are kept separate (local work, workspaces, the
//! remote, git-side work, sync, faults), so the inconsistent states between them get
//! explored: a machine can work on a stale view, git can move a branch jj has not imported,
//! a node can stop halfway through a sync, and so on.
//!
//! Each rule is eligible only when it has work to do, and rejects a step only before it acts:
//! Hegel restores nothing on a rejection. Where it is cheap to know first which machines can
//! do the work, a rule draws among those. Where a rule must look first, through a recorded
//! `jj` command that can snapshot, import and merge, it draws its candidates from what it saw
//! (with a helper of `View`), and if there are none the step stands as that look.
//!
//! Draws print as what they mean, so that a failure's printout reads as a reproduction: a
//! machine, file or workspace by name, a commit by id, an operation by what it did and how far
//! back it is (its id differs from one run of a case to the next, so it comes second), a
//! choice by its variant. Each step notes the trace entries it added.

use std::fmt;

use hegel::TestCase;
use hegel::generators as gs;

use crate::coverage::fired;
use crate::world::BOOKMARKS;
use crate::world::FILES;
use crate::world::MACHINES;
use crate::world::PastOp;
use crate::world::SEARCH_MACHINES;
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

pub struct Search<'a> {
    world: &'a mut World,
    faults: usize,
    undos: usize,
    converges: usize,
    /// How much of the world's trace earlier steps (or the setup) have accounted for.
    noted: usize,
}

/// An item of a pool the world indexes, printed as its name.
#[derive(Clone)]
struct Named {
    index: usize,
    name: String,
}

impl fmt::Debug for Named {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.name, f)
    }
}

/// The index of one of `items` (index and name), printed under `what` as its name.
fn draw_named_index(
    tc: &TestCase,
    what: &str,
    items: impl IntoIterator<Item = (usize, String)>,
) -> usize {
    let items: Vec<Named> = items
        .into_iter()
        .map(|(index, name)| Named { index, name })
        .collect();
    tc.draw_named(what, gs::sampled_from(items)).index
}

/// One of `eligible` machines, printed under `what`, rejecting the step if there are none.
fn draw_machine(tc: &TestCase, what: &str, eligible: Vec<usize>) -> usize {
    tc.assume(!eligible.is_empty());
    draw_named_index(
        tc,
        what,
        eligible.into_iter().map(|m| (m, MACHINES[m].to_owned())),
    )
}

/// One of the shared files, by index.
fn draw_file(tc: &TestCase) -> usize {
    draw_named_index(
        tc,
        "file",
        FILES.iter().enumerate().map(|(i, f)| (i, (*f).to_owned())),
    )
}

/// One of `candidates`, which mustn't be empty, printed under `what`.
fn draw_from(tc: &TestCase, what: &str, candidates: Vec<String>) -> String {
    tc.draw_named(what, gs::sampled_from(candidates))
}

/// One of `candidates`, or `None` if there are none: for a rule that has already acted,
/// and so mustn't reject.
fn choose(tc: &TestCase, what: &str, candidates: Vec<String>) -> Option<String> {
    (!candidates.is_empty()).then(|| draw_from(tc, what, candidates))
}

/// The id of one of `ops`, or `None` if there are none, as `choose` does: printed as what the
/// operation did and how far back it is, as well as its id, which differs between runs.
fn choose_op(tc: &TestCase, ops: Vec<PastOp>) -> Option<String> {
    (!ops.is_empty()).then(|| tc.draw_named("op", gs::sampled_from(ops)).id)
}

/// One of `candidates`, rejecting the step if there are none: only before the rule acts.
fn require(tc: &TestCase, what: &str, candidates: Vec<String>) -> String {
    tc.assume(!candidates.is_empty());
    draw_from(tc, what, candidates)
}

fn strs(args: &[String]) -> Vec<&str> {
    args.iter().map(String::as_str).collect()
}

/// How `rewrite_under_other_wc` rewrites a commit.
#[derive(Clone, Copy, Debug)]
enum Rewrite {
    Describe,
    Rebase,
}

/// The command `at_op` runs at an older operation.
#[derive(Clone, Copy, Debug)]
enum AtOpCommand {
    Describe,
    Abandon,
    New,
    BookmarkSet,
}

impl<'a> Search<'a> {
    /// The search over `world`, whose trace so far is the setup's.
    pub fn new(world: &'a mut World) -> Self {
        let noted = world.trace.len();
        Self {
            world,
            faults: 0,
            undos: 0,
            converges: 0,
            noted,
        }
    }

    /// Any machine.
    fn machine(&self, tc: &TestCase) -> usize {
        self.machine_where(tc, |_, _| true)
    }

    /// A machine for which `eligible` holds, rejecting the step if there is none.
    fn machine_where(&self, tc: &TestCase, eligible: impl Fn(&World, usize) -> bool) -> usize {
        let machines = (0..self.world.nodes())
            .filter(|&m| eligible(self.world, m))
            .collect();
        draw_machine(tc, "machine", machines)
    }

    /// A machine other than `m`.
    fn other_than(&self, tc: &TestCase, m: usize) -> usize {
        let nodes = self.world.nodes();
        draw_machine(tc, "other", (0..nodes).filter(|&o| o != m).collect())
    }

    /// A machine with a secondary workspace, and that workspace.
    fn secondary(&self, tc: &TestCase) -> (usize, usize) {
        let m = self.machine_where(tc, |world, m| world.workspaces[m].len() > 1);
        let workspaces = &self.world.workspaces[m];
        let ws = draw_named_index(
            tc,
            "workspace",
            (1..workspaces.len()).map(|ws| (ws, workspaces[ws].name.clone())),
        );
        (m, ws)
    }

    /// Rejects the step if the sequence has had its faults. Fault rules call it first.
    fn may_fault(&self, tc: &TestCase) {
        tc.assume(self.faults < MAX_FAULTS);
    }

    /// Counts a fault, once the rule's preconditions hold.
    fn fault(&mut self, rule: &'static str) {
        self.faults += 1;
        fired(rule);
    }

    /// Notes each trace entry the step added.
    fn note(&mut self, tc: &TestCase) {
        for entry in &self.world.trace[self.noted..] {
            tc.note(entry);
        }
        self.noted = self.world.trace.len();
    }

    /// Ends a step that looked, through a recorded `jj` command, and found nothing to do.
    /// The look can have snapshotted, imported and merged, so the step stands as that
    /// rather than being rejected.
    fn found_nothing(&mut self, tc: &TestCase, m: usize, what: &str) {
        self.note(tc);
        tc.note(&format!("{}: looked, and found {what}", MACHINES[m]));
    }
}

#[hegel::state_machine]
impl Search<'_> {
    // Local work, through the jj CLI.

    #[rule(weight = 4)]
    fn commit(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let file = draw_file(&tc);
        fired("commit");
        self.world.commit(m, 0, file);
        self.note(&tc);
    }

    #[rule]
    fn edit_unsnapshotted(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let file = draw_file(&tc);
        fired("edit_unsnapshotted");
        self.world.edit(m, file);
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn describe(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let Some(commit) = choose(&tc, "commit", self.world.observe(m).mutable()) else {
            return self.found_nothing(&tc, m, "nothing to describe");
        };
        fired("describe");
        let message = self.world.message(m);
        self.world.jj(m, &["describe", &commit, "-m", &message]);
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn new_commit(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let Some(parent) = choose(&tc, "parent", self.world.observe(m).bases()) else {
            return self.found_nothing(&tc, m, "nothing to make a commit on");
        };
        fired("new_commit");
        self.world.jj(m, &["new", &parent]);
        self.note(&tc);
    }

    #[rule]
    fn new_merge(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let view = self.world.observe(m);
        let firsts = view
            .bases()
            .into_iter()
            .filter(|first| !view.unrelated(first).is_empty())
            .collect();
        let Some(first) = choose(&tc, "first", firsts) else {
            return self.found_nothing(&tc, m, "no two unrelated commits to merge");
        };
        let second = draw_from(&tc, "second", view.unrelated(&first));
        fired("new_merge");
        self.world.jj(m, &["new", &first, &second]);
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn rebase_revision(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let view = self.world.observe(m);
        let revisions = view
            .mutable()
            .into_iter()
            .filter(|revision| !view.rebase_revision_destinations(revision).is_empty())
            .collect();
        let Some(revision) = choose(&tc, "revision", revisions) else {
            return self.found_nothing(&tc, m, "nothing to rebase");
        };
        let onto = draw_from(&tc, "onto", view.rebase_revision_destinations(&revision));
        fired("rebase_revision");
        self.world.jj(m, &["rebase", "-r", &revision, "-o", &onto]);
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn rebase_source(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let view = self.world.observe(m);
        let sources = view
            .mutable()
            .into_iter()
            .filter(|source| !view.rebase_source_destinations(source).is_empty())
            .collect();
        let Some(source) = choose(&tc, "source", sources) else {
            return self.found_nothing(&tc, m, "nothing to rebase");
        };
        let onto = draw_from(&tc, "onto", view.rebase_source_destinations(&source));
        fired("rebase_source");
        self.world.jj(m, &["rebase", "-s", &source, "-o", &onto]);
        self.note(&tc);
    }

    #[rule]
    fn squash(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let Some(commit) = choose(&tc, "commit", self.world.observe(m).squashable()) else {
            return self.found_nothing(&tc, m, "nothing to squash");
        };
        fired("squash");
        self.world
            .jj(m, &["squash", "-r", &commit, "--use-destination-message"]);
        self.note(&tc);
    }

    /// Squashes one commit's work into another, which another machine may be squashing
    /// into too.
    #[rule]
    fn squash_into(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mutable = self.world.observe(m).mutable();
        if mutable.len() < 2 {
            return self.found_nothing(&tc, m, "no two commits to squash one into the other");
        }
        let into = draw_from(&tc, "into", mutable.clone());
        let from = draw_from(
            &tc,
            "from",
            mutable.into_iter().filter(|c| *c != into).collect(),
        );
        fired("squash_into");
        self.world.jj(
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
        self.note(&tc);
    }

    #[rule]
    fn abandon(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let Some(commit) = choose(&tc, "commit", self.world.observe(m).mutable()) else {
            return self.found_nothing(&tc, m, "nothing to abandon");
        };
        fired("abandon");
        self.world.jj(m, &["abandon", &commit]);
        self.note(&tc);
    }

    /// Resolves a conflicted commit (rebases of shared files make them), taking one side.
    #[rule]
    fn resolve(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let Some(commit) = choose(&tc, "commit", self.world.observe(m).conflicted()) else {
            return self.found_nothing(&tc, m, "no conflict to resolve");
        };
        let tool = tc.draw(gs::sampled_from(vec![":ours", ":theirs"]));
        // jj's built-in tools resolve only conflicts of two sides, and jj refuses others, as
        // a merge of three machines' work can make.
        let resolved = self.world.try_jj_in(
            m,
            0,
            &["resolve", "-r", &commit, "--tool", tool],
            &["At most 2 sides are supported"],
        );
        if resolved.is_ok() {
            fired("resolve");
        }
        self.note(&tc);
    }

    /// Abandons another machine's working-copy commit.
    #[rule]
    fn abandon_other_wc(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let Some(commit) = choose(&tc, "commit", self.world.observe(m).other_working_copies())
        else {
            return self.found_nothing(&tc, m, "no other machine's working copy to abandon");
        };
        fired("abandon_other_wc");
        self.world.jj(m, &["abandon", &commit]);
        self.note(&tc);
    }

    /// Rewrites a commit under another machine's working copy, which that machine must
    /// follow, possibly with edits it has not snapshotted.
    #[rule(weight = 2)]
    fn rewrite_under_other_wc(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let view = self.world.observe(m);
        let Some(commit) = choose(&tc, "commit", view.under_other_working_copies()) else {
            return self.found_nothing(
                &tc,
                m,
                "nothing under another machine's working copy to rewrite",
            );
        };
        let destinations = view.rebase_source_destinations(&commit);
        let mut rewrites = vec![Rewrite::Describe];
        if !destinations.is_empty() {
            rewrites.push(Rewrite::Rebase);
        }
        let rewrite = tc.draw(gs::sampled_from(rewrites));
        fired("rewrite_under_other_wc");
        match rewrite {
            Rewrite::Describe => {
                let message = self.world.message(m);
                self.world.jj(m, &["describe", &commit, "-m", &message]);
            }
            Rewrite::Rebase => {
                let onto = draw_from(&tc, "onto", destinations);
                self.world.jj(m, &["rebase", "-s", &commit, "-o", &onto]);
            }
        }
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn bookmark_create(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let view = self.world.observe(m);
        let free = self.world.free_bookmark_names(m, &view);
        let targets = view.targets();
        if free.is_empty() || targets.is_empty() {
            return self.found_nothing(&tc, m, "no free bookmark name, or nothing to create it on");
        }
        let name = draw_from(&tc, "name", free);
        let target = draw_from(&tc, "target", targets);
        fired("bookmark_create");
        // A tracked remote bookmark on a hidden commit is not in the view.
        let _refused = self.world.try_jj_in(
            m,
            0,
            &["bookmark", "create", &name, "-r", &target],
            &["Tracked remote bookmarks exist"],
        );
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn bookmark_move(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let view = self.world.observe(m);
        let bookmarks = view.bookmarks();
        let targets = view.targets();
        if bookmarks.is_empty() || targets.is_empty() {
            return self.found_nothing(&tc, m, "no bookmark to move, or nothing to move it to");
        }
        let bookmark = draw_from(&tc, "bookmark", bookmarks);
        let target = draw_from(&tc, "target", targets);
        fired("bookmark_move");
        self.world.jj(
            m,
            &[
                "bookmark",
                "move",
                &bookmark,
                "--to",
                &target,
                "--allow-backwards",
            ],
        );
        self.note(&tc);
    }

    #[rule]
    fn bookmark_delete(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let Some(bookmark) = choose(&tc, "bookmark", self.world.observe(m).bookmarks()) else {
            return self.found_nothing(&tc, m, "no bookmark to delete");
        };
        fired("bookmark_delete");
        self.world.jj(m, &["bookmark", "delete", &bookmark]);
        self.note(&tc);
    }

    #[rule]
    fn bookmark_set(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let name = tc.draw(gs::sampled_from(&BOOKMARKS[..]));
        let Some(target) = choose(&tc, "target", self.world.observe(m).targets()) else {
            return self.found_nothing(&tc, m, "nothing to set the bookmark to");
        };
        fired("bookmark_set");
        self.world.jj(
            m,
            &["bookmark", "set", name, "-r", &target, "--allow-backwards"],
        );
        self.note(&tc);
    }

    #[rule]
    fn tag_set(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let name = tc.draw(gs::sampled_from(&TAGS[..]));
        let Some(target) = choose(&tc, "target", self.world.observe(m).targets()) else {
            return self.found_nothing(&tc, m, "nothing to tag");
        };
        fired("tag_set");
        self.world
            .jj(m, &["tag", "set", name, "-r", &target, "--allow-move"]);
        self.note(&tc);
    }

    #[rule]
    fn tag_delete(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let Some(tag) = choose(&tc, "tag", self.world.observe(m).tags()) else {
            return self.found_nothing(&tc, m, "no tag to delete");
        };
        fired("tag_delete");
        self.world.jj(m, &["tag", "delete", &tag]);
        self.note(&tc);
    }

    #[rule]
    fn undo(&mut self, tc: TestCase) {
        tc.assume(self.undos < MAX_UNDOS);
        let m = self.machine_where(&tc, |world, m| world.can_undo(m));
        self.undos += 1;
        fired("undo");
        self.world.undo(m);
        self.note(&tc);
    }

    /// A command based at an older operation, as a long-running command or `--at-op`
    /// produces: a concurrent operation on one machine.
    #[rule(weight = 2)]
    fn at_op(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let ops = self.world.older_ops(m);
        let Some(op) = choose_op(&tc, ops) else {
            return self.found_nothing(&tc, m, "no older operation to run a command at");
        };
        let view = self.world.view_at(m, &op);
        let mutable = view.mutable();
        let bases = view.bases();
        let targets = view.targets();
        let commands: Vec<AtOpCommand> = [
            (AtOpCommand::Describe, !mutable.is_empty()),
            (AtOpCommand::Abandon, !mutable.is_empty()),
            (AtOpCommand::New, !bases.is_empty()),
            (AtOpCommand::BookmarkSet, !targets.is_empty()),
        ]
        .into_iter()
        .filter_map(|(command, possible)| possible.then_some(command))
        .collect();
        if commands.is_empty() {
            return self.found_nothing(&tc, m, "nothing to do at that operation");
        }
        let command = tc.draw(gs::sampled_from(commands));
        let args: Vec<String> = match command {
            AtOpCommand::Describe => {
                let commit = draw_from(&tc, "commit", mutable);
                let message = self.world.message(m);
                vec!["describe".into(), commit, "-m".into(), message]
            }
            AtOpCommand::Abandon => vec!["abandon".into(), draw_from(&tc, "commit", mutable)],
            AtOpCommand::New => vec!["new".into(), draw_from(&tc, "parent", bases)],
            AtOpCommand::BookmarkSet => {
                let name = tc.draw(gs::sampled_from(&BOOKMARKS[..]));
                let target = draw_from(&tc, "target", targets);
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
        self.world.jj_at_op(m, &op, &strs(&args));
        self.note(&tc);
    }

    /// `jj op abandon` of an operation since setup, below the head and not a merge (which jj
    /// refuses to abandon): every machine drops it, and the repository stays as it was at each
    /// operation left. Once every copy the hive shows has taken it, the hub prunes its record.
    #[rule]
    fn op_abandon(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let ops = self.world.abandonable_ops(m);
        let Some(op) = choose_op(&tc, ops) else {
            return self.found_nothing(&tc, m, "no operation it can abandon");
        };
        fired("op_abandon");
        self.world.op_abandon(m, &op);
        self.note(&tc);
    }

    /// Trim below a push the hub accepted before its publisher advanced the saved base.
    /// This includes the joins, which the single-operation rule deliberately leaves alone.
    #[rule]
    fn trim_below_accepted_push(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        fired("trim_below_accepted_push");
        self.world.trim_below_accepted_push(m);
        self.note(&tc);
    }

    /// A full trim removes an accepted forget beneath new unpublished work.
    #[rule]
    fn trim_below_accepted_forget(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let other = self.other_than(&tc, m);
        fired("trim_below_accepted_forget");
        self.world.trim_below_accepted_forget(m, other);
        self.note(&tc);
    }

    /// Any `jj` command: snapshots, imports git refs, merges concurrent operations, and,
    /// with auto-update-stale as the tests set it, updates a stale working copy.
    #[rule]
    fn status(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        fired("status");
        self.world.jj(m, &["status"]);
        self.note(&tc);
    }

    // Workspaces: per machine; other machines only ever see their commits.

    #[rule]
    fn workspace_add(&mut self, tc: TestCase) {
        let m = self.machine_where(&tc, |world, m| world.workspaces[m].len() < 3);
        let name = require(&tc, "name", self.world.free_workspace_names(m));
        fired("workspace_add");
        self.world.add_workspace(m, &name);
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn workspace_commit(&mut self, tc: TestCase) {
        let (m, ws) = self.secondary(&tc);
        let file = draw_file(&tc);
        fired("workspace_commit");
        self.world.commit(m, ws, file);
        self.note(&tc);
    }

    #[rule]
    fn workspace_rename(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let workspaces = &self.world.workspaces[m];
        let ws = draw_named_index(
            &tc,
            "workspace",
            workspaces
                .iter()
                .enumerate()
                .map(|(ws, workspace)| (ws, workspace.name.clone())),
        );
        let name = require(&tc, "name", self.world.free_workspace_names(m));
        fired("workspace_rename");
        self.world.rename_workspace(m, ws, &name);
        self.note(&tc);
    }

    #[rule]
    fn workspace_forget(&mut self, tc: TestCase) {
        let (m, ws) = self.secondary(&tc);
        fired("workspace_forget");
        self.world.forget_workspace(m, ws);
        self.note(&tc);
    }

    /// Tries to forget a workspace that only another machine has: jj warns that there is
    /// no such workspace, and nothing changes.
    #[rule]
    fn forget_other_workspace(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let name = require(&tc, "workspace", self.world.foreign_workspace_names(m));
        fired("forget_other_workspace");
        self.world.jj(m, &["workspace", "forget", &name]);
        self.note(&tc);
    }

    /// Forgets another machine's copy, as `musubi forget` does: every machine stops showing
    /// it until that machine's next work.
    #[rule]
    fn forget_copy(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let other = self.other_than(&tc, m);
        fired("forget_copy");
        self.world.forget_copy(m, other);
        self.note(&tc);
    }

    /// A copy goes offline, and a machine still in the hive forgets it, then runs `jj op
    /// abandon`, and the rest of the hive syncs, twice, taking the abandon: the hub prunes its
    /// record, which the forgotten copy never took. A sequence rarely does all that by itself.
    #[rule]
    fn abandon_while_forgotten(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let other = self.other_than(&tc, m);
        let ops = self.world.abandonable_ops(m);
        let Some(op) = choose_op(&tc, ops) else {
            return self.found_nothing(&tc, m, "no operation it can abandon");
        };
        fired("abandon_while_forgotten");
        self.world.forget_copy(m, other);
        self.world.op_abandon(m, &op);
        for _ in 0..2 {
            for x in (0..self.world.nodes()).filter(|&x| x != other) {
                self.world.sync(x);
            }
        }
        self.note(&tc);
    }

    /// Another machine joins, with a new copy made by `musubi clone`.
    #[rule]
    fn join(&mut self, tc: TestCase) {
        let m = self.world.nodes();
        tc.assume(m < SEARCH_MACHINES);
        fired("join");
        self.world.clone_copy(m);
        self.note(&tc);
    }

    /// Sets this copy's `musubi.forget-after`, as `musubi join` does, to an hour or never,
    /// and records it, as the daemon does.
    #[rule]
    fn set_forget_after(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let value = tc.draw(gs::sampled_from(vec!["1h", "never"]));
        fired("set_forget_after");
        self.world.set_forget_after(m, value);
        self.note(&tc);
    }

    /// A daemon, two hours on, forgets the other copies unused for longer than their
    /// `musubi.forget-after`.
    #[rule]
    fn expire_idle(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        fired("expire_idle");
        self.world.expire_idle(m);
        self.note(&tc);
    }

    // The shared remote.

    /// Someone outside the hive pushes to origin's `main`.
    #[rule]
    fn origin_advance(&mut self, tc: TestCase) {
        fired("origin_advance");
        let message = self.world.origin.advance();
        self.world.record(format!("origin: push {message}"));
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn fetch(&mut self, tc: TestCase) {
        let m = self.machine_where(&tc, |world, m| world.has_origin(m));
        fired("fetch");
        self.world.jj(m, &["git", "fetch"]);
        self.note(&tc);
    }

    #[rule]
    fn push(&mut self, tc: TestCase) {
        let m = self.machine_where(&tc, |world, m| world.has_origin(m));
        let Some(bookmark) = choose(&tc, "bookmark", self.world.observe(m).pushable_bookmarks())
        else {
            return self.found_nothing(&tc, m, "no bookmark it can push");
        };
        fired("push");
        let pushed = self.world.try_jj_in(
            m,
            0,
            &["git", "push", "--bookmark", &bookmark],
            PUSH_REFUSALS,
        );
        if pushed.is_ok() {
            fired("push:accepted");
        }
        self.note(&tc);
    }

    // Git-side work in the colocated repository, which jj imports on its next command.

    #[rule(weight = 2)]
    fn git_set_branch(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        // Read-only: it neither snapshots, imports nor merges.
        let view = self.world.view_at_head(m);
        let targets = view.targets();
        tc.assume(!targets.is_empty());
        let name = tc.draw(gs::sampled_from(&BOOKMARKS[..]));
        let target = draw_from(&tc, "target", targets);
        let target = view
            .commits
            .iter()
            .find(|c| c.id == target)
            .expect("a drawn target is visible");
        fired("git_set_branch");
        self.world.move_git_branch(m, name, target);
        self.note(&tc);
    }

    #[rule]
    fn git_delete_branch(&mut self, tc: TestCase) {
        let m = self.machine_where(&tc, |world, m| !world.git_branches(m).is_empty());
        let branch = draw_from(&tc, "branch", self.world.git_branches(m));
        fired("git_delete_branch");
        self.world.delete_git_branch(m, &branch);
        self.note(&tc);
    }

    // Sync: one node at a time, so machines see each other's work partially.

    #[rule(weight = 5)]
    fn sync(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        fired("sync");
        self.world.sync(m);
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn sync_partial(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let steps = tc.draw(gs::integers::<usize>().min_value(1).max_value(4));
        fired("sync_partial");
        self.world.sync_partial(m, steps, None);
        self.note(&tc);
    }

    /// Full convergence in the middle of a sequence, with every property checked; the
    /// ledger starts afresh.
    #[rule]
    fn converge(&mut self, tc: TestCase) {
        tc.assume(self.converges < MAX_CONVERGES);
        self.converges += 1;
        fired("converge");
        self.world.converge();
        self.note(&tc);
    }

    // Faults.

    #[rule]
    fn restart(&mut self, tc: TestCase) {
        self.may_fault(&tc);
        let m = self.machine(&tc);
        self.fault("restart");
        self.world.restart(m);
        self.note(&tc);
    }

    #[rule]
    fn crash(&mut self, tc: TestCase) {
        self.may_fault(&tc);
        let m = self.machine(&tc);
        self.fault("crash");
        let stopped = tc.draw(gs::integers::<u64>());
        if self.world.crash(m, false, stopped) > 0 {
            fired("crash:writes_in_flight");
        }
        self.note(&tc);
    }

    /// A crash partway through realizing what a sync fetched, with realizations still being
    /// written.
    #[rule]
    fn crash_while_syncing(&mut self, tc: TestCase) {
        self.may_fault(&tc);
        // Only a machine with something to realize can crash while writing it.
        let m = self.machine_where(&tc, |world, m| world.behind_hub(m));
        self.fault("crash_while_syncing");
        let count = tc.draw(gs::integers::<usize>().min_value(1).max_value(4));
        let stopped = tc.draw(gs::integers::<u64>());
        self.world.sync_realizing(m, count);
        if self.world.crash(m, false, stopped) > 0 {
            fired("crash:writes_in_flight");
        }
        self.note(&tc);
    }

    #[rule]
    fn lose_cache(&mut self, tc: TestCase) {
        self.may_fault(&tc);
        let m = self.machine(&tc);
        self.fault("lose_cache");
        let stopped = tc.draw(gs::integers::<u64>());
        if self.world.crash(m, true, stopped) > 0 {
            fired("crash:writes_in_flight");
        }
        self.note(&tc);
    }

    #[rule]
    fn restart_hub(&mut self, tc: TestCase) {
        self.may_fault(&tc);
        self.fault("restart_hub");
        self.world.restart_hub();
        self.note(&tc);
    }

    /// A power cut on the hub's machine: it loses the last heads it accepted, and comes back
    /// at an older one.
    #[rule]
    fn hub_goes_back(&mut self, tc: TestCase) {
        self.may_fault(&tc);
        tc.assume(self.world.hub_can_go_back());
        self.fault("hub_goes_back");
        let lost = tc.draw(gs::integers::<usize>().min_value(1).max_value(3));
        self.world.hub_goes_back(lost);
        self.note(&tc);
    }

    /// A power cut on the hub's machine just after it pruned its records: it loses the
    /// `heads` log it wrote pruning, and everything after, and comes back with the one before.
    #[rule]
    fn hub_loses_prune(&mut self, tc: TestCase) {
        self.may_fault(&tc);
        tc.assume(self.world.hub_pruned_since_restart());
        self.fault("hub_loses_prune");
        self.world.hub_loses_prune();
        self.note(&tc);
    }

    /// The hub finds its store corrupt, as a power cut can leave it, and makes the hive
    /// again, empty.
    #[rule]
    fn remake_hub(&mut self, tc: TestCase) {
        self.may_fault(&tc);
        self.fault("remake_hub");
        self.world.remake_hub();
        self.note(&tc);
    }

    /// An hour passes on the hub: it stops waiting, before pruning, for machines that may have
    /// been joining when it opened its store, as after `restart_hub`.
    #[rule]
    fn an_hour_passes(&mut self, tc: TestCase) {
        fired("an_hour_passes");
        self.world.an_hour_passes();
        self.note(&tc);
    }

    /// A sync in which the reply to one request is lost after the hub handled it.
    #[rule]
    fn lose_reply(&mut self, tc: TestCase) {
        self.may_fault(&tc);
        let m = self.machine(&tc);
        self.fault("lose_reply");
        let steps = tc.draw(gs::integers::<usize>().min_value(1).max_value(4));
        let lost = tc.draw(gs::integers::<usize>().max_value(4));
        self.world.sync_partial(m, steps, Some(lost));
        self.note(&tc);
    }

    #[invariant(always_run)]
    fn repositories_load(&mut self, _: TestCase) {
        self.world.check_loads();
    }

    /// Every import of git refs or of git's HEAD follows a git move, or does as jj does in one
    /// repository (`imports`).
    #[invariant(always_run)]
    fn no_spurious_revert(&mut self, _: TestCase) {
        for m in 0..self.world.nodes() {
            self.world.check_imports(m);
        }
    }
}
