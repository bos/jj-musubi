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
//! machine, file or workspace by name, a commit or operation by id, a choice by its variant.
//! Each step notes the trace entries it added.

use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

use hegel::TestCase;
use hegel::generators as gs;

use crate::coverage::fired;
use crate::world::BOOKMARKS;
use crate::world::FILES;
use crate::world::MACHINES;
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

pub struct Search {
    world: Rc<RefCell<World>>,
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

impl Search {
    /// The search over `world`, whose trace so far is the setup's.
    pub fn new(world: Rc<RefCell<World>>) -> Self {
        let noted = world.borrow().trace.len();
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
        let world = self.world.borrow();
        let machines = (0..world.nodes())
            .filter(|&m| eligible(&world, m))
            .collect();
        drop(world);
        draw_machine(tc, "machine", machines)
    }

    /// A machine other than `m`.
    fn other_than(&self, tc: &TestCase, m: usize) -> usize {
        let nodes = self.world.borrow().nodes();
        draw_machine(tc, "other", (0..nodes).filter(|&o| o != m).collect())
    }

    /// A machine with a secondary workspace, and that workspace.
    fn secondary(&self, tc: &TestCase) -> (usize, usize) {
        let m = self.machine_where(tc, |world, m| world.workspaces[m].len() > 1);
        let world = self.world.borrow();
        let workspaces = &world.workspaces[m];
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
        let world = self.world.borrow();
        for entry in &world.trace[self.noted..] {
            tc.note(entry);
        }
        self.noted = world.trace.len();
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
impl Search {
    // Local work, through the jj CLI.

    #[rule(weight = 4)]
    fn commit(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let file = draw_file(&tc);
        fired("commit");
        self.world.borrow_mut().commit(m, 0, file);
        self.note(&tc);
    }

    #[rule]
    fn edit_unsnapshotted(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let file = draw_file(&tc);
        fired("edit_unsnapshotted");
        self.world.borrow_mut().edit(m, file);
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn describe(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let Some(commit) = choose(&tc, "commit", world.observe(m).mutable()) else {
            drop(world);
            return self.found_nothing(&tc, m, "nothing to describe");
        };
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
        let Some(parent) = choose(&tc, "parent", world.observe(m).bases()) else {
            drop(world);
            return self.found_nothing(&tc, m, "nothing to make a commit on");
        };
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
        let firsts = view
            .bases()
            .into_iter()
            .filter(|first| !view.unrelated(first).is_empty())
            .collect();
        let Some(first) = choose(&tc, "first", firsts) else {
            drop(world);
            return self.found_nothing(&tc, m, "no two unrelated commits to merge");
        };
        let second = draw_from(&tc, "second", view.unrelated(&first));
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
        let revisions = view
            .mutable()
            .into_iter()
            .filter(|revision| !view.rebase_revision_destinations(revision).is_empty())
            .collect();
        let Some(revision) = choose(&tc, "revision", revisions) else {
            drop(world);
            return self.found_nothing(&tc, m, "nothing to rebase");
        };
        let onto = draw_from(&tc, "onto", view.rebase_revision_destinations(&revision));
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
        let sources = view
            .mutable()
            .into_iter()
            .filter(|source| !view.rebase_source_destinations(source).is_empty())
            .collect();
        let Some(source) = choose(&tc, "source", sources) else {
            drop(world);
            return self.found_nothing(&tc, m, "nothing to rebase");
        };
        let onto = draw_from(&tc, "onto", view.rebase_source_destinations(&source));
        fired("rebase_source");
        world.jj(m, &["rebase", "-s", &source, "-o", &onto]);
        drop(world);
        self.note(&tc);
    }

    #[rule]
    fn squash(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let Some(commit) = choose(&tc, "commit", world.observe(m).squashable()) else {
            drop(world);
            return self.found_nothing(&tc, m, "nothing to squash");
        };
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
        let mutable = world.observe(m).mutable();
        if mutable.len() < 2 {
            drop(world);
            return self.found_nothing(&tc, m, "no two commits to squash one into the other");
        }
        let into = draw_from(&tc, "into", mutable.clone());
        let from = draw_from(
            &tc,
            "from",
            mutable.into_iter().filter(|c| *c != into).collect(),
        );
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
        let Some(commit) = choose(&tc, "commit", world.observe(m).mutable()) else {
            drop(world);
            return self.found_nothing(&tc, m, "nothing to abandon");
        };
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
        let Some(commit) = choose(&tc, "commit", world.observe(m).conflicted()) else {
            drop(world);
            return self.found_nothing(&tc, m, "no conflict to resolve");
        };
        let tool = tc.draw(gs::sampled_from(vec![":ours", ":theirs"]));
        // jj's built-in tools resolve only conflicts of two sides, and jj refuses others, as
        // a merge of three machines' work can make.
        let resolved = world.try_jj_in(
            m,
            0,
            &["resolve", "-r", &commit, "--tool", tool],
            &["At most 2 sides are supported"],
        );
        if resolved.is_ok() {
            fired("resolve");
        }
        drop(world);
        self.note(&tc);
    }

    /// Abandons another machine's working-copy commit.
    #[rule]
    fn abandon_other_wc(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let Some(commit) = choose(&tc, "commit", world.observe(m).other_working_copies()) else {
            drop(world);
            return self.found_nothing(&tc, m, "no other machine's working copy to abandon");
        };
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
        let Some(commit) = choose(&tc, "commit", view.under_other_working_copies()) else {
            drop(world);
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
                let message = world.message(m);
                world.jj(m, &["describe", &commit, "-m", &message]);
            }
            Rewrite::Rebase => {
                let onto = draw_from(&tc, "onto", destinations);
                world.jj(m, &["rebase", "-s", &commit, "-o", &onto]);
            }
        }
        drop(world);
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn bookmark_create(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let view = world.observe(m);
        // Not only the view's bookmarks: a conflicted bookmark can have no side that is a
        // commit, which `jj log` never shows but `jj bookmark create` refuses. jj makes one
        // where a conflict is resolved and deleted concurrently: from `main` at {A, B, C},
        // moving it to A on one machine and deleting it on another leaves {-B, -C} and
        // absent sides, as plain jj does for the same two operations in one repository.
        // `observe` has just snapshotted and imported, so the list needn't again.
        let existing = world.raw_jj(
            m,
            &[
                "--ignore-working-copy",
                "bookmark",
                "list",
                "-T",
                r#"if(!remote && present, name ++ "\n")"#,
            ],
        );
        let existing: Vec<&str> = existing.lines().collect();
        let remote = view.remote_names();
        let free: Vec<String> = BOOKMARKS
            .iter()
            .map(|b| (*b).to_owned())
            .filter(|b| !existing.contains(&b.as_str()) && !remote.contains(b))
            .collect();
        let targets = view.targets();
        if free.is_empty() || targets.is_empty() {
            drop(world);
            return self.found_nothing(&tc, m, "no free bookmark name, or nothing to create it on");
        }
        let name = draw_from(&tc, "name", free);
        let target = draw_from(&tc, "target", targets);
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
        let bookmarks = view.bookmarks();
        let targets = view.targets();
        if bookmarks.is_empty() || targets.is_empty() {
            drop(world);
            return self.found_nothing(&tc, m, "no bookmark to move, or nothing to move it to");
        }
        let bookmark = draw_from(&tc, "bookmark", bookmarks);
        let target = draw_from(&tc, "target", targets);
        fired("bookmark_move");
        world.jj(
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
        drop(world);
        self.note(&tc);
    }

    #[rule]
    fn bookmark_delete(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let Some(bookmark) = choose(&tc, "bookmark", world.observe(m).bookmarks()) else {
            drop(world);
            return self.found_nothing(&tc, m, "no bookmark to delete");
        };
        fired("bookmark_delete");
        world.jj(m, &["bookmark", "delete", &bookmark]);
        drop(world);
        self.note(&tc);
    }

    #[rule]
    fn bookmark_set(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let name = tc.draw(gs::sampled_from(&BOOKMARKS[..]));
        let mut world = self.world.borrow_mut();
        let Some(target) = choose(&tc, "target", world.observe(m).targets()) else {
            drop(world);
            return self.found_nothing(&tc, m, "nothing to set the bookmark to");
        };
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
        let name = tc.draw(gs::sampled_from(&TAGS[..]));
        let mut world = self.world.borrow_mut();
        let Some(target) = choose(&tc, "target", world.observe(m).targets()) else {
            drop(world);
            return self.found_nothing(&tc, m, "nothing to tag");
        };
        fired("tag_set");
        world.jj(m, &["tag", "set", name, "-r", &target, "--allow-move"]);
        drop(world);
        self.note(&tc);
    }

    #[rule]
    fn tag_delete(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let Some(tag) = choose(&tc, "tag", world.observe(m).tags()) else {
            drop(world);
            return self.found_nothing(&tc, m, "no tag to delete");
        };
        fired("tag_delete");
        world.jj(m, &["tag", "delete", &tag]);
        drop(world);
        self.note(&tc);
    }

    #[rule]
    fn undo(&mut self, tc: TestCase) {
        tc.assume(self.undos < MAX_UNDOS);
        let m = self.machine_where(&tc, |world, m| world.can_undo(m));
        let mut world = self.world.borrow_mut();
        self.undos += 1;
        fired("undo");
        // jj refuses to undo another workspace's operation unless told to, and another
        // machine's operations are another workspace's even when the names match. jj
        // undoes the latest operation when it runs, which can be one it wrote itself first
        // (importing git HEAD, say), so check the operation it actually undid.
        let ws = world.workspaces[m][0].name.clone();
        let own = |made_in: &str| {
            let made_in = made_in.trim_end_matches('@').trim_matches('"');
            made_in.is_empty() || made_in == ws
        };
        let latest = world.head_op_workspace(m);
        let refusal = "Refusing to undo operation";
        match world.try_jj_in(m, 0, &["undo"], &[refusal]) {
            Ok(_) => {
                if let Some(undone) = world.undone_workspace(m)
                    && !own(&undone)
                {
                    world.fail(&format!("`jj undo` undid an operation made in {undone}"));
                }
            }
            Err(_) if own(&latest) => {
                world.fail("`jj undo` refused this workspace's own operation");
            }
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
        let Some(op) = choose(&tc, "op", ops) else {
            drop(world);
            return self.found_nothing(&tc, m, "no older operation to run a command at");
        };
        let view = world.view_at(m, &op);
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
            drop(world);
            return self.found_nothing(&tc, m, "nothing to do at that operation");
        }
        let command = tc.draw(gs::sampled_from(commands));
        let args: Vec<String> = match command {
            AtOpCommand::Describe => {
                let commit = draw_from(&tc, "commit", mutable);
                let message = world.message(m);
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
        world.jj_at_op(m, &op, &strs(&args));
        drop(world);
        self.note(&tc);
    }

    /// `jj op abandon` of an operation since setup, below the head and not a merge (which jj
    /// refuses to abandon): every machine drops it, and the repository stays as it was at each
    /// operation left. Once every copy the hive shows has taken it, the hub prunes its record.
    #[rule]
    fn op_abandon(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let ops = world.abandonable_ops(m);
        let Some(op) = choose(&tc, "op", ops) else {
            drop(world);
            return self.found_nothing(&tc, m, "no operation it can abandon");
        };
        fired("op_abandon");
        world.op_abandon(m, &op);
        drop(world);
        self.note(&tc);
    }

    /// Trim below a push the hub accepted before its publisher advanced the saved base.
    /// This includes the joins, which the single-operation rule deliberately leaves alone.
    #[rule]
    fn trim_below_accepted_push(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        fired("trim_below_accepted_push");
        self.world.borrow_mut().trim_below_accepted_push(m);
        self.note(&tc);
    }

    /// A full trim removes an accepted forget beneath new unpublished work.
    #[rule]
    fn trim_below_accepted_forget(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let other = self.other_than(&tc, m);
        fired("trim_below_accepted_forget");
        self.world.borrow_mut().trim_below_accepted_forget(m, other);
        self.note(&tc);
    }

    /// Any `jj` command: snapshots, imports git refs, merges concurrent operations, and,
    /// with auto-update-stale as the tests set it, updates a stale working copy.
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
        let m = self.machine_where(&tc, |world, m| world.workspaces[m].len() < 3);
        let mut world = self.world.borrow_mut();
        let name = require(&tc, "name", world.free_workspace_names(m));
        fired("workspace_add");
        world.add_workspace(m, &name);
        drop(world);
        self.note(&tc);
    }

    #[rule(weight = 2)]
    fn workspace_commit(&mut self, tc: TestCase) {
        let (m, ws) = self.secondary(&tc);
        let file = draw_file(&tc);
        fired("workspace_commit");
        self.world.borrow_mut().commit(m, ws, file);
        self.note(&tc);
    }

    #[rule]
    fn workspace_rename(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut world = self.world.borrow_mut();
        let workspaces = &world.workspaces[m];
        let ws = draw_named_index(
            &tc,
            "workspace",
            workspaces
                .iter()
                .enumerate()
                .map(|(ws, workspace)| (ws, workspace.name.clone())),
        );
        let name = require(&tc, "name", world.free_workspace_names(m));
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
        let name = require(&tc, "workspace", world.foreign_workspace_names(m));
        fired("forget_other_workspace");
        world.jj(m, &["workspace", "forget", &name]);
        drop(world);
        self.note(&tc);
    }

    /// Forgets another machine's copy, as `musubi forget` does: every machine stops showing
    /// it until that machine's next work.
    #[rule]
    fn forget_copy(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let other = self.other_than(&tc, m);
        fired("forget_copy");
        self.world.borrow_mut().forget_copy(m, other);
        self.note(&tc);
    }

    /// A copy goes offline, and a machine still in the hive forgets it, then runs `jj op
    /// abandon`, and the rest of the hive syncs, twice, taking the abandon: the hub prunes its
    /// record, which the forgotten copy never took. A sequence rarely does all that by itself.
    #[rule]
    fn abandon_while_forgotten(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let other = self.other_than(&tc, m);
        let mut world = self.world.borrow_mut();
        let ops = world.abandonable_ops(m);
        let Some(op) = choose(&tc, "op", ops) else {
            drop(world);
            return self.found_nothing(&tc, m, "no operation it can abandon");
        };
        fired("abandon_while_forgotten");
        world.forget_copy(m, other);
        world.op_abandon(m, &op);
        for _ in 0..2 {
            for x in (0..world.nodes()).filter(|&x| x != other) {
                world.sync(x);
            }
        }
        drop(world);
        self.note(&tc);
    }

    /// Another machine joins, with a new copy made by `musubi clone`.
    #[rule]
    fn join(&mut self, tc: TestCase) {
        let mut world = self.world.borrow_mut();
        let m = world.nodes();
        tc.assume(m < SEARCH_MACHINES);
        fired("join");
        world.clone_copy(m);
        drop(world);
        self.note(&tc);
    }

    /// Sets this copy's `musubi.forget-after`, as `musubi join` does, to an hour or never,
    /// and records it, as the daemon does.
    #[rule]
    fn set_forget_after(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        let value = tc.draw(gs::sampled_from(vec!["1h", "never"]));
        fired("set_forget_after");
        self.world.borrow_mut().set_forget_after(m, value);
        self.note(&tc);
    }

    /// A daemon, two hours on, forgets the other copies unused for longer than their
    /// `musubi.forget-after`.
    #[rule]
    fn expire_idle(&mut self, tc: TestCase) {
        let m = self.machine(&tc);
        fired("expire_idle");
        self.world.borrow_mut().expire_idle(m);
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
        let m = self.machine_where(&tc, |world, m| world.has_origin(m));
        fired("fetch");
        self.world.borrow_mut().jj(m, &["git", "fetch"]);
        self.note(&tc);
    }

    #[rule]
    fn push(&mut self, tc: TestCase) {
        let m = self.machine_where(&tc, |world, m| world.has_origin(m));
        let mut world = self.world.borrow_mut();
        let Some(bookmark) = choose(&tc, "bookmark", world.observe(m).pushable_bookmarks()) else {
            drop(world);
            return self.found_nothing(&tc, m, "no bookmark it can push");
        };
        fired("push");
        let pushed = world.try_jj_in(
            m,
            0,
            &["git", "push", "--bookmark", &bookmark],
            PUSH_REFUSALS,
        );
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
        let mut world = self.world.borrow_mut();
        // Read-only: it neither snapshots, imports nor merges.
        let view = world.view_at_head(m);
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
        world.move_git_branch(m, name, target);
        drop(world);
        self.note(&tc);
    }

    #[rule]
    fn git_delete_branch(&mut self, tc: TestCase) {
        let m = self.machine_where(&tc, |world, m| !world.git_branches(m).is_empty());
        let mut world = self.world.borrow_mut();
        let branch = draw_from(&tc, "branch", world.git_branches(m));
        fired("git_delete_branch");
        world.delete_git_branch(m, &branch);
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
        self.may_fault(&tc);
        let m = self.machine(&tc);
        self.fault("restart");
        self.world.borrow_mut().restart(m);
        self.note(&tc);
    }

    #[rule]
    fn crash(&mut self, tc: TestCase) {
        self.may_fault(&tc);
        let m = self.machine(&tc);
        self.fault("crash");
        let stopped = tc.draw(gs::integers::<u64>());
        if self.world.borrow_mut().crash(m, false, stopped) > 0 {
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
        self.world.borrow_mut().sync_realizing(m, count);
        if self.world.borrow_mut().crash(m, false, stopped) > 0 {
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
        if self.world.borrow_mut().crash(m, true, stopped) > 0 {
            fired("crash:writes_in_flight");
        }
        self.note(&tc);
    }

    #[rule]
    fn restart_hub(&mut self, tc: TestCase) {
        self.may_fault(&tc);
        self.fault("restart_hub");
        self.world.borrow_mut().restart_hub();
        self.note(&tc);
    }

    /// A power cut on the hub's machine: it loses the last heads it accepted, and comes back
    /// at an older one.
    #[rule]
    fn hub_goes_back(&mut self, tc: TestCase) {
        self.may_fault(&tc);
        tc.assume(self.world.borrow().hub_can_go_back());
        self.fault("hub_goes_back");
        let lost = tc.draw(gs::integers::<usize>().min_value(1).max_value(3));
        self.world.borrow_mut().hub_goes_back(lost);
        self.note(&tc);
    }

    /// A power cut on the hub's machine just after it pruned its records: it loses the
    /// `heads` log it wrote pruning, and everything after, and comes back with the one before.
    #[rule]
    fn hub_loses_prune(&mut self, tc: TestCase) {
        self.may_fault(&tc);
        tc.assume(self.world.borrow().hub_pruned_since_restart());
        self.fault("hub_loses_prune");
        self.world.borrow_mut().hub_loses_prune();
        self.note(&tc);
    }

    /// The hub finds its store corrupt, as a power cut can leave it, and makes the hive
    /// again, empty.
    #[rule]
    fn remake_hub(&mut self, tc: TestCase) {
        self.may_fault(&tc);
        self.fault("remake_hub");
        self.world.borrow_mut().remake_hub();
        self.note(&tc);
    }

    /// An hour passes on the hub: it stops waiting, before pruning, for machines that may have
    /// been joining when it opened its store, as after `restart_hub`.
    #[rule]
    fn an_hour_passes(&mut self, tc: TestCase) {
        fired("an_hour_passes");
        self.world.borrow_mut().an_hour_passes();
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
        self.world.borrow_mut().sync_partial(m, steps, Some(lost));
        self.note(&tc);
    }

    #[invariant(always_run)]
    fn repositories_load(&mut self, _: TestCase) {
        self.world.borrow_mut().check_loads();
    }

    /// Every import of git refs or of git's HEAD follows a git move, or does as jj does in one
    /// repository (`imports`).
    #[invariant(always_run)]
    fn no_spurious_revert(&mut self, _: TestCase) {
        let mut world = self.world.borrow_mut();
        for m in 0..world.nodes() {
            world.check_imports(m);
        }
    }
}
