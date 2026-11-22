//! Which of the search's rules and events never fired in a test, printed when the test ends
//! (shown with `--no-capture`): a rule that never fires is one the search doesn't exercise.

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::rc::Rc;

/// Every rule of the state machine, and the setup choices, for listing those that never
/// fired.
pub const RULES: &[&str] = &[
    "commit",
    "edit_unsnapshotted",
    "describe",
    "new_commit",
    "new_merge",
    "rebase_revision",
    "rebase_source",
    "squash",
    "squash_into",
    "abandon",
    "resolve",
    "abandon_other_wc",
    "rewrite_under_other_wc",
    "bookmark_create",
    "bookmark_move",
    "bookmark_delete",
    "bookmark_set",
    "tag_set",
    "tag_delete",
    "undo",
    "at_op",
    "op_abandon",
    "abandon_while_forgotten",
    "status",
    "workspace_add",
    "workspace_commit",
    "workspace_rename",
    "workspace_forget",
    "forget_other_workspace",
    "forget_copy",
    "set_forget_after",
    "expire_idle",
    "origin_advance",
    "fetch",
    "push",
    "git_set_branch",
    "git_delete_branch",
    "sync",
    "sync_partial",
    "converge",
    "restart",
    "crash",
    "crash_while_syncing",
    "lose_cache",
    "restart_hub",
    "hub_goes_back",
    "remake_hub",
    "lose_reply",
    "join",
];

/// Events that are not rules: how the hive was set up, and outcomes worth reaching.
pub const EVENTS: &[&str] = &[
    "setup:three_machines",
    "setup:shared_workspace_name",
    "setup:shared_hostname",
    "setup:prejoin",
    "setup:empty",
    "push:accepted",
    "crash:writes_in_flight",
    // Imports of git refs, by what explains each ref they changed (`imports`).
    "import:git_move",
    "import:concurrent_records",
    "import:plain_jj",
    // Imports of git's HEAD, by what explains each.
    "import:head_git_move",
    "import:concurrent_heads",
    "join:with_history",
    "join:fetch_conflict",
];

type Fired = Rc<RefCell<BTreeSet<&'static str>>>;

thread_local! {
    #[cfg_attr(
        any(target_os = "illumos", target_os = "solaris"),
        allow(
            clippy::missing_const_for_thread_local,
            reason = "clippy wrongly reports this on illumos, but only when the \
                      rust-src component is installed, so it's allowed rather than expected"
        )
    )]
    static FIRED: RefCell<Option<Fired>> = const { RefCell::new(None) };
}

/// Notes a rule that passed its precondition, or an observed setup or outcome event, even
/// if a later assumption or check stops the case.
pub fn fired(rule: &'static str) {
    debug_assert!(
        RULES.contains(&rule) || EVENTS.contains(&rule),
        "unlisted rule {rule}"
    );
    FIRED.with(|current| {
        if let Some(fired) = current.borrow().as_ref() {
            fired.borrow_mut().insert(rule);
        }
    });
}

/// One test's rules and events, from `new` until it is dropped, when it prints those that
/// never fired.
pub struct Report {
    name: &'static str,
    fired: Fired,
}

impl Report {
    pub fn new(name: &'static str) -> Self {
        let fired = Fired::default();
        FIRED.with(|current| current.replace(Some(fired.clone())));
        Self { name, fired }
    }
}

impl Drop for Report {
    fn drop(&mut self) {
        FIRED.with(|current| current.take());
        let fired = self.fired.borrow();
        let never: Vec<&str> = RULES
            .iter()
            .chain(EVENTS)
            .copied()
            .filter(|rule| !fired.contains(rule))
            .collect();
        if never.is_empty() {
            eprintln!("{}: every listed rule and event fired", self.name);
        } else {
            eprintln!("{}: never fired: {}", self.name, never.join(", "));
        }
    }
}
