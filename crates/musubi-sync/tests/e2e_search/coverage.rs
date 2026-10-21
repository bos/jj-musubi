//! Which rules the generated sequences fired, and which rows of the race catalogue
//! (docs/races.md) they reached. A rule or row no sequence reaches is a search problem:
//! give it a richer starting state or fix its precondition (docs/testing.md).

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::fs;
use std::path::PathBuf;
use std::sync::Mutex;

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
    "status",
    "workspace_add",
    "workspace_commit",
    "workspace_rename",
    "workspace_forget",
    "forget_other_workspace",
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
    "lose_cache",
    "restart_hub",
    "lose_reply",
];

/// Events that are not rules: how the hive was set up, and outcomes some rows need.
pub const EVENTS: &[&str] = &[
    "setup:three_machines",
    "setup:shared_workspace_name",
    "setup:shared_hostname",
    "setup:prejoin",
    "setup:empty",
    "push:accepted",
];

/// Each catalogue row, by test name, with the rules and events that together exercise it
/// in one sequence (every sequence ends by syncing everything); `None` for rows the search
/// deliberately avoids.
pub const CATALOGUE: &[(&str, Option<&[&str]>)] = &[
    (
        "machines_may_share_a_workspace_name",
        Some(&["setup:shared_workspace_name", "commit"]),
    ),
    (
        "other_machines_workspaces_are_theirs",
        Some(&["forget_other_workspace"]),
    ),
    (
        "forgotten_working_copies_dont_keep_rewritten_parents",
        Some(&["forget_other_workspace", "rebase_revision"]),
    ),
    (
        "forgotten_working_copies_follow_an_abandon_to_the_parent",
        Some(&["forget_other_workspace", "abandon"]),
    ),
    (
        "secondary_workspaces_show_everywhere",
        Some(&["workspace_commit", "workspace_forget"]),
    ),
    (
        "rewriting_under_another_machines_working_copy_is_allowed",
        Some(&["rewrite_under_other_wc"]),
    ),
    (
        "unsnapshotted_edit_survives_a_remote_rebase",
        Some(&["edit_unsnapshotted", "rewrite_under_other_wc"]),
    ),
    (
        "abandoning_another_machines_working_copy_commit",
        Some(&["abandon_other_wc"]),
    ),
    (
        "other_machines_working_copies_follow_rewrites",
        Some(&["rewrite_under_other_wc"]),
    ),
    (
        "renamed_workspace_shows_renamed",
        Some(&["workspace_rename"]),
    ),
    ("git_never_sees_other_machines_working_copies", None),
    (
        "machines_sharing_a_hostname_are_told_apart",
        Some(&["setup:shared_hostname"]),
    ),
    (
        "same_bookmark_moved_to_different_commits",
        Some(&["bookmark_move"]),
    ),
    (
        "same_bookmark_created_at_the_same_commit",
        Some(&["bookmark_create"]),
    ),
    (
        "same_bookmark_deleted_on_both_machines",
        Some(&["bookmark_delete"]),
    ),
    (
        "bookmark_moved_on_one_machine_and_deleted_on_another",
        Some(&["bookmark_move", "bookmark_delete"]),
    ),
    (
        "git_branch_moved_behind_jj_while_another_machine_moves_it",
        Some(&["git_set_branch", "bookmark_move"]),
    ),
    ("same_tag_created_at_different_commits", Some(&["tag_set"])),
    (
        "joining_repositories_with_conflicting_bookmarks",
        Some(&["setup:prejoin"]),
    ),
    ("same_change_rewritten_on_two_machines", Some(&["describe"])),
    (
        "commit_abandoned_while_another_machine_builds_on_it",
        Some(&["abandon", "new_commit", "commit"]),
    ),
    (
        "both_machines_squash_into_the_same_commit",
        Some(&["squash_into"]),
    ),
    ("conflicts_replicate_and_resolve", Some(&["resolve"])),
    (
        "three_machines_build_on_the_same_commit",
        Some(&["setup:three_machines", "new_commit", "describe"]),
    ),
    ("fetch_on_one_machine_reaches_the_other", Some(&["fetch"])),
    (
        "concurrent_fetches_of_a_moving_remote",
        Some(&["fetch", "origin_advance"]),
    ),
    ("push_from_one_machine", Some(&["push:accepted"])),
    ("undo_of_another_machines_operation", Some(&["undo"])),
    ("concurrent_operation_on_one_machine", Some(&["at_op"])),
    ("long_offline_machine_catches_up", Some(&["commit"])),
    ("hub_restart_between_push_and_fetch", Some(&["restart_hub"])),
    ("joining_with_full_history", Some(&["setup:prejoin"])),
    ("empty_repositories_make_a_hive", Some(&["setup:empty"])),
    // A documented refusal: rules never run `jj op abandon`.
    ("op_abandon_pauses_replication", None),
    ("restart_with_lost_cache", Some(&["lose_cache"])),
    (
        "lost_cache_does_not_duplicate_realizations",
        Some(&["lose_cache"]),
    ),
    // A negative control of a design musubi does not use.
    ("verbatim_replication_reverts_bookmarks", None),
];

static FIRED: Mutex<BTreeMap<&'static str, u64>> = Mutex::new(BTreeMap::new());
static ROWS: Mutex<BTreeMap<&'static str, u64>> = Mutex::new(BTreeMap::new());

thread_local! {
    static CASE: RefCell<BTreeSet<&'static str>> = const { RefCell::new(BTreeSet::new()) };
}

/// Counts a rule that passed its precondition, or an event.
pub fn fired(rule: &'static str) {
    debug_assert!(
        RULES.contains(&rule) || EVENTS.contains(&rule),
        "unlisted rule {rule}"
    );
    *FIRED
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .entry(rule)
        .or_default() += 1;
    CASE.with(|case| case.borrow_mut().insert(rule));
}

/// Starts counting a case's rules; the catalogue rows they reach are counted when the
/// returned guard drops, whether the case passes or fails.
pub fn start_case() -> Case {
    CASE.with(|case| case.borrow_mut().clear());
    Case
}

pub struct Case;

impl Drop for Case {
    fn drop(&mut self) {
        end_case();
    }
}

fn end_case() {
    CASE.with(|case| {
        let case = case.borrow();
        let mut rows = ROWS.lock().unwrap_or_else(|e| e.into_inner());
        for (row, needs) in CATALOGUE {
            if let Some(needs) = needs
                && needs.iter().all(|need| case.contains(need))
            {
                *rows.entry(row).or_default() += 1;
            }
        }
    });
}

pub fn dir() -> PathBuf {
    PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("e2e_search")
}

fn render(counts: &BTreeMap<String, u64>) -> String {
    let mut out = String::new();
    let count = |name: &str| counts.get(name).copied().unwrap_or(0);
    writeln!(out, "rules (times fired):").unwrap();
    for rule in RULES.iter().chain(EVENTS) {
        writeln!(out, "  {rule:<28} {}", count(rule)).unwrap();
    }
    writeln!(out, "catalogue rows (sequences reaching them):").unwrap();
    for (row, needs) in CATALOGUE {
        match needs {
            Some(needs) => writeln!(
                out,
                "  {row:<60} {:>5}  via {}",
                count(&format!("row:{row}")),
                needs.join(" + ")
            )
            .unwrap(),
            None => writeln!(out, "  {row:<60}     -  excluded").unwrap(),
        }
    }
    let never: Vec<&str> = RULES
        .iter()
        .chain(EVENTS)
        .copied()
        .filter(|rule| count(rule) == 0)
        .collect();
    let unreached: Vec<&str> = CATALOGUE
        .iter()
        .filter(|(row, needs)| needs.is_some() && count(&format!("row:{row}")) == 0)
        .map(|(row, _)| *row)
        .collect();
    if never.is_empty() {
        writeln!(out, "every rule fired").unwrap();
    } else {
        writeln!(out, "never fired: {}", never.join(", ")).unwrap();
    }
    if unreached.is_empty() {
        writeln!(out, "every catalogue row reached").unwrap();
    } else {
        writeln!(out, "rows never reached: {}", unreached.join(", ")).unwrap();
    }
    out
}

/// Writes this test's counts to `target/tmp/e2e_search/coverage-<test>.txt`, then sums
/// every test's file into `coverage.txt`, and prints both (visible with `--no-capture`).
/// Written on drop, so a failing run still reports what it reached.
pub struct Report(pub &'static str);

impl Drop for Report {
    fn drop(&mut self) {
        let mut counts: BTreeMap<String, u64> = FIRED
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .iter()
            .map(|(k, v)| ((*k).to_owned(), *v))
            .collect();
        for (row, n) in ROWS.lock().unwrap_or_else(|e| e.into_inner()).iter() {
            counts.insert(format!("row:{row}"), *n);
        }
        let dir = dir();
        if fs::create_dir_all(&dir).is_err() {
            return;
        }
        let mut raw = String::new();
        for (key, n) in &counts {
            writeln!(raw, "{key} {n}").unwrap();
        }
        fs::write(dir.join(format!("counts-{}.txt", self.0)), raw).ok();
        eprintln!("coverage of {}:\n{}", self.0, render(&counts));

        let mut total: BTreeMap<String, u64> = BTreeMap::new();
        let mut sources = vec![];
        for entry in fs::read_dir(&dir).into_iter().flatten().flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            let Some(test) = name
                .strip_prefix("counts-")
                .and_then(|n| n.strip_suffix(".txt"))
            else {
                continue;
            };
            sources.push(test.to_owned());
            let text = fs::read_to_string(entry.path()).unwrap_or_default();
            for line in text.lines() {
                if let Some((key, n)) = line.rsplit_once(' ')
                    && let Ok(n) = n.parse::<u64>()
                {
                    *total.entry(key.to_owned()).or_default() += n;
                }
            }
        }
        sources.sort();
        let summary = format!(
            "coverage across {}:\n{}",
            sources.join(", "),
            render(&total)
        );
        fs::write(dir.join("coverage.txt"), &summary).ok();
        eprintln!("{summary}");
    }
}
