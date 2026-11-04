//! Which rules the generated sequences fired, and which rows of the race catalogue
//! (docs/internals/races.md) they reached. A rule or row no sequence reaches is a search problem:
//! give it a richer starting state or fix its precondition (docs/internals/testing.md).

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
    "op_abandon",
    "trim_below_accepted_push",
    "trim_below_accepted_forget",
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
    "hub_loses_prune",
    "remake_hub",
    "lose_reply",
    "join",
];

/// Events that are not rules: how the hive was set up, and outcomes some rows need.
pub const EVENTS: &[&str] = &[
    "setup:three_machines",
    "setup:shared_workspace_name",
    "setup:shared_hostname",
    "setup:prejoin",
    "setup:empty",
    "setup:dropped_merge",
    "push:accepted",
    "crash:writes_in_flight",
    // Imports of git refs, by what explains each ref they changed (`imports`).
    "import:git_move",
    "import:concurrent_records",
    // Imports of git's HEAD, by what explains each.
    "import:head_git_move",
    "import:concurrent_heads",
    // What the hub did about pruning its records, and faults after it.
    "prune",
    "prune:held_back",
    "prune:forgotten_behind",
    "prune:forgotten_took",
    "prune:stopped",
    "join:after_prune",
    "restart_hub:after_prune",
    "hub_goes_back:after_prune",
    "remake_hub:after_prune",
    "remake_hub:joiner_with_prefix",
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
        "other_machines_workspaces_are_theirs_through_a_merge",
        Some(&["forget_other_workspace", "at_op"]),
    ),
    (
        "forgetting_another_machines_workspace_moves_nothing_built_on_it",
        Some(&["forget_other_workspace", "rebase_revision"]),
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
        "forgotten_working_copies_follow_a_parent_rebased_by_an_abandon",
        Some(&["forget_other_workspace", "abandon"]),
    ),
    (
        "forgotten_working_copies_follow_a_moved_parent",
        Some(&["forget_other_workspace", "rebase_revision"]),
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
        "a_forgotten_copy_comes_back_with_its_next_work",
        Some(&["forget_copy", "commit"]),
    ),
    (
        "a_forgotten_copy_back_by_other_work_gets_a_new_working_copy",
        Some(&["forget_copy", "bookmark_create"]),
    ),
    (
        "a_forgotten_copy_keeps_its_working_copy_through_a_run",
        Some(&["forget_copy"]),
    ),
    (
        "a_forgotten_copy_keeps_its_latest_workspaces_through_a_merge",
        Some(&["setup:three_machines", "workspace_add", "forget_copy"]),
    ),
    (
        "a_rewrite_before_a_forget_sticks_through_a_merge",
        Some(&["rewrite_under_other_wc", "forget_copy", "sync_partial"]),
    ),
    (
        "work_a_forget_didnt_see_keeps_the_copy",
        Some(&["forget_copy", "sync_partial", "commit"]),
    ),
    (
        "unused_copies_are_forgotten_after_their_forget_after",
        Some(&["set_forget_after", "expire_idle"]),
    ),
    (
        "changing_forget_after_is_work",
        Some(&["set_forget_after", "expire_idle", "commit"]),
    ),
    // The search's machines never leave.
    ("leaving_sticks_through_a_merge", None),
    ("a_copy_that_leaves_gets_a_new_working_copy", None),
    ("a_copy_that_left_shows_again_once_it_joins", None),
    // The search names workspaces without a `/`.
    ("own_workspaces_with_a_slash_are_own", None),
    ("own_workspaces_named_like_another_machine_are_own", None),
    (
        "an_operation_that_forgot_its_workspace_keeps_its_name",
        None,
    ),
    (
        "undoing_a_forget_brings_back_nothing",
        Some(&["forget_copy", "undo"]),
    ),
    (
        "concurrent_forgets_agree",
        Some(&["setup:three_machines", "forget_copy"]),
    ),
    (
        "a_forgotten_working_copy_follows_its_rewrite",
        Some(&["forget_copy", "edit_unsnapshotted", "describe"]),
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
        "two_machines_sharing_a_hostname_show_each_other_qualified",
        Some(&["setup:shared_hostname"]),
    ),
    (
        "an_unchanged_import_exports_a_bookmark_selected_by_a_merge",
        Some(&["fetch", "at_op"]),
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
    (
        "a_push_to_a_hive_made_again_is_rejected",
        Some(&["remake_hub", "lose_reply"]),
    ),
    ("joining_with_full_history", Some(&["setup:prejoin"])),
    // The search's machines with history of their own join before any rule runs; later
    // ones join empty, as `musubi clone` makes them.
    (
        "an_operation_from_before_the_join_doesnt_bring_its_history",
        None,
    ),
    (
        "an_operation_on_rewritten_history_from_before_the_join_doesnt_bring_it",
        None,
    ),
    ("empty_repositories_make_a_hive", Some(&["setup:empty"])),
    ("op_abandon_replicates", Some(&["op_abandon"])),
    (
        "a_trim_keeps_a_secondary_workspaces_snapshot_basis",
        Some(&["op_abandon", "edit_unsnapshotted", "rewrite_under_other_wc"]),
    ),
    (
        "e2e_git_change_while_taking_a_trim",
        Some(&[
            "trim_below_accepted_push",
            "sync_partial",
            "bookmark_delete",
        ]),
    ),
    (
        "a_trim_below_an_accepted_forget_keeps_the_copy_forgotten",
        Some(&["trim_below_accepted_forget"]),
    ),
    (
        "e2e_trim_below_accepted_forget",
        Some(&["trim_below_accepted_forget"]),
    ),
    // The search interleaves whole policy steps, not a command inside adapter.advance.
    (
        "a_forward_bookmark_survives_a_command_inside_a_trim_advance",
        None,
    ),
    // This needs two range trims retaining an independently cached root branch.
    (
        "a_second_trim_keeps_git_state_with_a_cached_root_realization",
        None,
    ),
    (
        "a_trim_below_an_accepted_push_keeps_the_other_copy_present",
        Some(&["trim_below_accepted_push"]),
    ),
    (
        "e2e_trim_below_accepted_push",
        Some(&["trim_below_accepted_push"]),
    ),
    // The search does not run jj's object-pruning gc after restoring and abandoning a base.
    (
        "collected_objects_of_an_abandoned_fetch_base_are_fetched_again",
        None,
    ),
    // Hub remakes are between generated syncs, not between requests of a running round.
    ("an_empty_object_reply_retries_from_the_remade_hub", None),
    // These require exact cuts within record taking, not just a partial sync and rollback.
    (
        "a_sync_stopped_while_taking_an_abandon_the_hub_then_loses",
        None,
    ),
    ("taking_an_abandon_resumes_where_it_stopped", None),
    // This correspondence case fixes identical operation metadata on different copies;
    // generated commands advance their timestamps instead.
    ("independent_merges_can_reuse_a_canonical_operation", None),
    // The generator interrupts driver calls, not Git export's physical head replacement.
    (
        "interrupted_git_export_can_leave_aliased_operation_heads",
        None,
    ),
    // These require a receiver that has only record metadata for a dropped operation,
    // followed by rollback and a different raw version of the same immutable original.
    (
        "record_bodies_keep_pending_drops_named_after_hub_rollback",
        None,
    ),
    (
        "lost_records_follow_an_older_name_the_receiver_never_held",
        None,
    ),
    // The search's fixed participants never leave. These native boundary checks also need
    // exact cuts before realization/advancement or a dropped merge with separate images.
    // The generated core survivor_advance_conformance separately targets the new steps.
    (
        "received_records_survive_departure_and_drop_local_aliases",
        None,
    ),
    (
        "an_operation_first_received_after_rollback_uses_the_applied_namespace",
        None,
    ),
    (
        "lost_received_records_preserve_work_before_the_fixup_arrives",
        None,
    ),
    (
        "a_dropped_head_published_again_is_dropped_by_who_took_it",
        None,
    ),
    (
        "advancing_to_what_survives_of_a_dropped_head",
        Some(&["setup:dropped_merge"]),
    ),
    (
        "advancing_to_what_survives_refuses_what_jj_cannot_merge",
        None,
    ),
    (
        "realizing_an_operation_this_machine_dropped_writes_nothing",
        None,
    ),
    // This also needs explicit integration and work on an unpublished realization.
    (
        "pending_drops_get_a_new_tip_when_the_hub_already_has_the_cached_fixup",
        None,
    ),
    (
        "a_receiver_takes_records_that_drop_its_head_above_a_cached_fixup",
        None,
    ),
    // These need a specific interrupted adoption across two record histories, not merely
    // the op_abandon and hub_goes_back rules occurring in the same generated sequence.
    (
        "a_push_can_drop_its_expected_head_and_reuse_a_cached_fixup",
        None,
    ),
    (
        "a_cached_fixup_publishes_pending_drops_even_when_its_head_is_known",
        None,
    ),
    (
        "op_abandon_under_a_realized_head_replicates",
        Some(&["op_abandon"]),
    ),
    (
        "op_abandon_below_a_merge_with_concurrent_work_replicates",
        Some(&["op_abandon"]),
    ),
    (
        "concurrent_op_abandons_on_two_machines",
        Some(&["op_abandon"]),
    ),
    (
        "a_jj_command_in_flight_during_the_rewrite",
        Some(&["op_abandon", "at_op"]),
    ),
    (
        "an_offline_machine_comes_back_after_an_abandon",
        Some(&["op_abandon"]),
    ),
    (
        "hub_restarts_during_and_after_a_rewrite",
        Some(&["op_abandon", "restart_hub"]),
    ),
    (
        "hub_goes_back_or_is_remade_after_a_rewrite",
        Some(&["op_abandon", "hub_goes_back"]),
    ),
    (
        "an_abandon_a_stale_workspace_brought_back_stays",
        Some(&["op_abandon", "workspace_commit"]),
    ),
    // The search runs no `jj util gc`.
    ("op_abandon_then_gc", None),
    (
        "a_trim_makes_the_hub_smaller",
        Some(&["op_abandon", "prune"]),
    ),
    (
        "an_offline_machine_holds_pruning_back",
        Some(&["prune:held_back", "prune"]),
    ),
    (
        "a_forgotten_copy_behind_pruned_records_stops",
        Some(&["prune:stopped"]),
    ),
    (
        "a_forgotten_copy_that_took_the_pruned_records_comes_back",
        Some(&["prune:forgotten_took", "commit"]),
    ),
    // The search delivers every reply at once, never one held up across a prune.
    (
        "a_machine_takes_records_from_a_pruned_one_it_held_before",
        None,
    ),
    ("a_machine_joins_after_a_prune", Some(&["join:after_prune"])),
    (
        "hub_restarts_after_a_prune",
        Some(&["restart_hub:after_prune"]),
    ),
    ("hub_goes_back_across_a_prune", Some(&["hub_loses_prune"])),
    (
        "a_machine_that_joined_after_a_prune_carries_on_when_the_hive_is_made_again",
        Some(&["remake_hub:joiner_with_prefix"]),
    ),
    ("restart_with_lost_cache", Some(&["lose_cache"])),
    (
        "lost_cache_does_not_duplicate_realizations",
        Some(&["lose_cache"]),
    ),
    (
        "crash_with_writes_in_flight",
        Some(&["crash:writes_in_flight"]),
    ),
    // Fixed timestamps intentionally defeat jj metadata uniqueness; the search advances
    // time per command, so this limitation is covered by a targeted jj test.
    (
        "repeated_restores_keep_distinct_identities_when_contracted",
        None,
    ),
    (
        "coalesced_history_after_gc_is_refused_before_publishing_drops",
        None,
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
