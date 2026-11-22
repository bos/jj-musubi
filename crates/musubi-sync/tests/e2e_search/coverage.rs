//! Rule activity, approximate exploration guidance, and independently witnessed races.
//!
//! Catalogue rule combinations suggest where to search; their occurrence does not prove
//! the named race happened. Only qualified native receipts from cases that completed all
//! checks count as witnessed. Each report covers its own test execution and reads no old files.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::rc::Rc;

use serde::Serialize;

use crate::identity::SourceKey;
use crate::world::CommandSnapshot;

mod witnesses;

use witnesses::Race;
use witnesses::Tracker;

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

/// Events that are not rules: how the hive was set up, and outcomes some rows need.
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
    // Imports of git's HEAD, by what explains each.
    "import:head_git_move",
    "import:concurrent_heads",
    "join:with_history",
    "join:fetch_conflict",
    // A forgotten copy's sync rebased a hidden working copy of its own.
    "forgotten:working_copy_rebased",
];

/// Approximate exploration guidance for each race-catalogue test. These rule combinations
/// identify candidate sequences, without establishing participants, objects or ordering.
/// `None` marks cases deliberately outside this search. Witness support is separate.
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
    // Copy-name resolution is exercised by the native and CLI tests; generated forgets
    // name copies by their keys and keep a primary workspace for later commands.
    ("a_copy_without_workspaces_can_be_forgotten_by_name", None),
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
    ("own_workspaces_with_a_slash_stay_here_until_renamed", None),
    ("own_workspaces_named_like_another_machine_stay_apart", None),
    (
        "own_workspaces_named_like_one_added_meanwhile_stay_apart",
        None,
    ),
    (
        "own_workspaces_named_like_one_of_a_machine_joining_meanwhile_stay_apart",
        None,
    ),
    (
        "own_workspaces_named_like_one_forgotten_here_stay_apart",
        None,
    ),
    (
        "a_workspace_shown_again_by_a_longer_name_can_lose_a_move_meanwhile",
        None,
    ),
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
        "a_forgotten_working_copy_follows_a_rewrite_of_its_parent",
        Some(&[
            "forgotten:working_copy_rebased",
            "describe",
            "edit_unsnapshotted",
        ]),
    ),
    (
        "a_forgotten_working_copy_follows_an_abandon_of_its_parent",
        Some(&[
            "forgotten:working_copy_rebased",
            "abandon",
            "edit_unsnapshotted",
        ]),
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
    (
        "joining_takes_the_newer_main_from_either_copy",
        Some(&["join:with_history", "origin_advance", "fetch"]),
    ),
    (
        "joining_fetches_ambiguous_remote_bookmarks",
        Some(&["join:fetch_conflict"]),
    ),
    (
        "e2e_join_after_upstream_rewrite",
        Some(&["join:fetch_conflict"]),
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
    // Later joins can bring Git history, but commands on their private operation history
    // from before admission are not generated.
    (
        "an_operation_from_before_the_join_doesnt_bring_its_history",
        None,
    ),
    (
        "an_operation_on_rewritten_history_from_before_the_join_doesnt_bring_it",
        None,
    ),
    ("empty_repositories_make_a_hive", Some(&["setup:empty"])),
    // The search has no operation-restore rule.
    (
        "abandoning_a_restore_of_an_old_alias_keeps_others_workspaces_theirs",
        None,
    ),
    (
        "abandoning_a_restore_of_a_forgotten_machines_workspace_keeps_it_theirs",
        None,
    ),
    ("abandoning_the_add_of_an_own_workspace_keeps_it_here", None),
    // Hub remakes are between generated syncs, not between requests of a running round.
    ("an_empty_object_reply_retries_from_the_remade_hub", None),
    // This correspondence case fixes identical operation metadata on different copies;
    // generated commands advance their timestamps instead.
    ("independent_merges_can_reuse_a_canonical_operation", None),
    // The generator interrupts driver calls, not Git export's physical head replacement.
    (
        "interrupted_git_export_can_leave_aliased_operation_heads",
        None,
    ),
    (
        "a_native_serial_merge_can_repeat_a_rebase_after_abandon",
        Some(&["op_abandon", "at_op"]),
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
    // A negative control of a design musubi does not use.
    ("verbatim_replication_reverts_bookmarks", None),
];

/// Counts belong to one report, including every attempted case's rule activity. A witness
/// receipt is admitted separately, only once that case has completed its checks.
#[derive(Default)]
struct Totals {
    attempts: u64,
    completed: u64,
    activity: BTreeMap<&'static str, u64>,
    combinations: BTreeMap<&'static str, u64>,
    races: BTreeMap<&'static str, RaceTotal>,
}

struct RaceTotal {
    cases: u64,
    first_receipt: String,
}

impl Totals {
    fn add_case(
        &mut self,
        activity: &BTreeMap<&'static str, u64>,
        witnesses: impl IntoIterator<Item = (Race, String)>,
        passed: bool,
    ) {
        self.attempts += 1;
        for (&rule, &count) in activity {
            *self.activity.entry(rule).or_default() += count;
        }
        for &(row, needs) in CATALOGUE {
            if needs.is_some_and(|needs| needs.iter().all(|need| activity.contains_key(need))) {
                *self.combinations.entry(row).or_default() += 1;
            }
        }
        if passed {
            self.completed += 1;
            let mut counted = BTreeSet::new();
            for (race, receipt) in witnesses {
                let name = race.catalogue_name();
                if !counted.insert(name) {
                    continue;
                }
                let total = self.races.entry(name).or_insert(RaceTotal {
                    cases: 0,
                    first_receipt: receipt,
                });
                total.cases += 1;
            }
        }
    }
}

#[derive(Default)]
struct CaseData {
    activity: BTreeMap<&'static str, u64>,
    tracker: Tracker,
}

type SharedTotals = Rc<RefCell<Totals>>;
type SharedCase = Rc<RefCell<CaseData>>;

thread_local! {
    #[cfg_attr(
        any(target_os = "illumos", target_os = "solaris"),
        allow(
            clippy::missing_const_for_thread_local,
            reason = "clippy wrongly reports this on illumos, but only when the \
                      rust-src component is installed, so it's allowed rather than expected"
        )
    )]
    static REPORT: RefCell<Option<SharedTotals>> = const { RefCell::new(None) };
    #[cfg_attr(
        any(target_os = "illumos", target_os = "solaris"),
        allow(
            clippy::missing_const_for_thread_local,
            reason = "clippy wrongly reports this on illumos, but only when the \
                      rust-src component is installed, so it's allowed rather than expected"
        )
    )]
    static CASE: RefCell<Option<SharedCase>> = const { RefCell::new(None) };
}

/// Counts a rule that passed its precondition, or an observed setup/outcome event.
/// Rule activity remains useful even when a later assumption or check stops the case.
pub fn fired(rule: &'static str) {
    debug_assert!(
        RULES.contains(&rule) || EVENTS.contains(&rule),
        "unlisted rule {rule}"
    );
    CASE.with(|current| {
        if let Some(case) = current.borrow().as_ref() {
            let mut case = case.borrow_mut();
            *case.activity.entry(rule).or_default() += 1;
            if RULES.contains(&rule) {
                case.tracker.rule(rule);
            }
        }
    });
}

/// Captures evidence already read by the recorded-command boundary. Qualification neither
/// probes an actor nor changes what the oracle accepts.
pub fn record_native(
    op: &jj_lib::op_store::Operation,
    snapshot: &CommandSnapshot,
    before: &BTreeSet<SourceKey>,
) {
    CASE.with(|current| {
        if let Some(case) = current.borrow().as_ref() {
            case.borrow_mut().tracker.command(op, snapshot, before);
        }
    });
}

/// Breaks the conservative independence interval at a synchronization or other barrier.
pub fn interrupt_races() {
    CASE.with(|current| {
        if let Some(case) = current.borrow().as_ref() {
            case.borrow_mut().tracker.interrupt();
        }
    });
}

/// Starts a case with its own tracker and captures the current report as its owner.
/// Dropping retains activity; call `passed` after every final check to admit its witnesses.
pub fn start_case() -> Case {
    let data = Rc::new(RefCell::new(CaseData::default()));
    let previous = CASE.with(|current| current.replace(Some(data.clone())));
    let report = REPORT.with(|current| current.borrow().clone());
    Case {
        data,
        report,
        previous,
        passed: false,
    }
}

pub struct Case {
    data: SharedCase,
    report: Option<SharedTotals>,
    previous: Option<SharedCase>,
    passed: bool,
}

impl Case {
    /// The generated walk and its final convergence checks completed successfully.
    pub fn passed(mut self) {
        self.passed = true;
    }

    /// Whether this case has captured a qualified receipt for the named race. Reporting
    /// still requires `passed`; the native bridge tests inspect this before finishing.
    pub fn witnessed(&self, name: &str) -> bool {
        self.data
            .borrow()
            .tracker
            .witnesses()
            .any(|(race, _)| race.catalogue_name() == name)
    }
}

impl Drop for Case {
    fn drop(&mut self) {
        CASE.with(|current| current.replace(self.previous.take()));
        if let Some(report) = &self.report {
            let case = self.data.borrow();
            let witnesses = case
                .tracker
                .witnesses()
                .map(|(race, witness)| (race, witness.to_string()));
            report
                .borrow_mut()
                .add_case(&case.activity, witnesses, self.passed);
        }
    }
}

pub fn dir() -> PathBuf {
    PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("e2e_search")
}

/// Raw output records both the witness support and the observations for each catalogue row.
/// A zero for an instrumented race differs from a row whose witness is not implemented.
#[derive(Serialize)]
struct RawCounts<'a> {
    schema_version: u8,
    test: &'a str,
    attempted_cases: u64,
    completed_cases: u64,
    rule_activity: &'a BTreeMap<&'static str, u64>,
    catalogue: Vec<CatalogueCount<'a>>,
}

#[derive(Serialize)]
struct CatalogueCount<'a> {
    race: &'static str,
    /// Approximate guidance only; failed and discarded cases contribute here too.
    rule_combination_cases: u64,
    suggested_rules: Option<&'static [&'static str]>,
    evidence: RaceEvidence<'a>,
}

#[derive(Serialize)]
#[serde(tag = "status", rename_all = "snake_case")]
enum RaceEvidence<'a> {
    Excluded,
    NotInstrumented,
    NotWitnessed,
    Witnessed {
        completed_cases: u64,
        first_receipt: &'a str,
    },
}

impl<'a> RawCounts<'a> {
    fn of(name: &'a str, totals: &'a Totals) -> Self {
        let catalogue = CATALOGUE
            .iter()
            .map(|&(race, rules)| {
                let evidence = if rules.is_none() {
                    RaceEvidence::Excluded
                } else if !Race::ALL.iter().any(|known| known.catalogue_name() == race) {
                    RaceEvidence::NotInstrumented
                } else if let Some(total) = totals.races.get(race) {
                    RaceEvidence::Witnessed {
                        completed_cases: total.cases,
                        first_receipt: &total.first_receipt,
                    }
                } else {
                    RaceEvidence::NotWitnessed
                };
                CatalogueCount {
                    race,
                    rule_combination_cases: totals.combinations.get(race).copied().unwrap_or(0),
                    suggested_rules: rules,
                    evidence,
                }
            })
            .collect();
        Self {
            schema_version: 2,
            test: name,
            attempted_cases: totals.attempts,
            completed_cases: totals.completed,
            rule_activity: &totals.activity,
            catalogue,
        }
    }
}

fn render(name: &str, totals: &Totals) -> String {
    let counts = RawCounts::of(name, totals);
    let mut out = String::new();
    writeln!(out, "coverage v2 for {name} (this test execution only):").unwrap();
    writeln!(
        out,
        "cases: {} completed all checks / {} attempted",
        totals.completed, totals.attempts
    )
    .unwrap();
    writeln!(
        out,
        "rules and events (times fired across attempted cases):"
    )
    .unwrap();
    for rule in RULES.iter().chain(EVENTS) {
        writeln!(
            out,
            "  {rule:<28} {}",
            totals.activity.get(rule).copied().unwrap_or(0)
        )
        .unwrap();
    }
    writeln!(
        out,
        "catalogue races (native witnesses from completed cases):"
    )
    .unwrap();
    for row in &counts.catalogue {
        match &row.evidence {
            RaceEvidence::Excluded => writeln!(out, "  {}: excluded", row.race).unwrap(),
            RaceEvidence::NotInstrumented => {
                writeln!(out, "  {}: not instrumented", row.race).unwrap();
            }
            RaceEvidence::NotWitnessed => {
                writeln!(out, "  {}: not witnessed", row.race).unwrap();
            }
            RaceEvidence::Witnessed {
                completed_cases,
                first_receipt,
            } => {
                writeln!(
                    out,
                    "  {}: witnessed in {completed_cases} completed cases",
                    row.race
                )
                .unwrap();
                for line in first_receipt.lines() {
                    writeln!(out, "    {line}").unwrap();
                }
            }
        }
    }
    writeln!(
        out,
        "approximate rule combinations (exploration guidance across attempted cases):"
    )
    .unwrap();
    for row in &counts.catalogue {
        if let Some(needs) = row.suggested_rules {
            writeln!(
                out,
                "  {}: {} via {}",
                row.race,
                row.rule_combination_cases,
                needs.join(" + ")
            )
            .unwrap();
        }
    }
    let never: Vec<&str> = RULES
        .iter()
        .chain(EVENTS)
        .copied()
        .filter(|rule| !totals.activity.contains_key(rule))
        .collect();
    if never.is_empty() {
        writeln!(out, "every listed rule and event fired").unwrap();
    } else {
        writeln!(out, "never fired: {}", never.join(", ")).unwrap();
    }
    out
}

const RETIRED_TOTAL: &str = "The cross-test coverage total has been retired.\n\
Coverage is reported per test execution in coverage-v2-<test>.txt and counts-v2-<test>.json.\n\
Use the files emitted by the current test command.\n";

fn write_report(dir: &Path, name: &str, totals: &Totals) -> std::io::Result<()> {
    fs::create_dir_all(dir)?;
    fs::write(dir.join("coverage.txt"), RETIRED_TOTAL)?;
    fs::write(
        dir.join(format!("coverage-v2-{name}.txt")),
        render(name, totals),
    )?;
    let raw = serde_json::to_vec_pretty(&RawCounts::of(name, totals))
        .expect("coverage counts serialize to JSON");
    fs::write(dir.join(format!("counts-v2-{name}.json")), raw)
}

/// One test execution's counts. The thread-local scope isolates tests even under the
/// ordinary test harness; nested reports restore their outer owner on drop.
pub struct Report {
    name: &'static str,
    totals: SharedTotals,
    previous: Option<SharedTotals>,
}

impl Report {
    pub fn new(name: &'static str) -> Self {
        let totals = Rc::new(RefCell::new(Totals::default()));
        let previous = REPORT.with(|current| current.replace(Some(totals.clone())));
        Self {
            name,
            totals,
            previous,
        }
    }
}

impl Drop for Report {
    fn drop(&mut self) {
        REPORT.with(|current| current.replace(self.previous.take()));
        let totals = self.totals.borrow();
        eprintln!("{}", render(self.name, &totals));
        if let Err(error) = write_report(&dir(), self.name, &totals) {
            eprintln!("could not write coverage for {}: {error}", self.name);
        }
    }
}

#[test]
fn rule_combinations_do_not_claim_a_race() {
    let mut totals = Totals::default();
    let activity = BTreeMap::from([("describe", 1), ("squash_into", 1)]);
    totals.add_case(&activity, [], true);
    assert_eq!(
        totals.combinations["same_change_rewritten_on_two_machines"],
        1
    );
    assert_eq!(
        totals.combinations["both_machines_squash_into_the_same_commit"],
        1
    );
    assert!(totals.races.is_empty());
    let output = serde_json::to_value(RawCounts::of("test", &totals)).unwrap();
    for race in [
        "same_change_rewritten_on_two_machines",
        "both_machines_squash_into_the_same_commit",
    ] {
        let row = output["catalogue"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["race"] == race)
            .unwrap();
        assert_eq!(row["evidence"]["status"], "not_witnessed");
    }
}

#[test]
fn only_completed_cases_admit_witness_receipts() {
    let mut totals = Totals::default();
    let race = Race::SameChangeRewritten;
    let activity = BTreeMap::from([("describe", 2)]);
    totals.add_case(&activity, [(race, "discarded receipt".to_owned())], false);
    assert_eq!(totals.activity["describe"], 2);
    assert_eq!(totals.combinations[race.catalogue_name()], 1);
    assert!(totals.races.is_empty());
    totals.add_case(
        &activity,
        [
            (race, "completed receipt".to_owned()),
            (race, "another receipt in the same case".to_owned()),
        ],
        true,
    );
    assert_eq!(totals.attempts, 2);
    assert_eq!(totals.completed, 1);
    assert_eq!(totals.races[race.catalogue_name()].cases, 1);
    assert_eq!(
        totals.races[race.catalogue_name()].first_receipt,
        "completed receipt"
    );
}

#[test]
fn an_uninstrumented_race_is_not_a_zero_or_an_exclusion() {
    let totals = Totals::default();
    let output = serde_json::to_value(RawCounts::of("test", &totals)).unwrap();
    let row = |name: &str| {
        output["catalogue"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["race"] == name)
            .unwrap()
    };
    assert_eq!(
        row("same_change_rewritten_on_two_machines")["evidence"]["status"],
        "not_witnessed"
    );
    assert_eq!(
        row("concurrent_fetches_of_a_moving_remote")["evidence"]["status"],
        "not_instrumented"
    );
    assert_eq!(
        row("a_copy_without_workspaces_can_be_forgotten_by_name")["evidence"]["status"],
        "excluded"
    );
}

#[test]
fn reports_do_not_share_cases_or_rule_activity() {
    let outer = Report::new("isolation-outer");
    let first = start_case();
    fired("commit");
    first.passed();
    {
        let inner = Report::new("isolation-inner");
        let case = start_case();
        fired("describe");
        drop(case);
        assert_eq!(
            inner.totals.borrow().activity,
            BTreeMap::from([("describe", 1)])
        );
        assert_eq!(inner.totals.borrow().completed, 0);
    }
    let second = start_case();
    fired("commit");
    second.passed();
    assert_eq!(outer.totals.borrow().attempts, 2);
    assert_eq!(outer.totals.borrow().completed, 2);
    assert_eq!(
        outer.totals.borrow().activity,
        BTreeMap::from([("commit", 2)])
    );
}

#[test]
fn old_reports_never_contribute_to_a_current_report() {
    let dir = musubi_testutil::tempdir();
    fs::write(
        dir.path().join("coverage.txt"),
        "every catalogue row reached",
    )
    .unwrap();
    fs::write(
        dir.path().join("counts-old.txt"),
        "row:same_change_rewritten_on_two_machines 999",
    )
    .unwrap();
    fs::write(
        dir.path().join("counts-v2-old.json"),
        r#"{"schema_version":2,"completed_cases":999}"#,
    )
    .unwrap();
    let totals = Totals::default();
    write_report(dir.path(), "current", &totals).unwrap();
    let current: serde_json::Value =
        serde_json::from_slice(&fs::read(dir.path().join("counts-v2-current.json")).unwrap())
            .unwrap();
    assert_eq!(current["attempted_cases"], 0);
    assert_eq!(current["completed_cases"], 0);
    for row in current["catalogue"].as_array().unwrap() {
        assert_ne!(row["evidence"]["status"], "witnessed");
    }
    assert!(!dir.path().join("counts-current.txt").exists());
    assert_eq!(
        fs::read_to_string(dir.path().join("coverage.txt")).unwrap(),
        RETIRED_TOTAL
    );
}
