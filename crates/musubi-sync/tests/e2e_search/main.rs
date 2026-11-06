//! Generated end-to-end tests (docs/internals/testing.md, "Generated end-to-end tests"): a Hegel
//! state machine drives two or three real colocated repositories, each a musubi node of an
//! in-process hive whose hub prunes its records as a hub does, through local `jj` work,
//! workspaces, forgotten and new copies, a shared `origin`, git-side work, partial syncs, and
//! faults, then syncs to a fixed point and checks that the hive converged. The rules can reach
//! every row of the race catalogue (docs/internals/races.md) but the documented refusals;
//! `coverage` maps rows to rules.
//!
//! After every rule, every op head of every repository a sync or fault touched loads, every `jj`
//! command and sync step must succeed (but for stops a user gets past as the error says, a copy's
//! behind pruned records only where the hive forgot it: `World::recover`), and no import of git
//! refs or of git's HEAD changes a ref that git didn't move, except where jj itself would
//! (`imports`). At every full convergence (`checks`): the fixture's `assert_converged`; every
//! node's canonical head is the hub's; translating every operation again from nothing does what
//! the protocol's model assumes; every operation is on every machine, but those `jj op abandon`
//! dropped, which are on none; tags agree; each machine has its own workspaces, at visible
//! commits; no divergence and no bookmark or tag conflict that jj wouldn't make of the same
//! operations in one repository (`reference`), nor the same rebase done twice (`ledger`); and
//! every machine shows the others' workspaces at their working copies, and git never sees them.
//!
//! `e2e_smoke` runs in the default suite. The search, `e2e_search_shard_*`, runs with
//! `cargo nextest run -p musubi-sync --profile search`; each shard has its own example
//! database under `target/tmp/e2e_search/`, and the run writes which rules fired to
//! `target/tmp/e2e_search/coverage.txt` (printed with `--no-capture`). Environment:
//!
//! - `MUSUBI_SEARCH_CASES`: test cases per shard (default 8; a case takes up to a few minutes when
//!   several shards run at once);
//! - `MUSUBI_SEARCH_STEPS`: rules per sequence (default 30);
//! - `MUSUBI_SEARCH_SEED`: base seed, shard `n` using `seed + n` (default: random);
//! - `MUSUBI_SEARCH_SHRINK`: `0` reports a shard's first failure unshrunk, `1` shrinks the
//!   smoke test's;
//! - `MUSUBI_SEARCH_MASK`: known bugs to look past, comma-separated (see `checks::masked`);
//! - `MUSUBI_SEARCH_TIMING`: print how long each case took;
//! - `MUSUBI_SEARCH_FINGERPRINTS`: a file to append each case's trace to, without what
//!   differs between runs of the same case (`World::fingerprint`): comparing two runs'
//!   files shows whether a case replays exactly;
//! - `HEGEL_STOP_ON_FIRST_FAILURE=false`: keep searching after a failure (for coverage).

#![allow(clippy::unwrap_used)]

#[allow(dead_code)]
#[path = "../races/fixture.rs"]
mod fixture;

mod checks;
mod coverage;
mod imports;
mod ledger;
mod machine;
mod origin;
mod reference;
mod view;
mod world;

use std::cell::RefCell;
use std::io::Write as _;
use std::rc::Rc;

use hegel::HealthCheck;
use hegel::NondeterminismStrictness;
use hegel::Phase;
use hegel::Settings;
use hegel::TestCase;
use hegel::generators as gs;

use crate::coverage::fired;
use crate::machine::Search;
use crate::world::FILES;
use crate::world::Naming;
use crate::world::Setup;
use crate::world::World;

#[derive(Clone, Copy)]
struct Config {
    shard: Option<u64>,
    cases: u64,
    steps: i64,
}

impl Config {
    fn smoke() -> Self {
        Self {
            shard: None,
            cases: 2,
            steps: 12,
        }
    }

    fn shard(shard: u64) -> Self {
        let env = |name: &str, default: u64| {
            std::env::var(name)
                .ok()
                .and_then(|v| v.parse().ok())
                .unwrap_or(default)
        };
        Self {
            shard: Some(shard),
            cases: env("MUSUBI_SEARCH_CASES", 8),
            steps: i64::try_from(env("MUSUBI_SEARCH_STEPS", 30)).unwrap(),
        }
    }

    fn settings(self) -> Settings {
        // Cases replay exactly, so a failure that doesn't replay fails the run at once,
        // saying where the replay went another way. By default Hegel would replay it in
        // batches, for minutes, pass the run if that didn't confirm it, and could keep it to
        // replay in batches again in later runs.
        let settings = Settings::new()
            .test_cases(self.cases)
            .suppress_health_check([HealthCheck::TooSlow, HealthCheck::TestCasesTooLarge])
            .nondeterminism_strictness(NondeterminismStrictness::Error);
        let shrink = std::env::var("MUSUBI_SEARCH_SHRINK").ok();
        let settings = match self.shard {
            // The smoke test is the same on every run, and by default reports its first
            // failure unshrunk: the search is for minimizing.
            None => {
                let settings = settings.derandomize(true).database(None);
                if shrink.as_deref() == Some("1") {
                    return settings;
                }
                settings
            }
            Some(shard) => {
                let database = coverage::dir().join(format!("examples-shard-{shard}"));
                let seed = std::env::var("MUSUBI_SEARCH_SEED")
                    .ok()
                    .and_then(|v| v.parse::<u64>().ok())
                    .map(|seed| seed + shard);
                let settings = settings
                    .database(Some(database.to_string_lossy().into_owned()))
                    .seed(seed);
                if shrink.as_deref() != Some("0") {
                    return settings;
                }
                settings
            }
        };
        settings.phases([Phase::Explicit, Phase::Reuse, Phase::Generate])
    }
}

#[hegel::standalone_function(config.settings())]
fn search(tc: TestCase, config: Config) {
    let _case = coverage::start_case();
    let setup = Setup {
        nodes: tc.draw(gs::integers::<usize>().min_value(2).max_value(3)),
        naming: [Naming::Own, Naming::Default, Naming::SharedHostname]
            [tc.draw(gs::integers::<usize>().max_value(2))],
        prejoin: tc.draw(gs::booleans()),
        secondary: tc.draw(gs::booleans()),
    };
    for (event, happened) in [
        ("setup:three_machines", setup.nodes == 3),
        (
            "setup:shared_workspace_name",
            !matches!(setup.naming, Naming::Own),
        ),
        (
            "setup:shared_hostname",
            matches!(setup.naming, Naming::SharedHostname),
        ),
        ("setup:prejoin", setup.prejoin),
        ("setup:empty", !setup.prejoin),
    ] {
        if happened {
            fired(event);
        }
    }
    walk(tc, config, setup, |_, _| {});
}

#[test]
fn e2e_workspace_names_after_trim_match_native_jj() {
    let mut world = World::new(Setup {
        nodes: 3,
        naming: Naming::SharedHostname,
        prejoin: true,
        secondary: false,
    });
    world.restart(2);
    world.trim_below_accepted_push(1);
    world.sync(0);
    world.trim_below_accepted_forget(0, 1);
    world.sync(2);
    world.rename_workspace(0, 0, "alpha");
    let view = world.observe(0);
    world.raw_jj(
        0,
        &[
            "--ignore-working-copy",
            "bookmark",
            "list",
            "-T",
            r#"if(!remote && present, name ++ "\n")"#,
        ],
    );
    let target = view
        .commits
        .iter()
        .find(|commit| commit.working_copies.iter().any(|name| name == "alpha"))
        .unwrap()
        .id
        .clone();
    world.jj(0, &["bookmark", "create", "topic", "-r", &target]);
    let view = world.observe(1);
    let prejoin = view
        .commits
        .iter()
        .find(|commit| commit.subject == "pre-join work on beta")
        .unwrap();
    let parent = view
        .commits
        .iter()
        .find(|commit| commit.subject.is_empty() && commit.parents == [prejoin.id.clone()])
        .unwrap()
        .id
        .clone();
    world.jj(1, &["new", &parent]);
    world.forget_copy(2, 0);
    let commit = world
        .observe(0)
        .commits
        .into_iter()
        .find(|commit| commit.subject == "pre-join work on beta")
        .unwrap()
        .id;
    let description = world.message(0);
    world.jj(0, &["describe", &commit, "-m", &description]);
    world.restart_hub();
    let foreign = world.foreign_workspace_names(0)[0].clone();
    world.jj(0, &["workspace", "forget", &foreign]);
    world.converge();
    assert!(world.logical_extras[0].contains("default"));
}

/// A case: the hive `setup` makes, which `prefix` takes further, a generated walk from there,
/// and convergence.
fn walk(tc: TestCase, config: Config, setup: Setup, prefix: impl FnOnce(&TestCase, &mut World)) {
    let started = std::time::Instant::now();
    let world = Rc::new(RefCell::new(World::new(setup)));
    prefix(&tc, &mut world.borrow_mut());
    let set_up = started.elapsed();
    hegel::stateful::machine(Search {
        world: world.clone(),
        faults: 0,
        undos: 0,
        converges: 0,
    })
    .steps(config.steps)
    .run(tc);
    let walked = started.elapsed();
    world.borrow_mut().converge();
    if let Some(path) = std::env::var_os("MUSUBI_SEARCH_FINGERPRINTS") {
        let mut file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .unwrap();
        // In one write, so that shards running at once don't interleave their records.
        let record = format!("case {setup:?}\n{}\n", world.borrow().fingerprint());
        file.write_all(record.as_bytes()).unwrap();
    }
    if std::env::var_os("MUSUBI_SEARCH_TIMING").is_some() {
        eprintln!(
            "case: {setup:?}, setup {set_up:?}, steps {:?}, converge {:?}",
            walked - set_up,
            started.elapsed() - walked
        );
    }
}

/// The search from a merge alpha dropped and gamma keeps, which beta, with work of its own,
/// took the drop of without advancing, before the hub went back and gamma published the merge
/// again (`World::hold_dropped_merge`). Beta alone, before alpha does anything again, advances
/// to what survives of it, two operations neither below the other, merged with its work in
/// one operation, and publishes the drop. Then a walk, as the search's, and convergence.
#[hegel::standalone_function(config.settings())]
fn dropped_merge_search(tc: TestCase, config: Config) {
    let _case = coverage::start_case();
    let setup = Setup {
        nodes: 4,
        naming: [Naming::Own, Naming::Default, Naming::SharedHostname]
            [tc.draw(gs::integers::<usize>().max_value(2))],
        prejoin: tc.draw(gs::booleans()),
        secondary: tc.draw(gs::booleans()),
    };
    fired("setup:dropped_merge");
    walk(tc, config, setup, |tc, world| {
        let work: Vec<usize> = (0..tc.draw(gs::integers::<usize>().min_value(1).max_value(2)))
            .map(|_| tc.draw(gs::integers::<usize>().max_value(FILES.len() - 1)))
            .collect();
        let kept = world.hold_dropped_merge(&work);
        world.sync(1);
        world.check_dropped_by(1, &kept);
    });
}

#[test]
fn e2e_dropped_merge() {
    let _report = coverage::Report("dropped-merge");
    dropped_merge_search(Config::smoke());
}

/// Exercise the trim rule's history bookkeeping and independent jj replay, including the
/// joins that ordinary generated single-operation abandonment leaves in place.
#[test]
fn e2e_trim_below_accepted_push() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Own,
        prejoin: false,
        secondary: false,
    });
    world.trim_below_accepted_push(0);
    world.converge();
}

/// The generated forget/trim rule retains the independent import and history checks.
#[test]
fn e2e_trim_below_accepted_forget() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Own,
        prejoin: false,
        secondary: false,
    });
    world.trim_below_accepted_forget(0, 1);
    world.converge();
}

#[test]
fn e2e_git_change_while_taking_a_trim() {
    for forward in [false, true] {
        let mut world = World::new(Setup {
            nodes: 2,
            naming: Naming::Own,
            prejoin: false,
            secondary: false,
        });
        world.commit(1, 0, 0);
        world.jj(1, &["bookmark", "create", "x", "-r", "@-"]);
        world.converge();
        world.trim_below_accepted_push(0);
        world.sync_realizing(1, 1);
        if forward {
            world.jj(1, &["bookmark", "set", "x", "-r", "@"]);
        } else {
            world.jj(1, &["bookmark", "delete", "x"]);
        }
        world.converge();
    }
}

/// A command above an abandoned merge keeps its own payload when its one parent
/// expands to two. The later, genuine reconciliation must still merge both commands.
#[test]
fn e2e_command_above_dropped_merge() {
    let mut world = World::new(Setup {
        nodes: 4,
        naming: Naming::Own,
        prejoin: false,
        secondary: false,
    });
    let kept = world.hold_dropped_merge(&[0]);
    world.sync(1);
    world.check_dropped_by(1, &kept);
    let target = |world: &World, m, suffix: &str| {
        world
            .view_at_head(m)
            .commits
            .into_iter()
            .find(|c| c.subject.ends_with(suffix))
            .unwrap()
            .id
    };
    let a = target(&world, 0, "on alpha");
    let b = target(&world, 2, "on gamma");
    world.jj(0, &["bookmark", "set", "both", "-r", &a]);
    world.jj(2, &["bookmark", "set", "both", "-r", &b]);
    world.converge();
    let out = world.raw_jj(0, &["--ignore-working-copy", "bookmark", "list", "both"]);
    assert!(
        out.contains("conflict"),
        "expected both commands' targets: {out}"
    );
    // Trimming to the root preserves the inherited conflict in the surviving command.
    world.trim_below_accepted_push(0);
    world.converge();
}

/// The reference needs operations written before the requested command, and a read that
/// snapshots too: either can be the command whose parent later expands through a drop.
#[test]
fn e2e_records_snapshots_from_commands_and_looking() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Own,
        prejoin: false,
        secondary: false,
    });
    world.edit(0, 0);
    world.jj(0, &["describe", "-m", "after snapshot"]);
    let store = world.fx.hive.members[0]
        .adapter
        .repo()
        .loader()
        .op_store()
        .clone();
    let read = |hex: &str| {
        let id = jj_lib::op_store::OperationId::try_from_hex(hex).unwrap();
        futures::executor::block_on(store.read_operation(&id)).unwrap()
    };
    let command = read(&world.latest_op_head(0));
    let snapshot = read(&jj_lib::object_id::ObjectId::hex(&command.parents[0]));
    assert_eq!(snapshot.metadata.description, "snapshot working copy");
    for op in [&snapshot, &command] {
        assert!(world.commands.contains_key(&world::merge_key(op)));
    }
    world.edit(0, 1);
    world.observe(0);
    let snapshot = read(&world.latest_op_head(0));
    assert_eq!(snapshot.metadata.description, "snapshot working copy");
    assert!(world.commands.contains_key(&world::merge_key(&snapshot)));
    world.converge();
}

#[test]
fn e2e_search_shard_4() {
    let _report = coverage::Report("shard-4-survivors");
    dropped_merge_search(Config::shard(4));
}

#[test]
fn e2e_smoke() {
    let _report = coverage::Report("smoke");
    search(Config::smoke());
}

#[test]
fn e2e_search_shard_0() {
    let _report = coverage::Report("shard-0");
    search(Config::shard(0));
}

#[test]
fn e2e_search_shard_1() {
    let _report = coverage::Report("shard-1");
    search(Config::shard(1));
}

#[test]
fn e2e_search_shard_2() {
    let _report = coverage::Report("shard-2");
    search(Config::shard(2));
}

#[test]
fn e2e_search_shard_3() {
    let _report = coverage::Report("shard-3");
    search(Config::shard(3));
}
