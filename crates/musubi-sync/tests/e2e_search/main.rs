//! Generated end-to-end tests (docs/internals/testing.md, "Generated end-to-end tests"): a Hegel
//! state machine drives two or three real colocated repositories, each a musubi node of an
//! in-process hive whose hub prunes its records as a hub does, through local `jj` work,
//! workspaces, forgotten and new copies, a shared `origin`, git-side work, partial syncs, and
//! faults, then syncs to a fixed point and checks that the hive converged. `coverage` maps race
//! catalogue rows (docs/internals/races.md) to suggested rules and reports concrete native
//! witnesses separately from that exploration guidance.
//!
//! After every rule, every op head of every repository a sync or fault touched loads, every `jj`
//! command and sync step must succeed (but for stops a user gets past as the error says, a copy's
//! behind pruned records only where the hive forgot it: `World::recover`), and no import of git
//! refs or of git's HEAD changes a ref that git didn't move, except where jj itself would
//! (`imports`). At every full convergence (`checks`): the fixture's `assert_converged`; every
//! node's canonical head is the hub's; translating every operation again from nothing does what
//! the protocol's model assumes; every replicated operation is on every machine, down to its
//! independently recorded join point, but those native `jj op abandon` removed completely,
//! which are on none; tags agree; each machine has its own workspaces, at visible
//! commits; no divergence and no bookmark or tag conflict that jj wouldn't make of the same
//! operations in one repository (`reference`), nor independent merges doing the same rebase
//! twice (`ledger`); and
//! every machine shows the others' workspaces at their working copies, and git never sees them.
//!
//! `e2e_smoke` runs in the default suite. The search, `e2e_search_shard_*`, runs with
//! `cargo nextest run -p musubi-sync --profile search`; each shard has its own example
//! database under `target/tmp/e2e_search/`. Each test writes `coverage-v2-<test>.txt` and
//! `counts-v2-<test>.json` there, separating rule activity, approximate exploration guidance
//! and native race witnesses from completed cases (printed with `--no-capture`). Environment:
//!
//! - `MUSUBI_SEARCH_CASES`: test cases per shard (default 8; a case takes up to a few minutes when
//!   several shards run at once);
//! - `MUSUBI_SEARCH_STEPS`: rules per sequence (default 30);
//! - `MUSUBI_SEARCH_SEED`: base seed, shard `n` using `seed + n` (default: random);
//! - `MUSUBI_SEARCH_SHRINK`: `1` shrinks a failure, `0` reports it unshrunk (default: the
//!   shards shrink, and the smoke tests, `e2e_smoke` and `e2e_dropped_merge`, don't);
//! - `MUSUBI_SEARCH_MASK`: known bugs to look past, comma-separated (see `checks::masked`);
//! - `MUSUBI_SEARCH_TIMING`: print how long each case took;
//! - `MUSUBI_SEARCH_VERIFY_OBSERVATIONS`: compare read-only staleness observations with
//!   the original native `jj` probes, retaining their command seeds;
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
mod identity;
mod imports;
mod ledger;
mod machine;
mod origin;
mod reference;
mod regressions;
mod view;
mod world;

use std::io::Write as _;

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

/// How machines name their workspaces: the ordinary case first, which a failure shrinks to.
const NAMINGS: [Naming; 3] = [Naming::Own, Naming::Default, Naming::SharedHostname];

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
        let mut settings = Settings::new()
            .test_cases(self.cases)
            .suppress_health_check([HealthCheck::TooSlow, HealthCheck::TestCasesTooLarge])
            .nondeterminism_strictness(NondeterminismStrictness::Error);
        // By default the smoke test reports its first failure unshrunk: the search is for
        // minimizing.
        let shrink = match std::env::var("MUSUBI_SEARCH_SHRINK").as_deref() {
            Ok("0") => false,
            Ok("1") => true,
            _ => self.shard.is_some(),
        };
        if !shrink {
            settings = settings.phases([Phase::Explicit, Phase::Reuse, Phase::Generate]);
        }
        match self.shard {
            // The smoke test is the same on every run.
            None => settings.derandomize(true).database(None),
            Some(shard) => {
                let database = coverage::dir().join(format!("examples-shard-{shard}"));
                settings = settings.database(Some(database.to_string_lossy().into_owned()));
                // Without `MUSUBI_SEARCH_SEED`, `HEGEL_SEED` or else a random seed.
                if let Some(seed) = std::env::var("MUSUBI_SEARCH_SEED")
                    .ok()
                    .and_then(|v| v.parse::<u64>().ok())
                {
                    settings = settings.seed(Some(seed + shard));
                }
                settings
            }
        }
    }
}

#[hegel::standalone_function(config.settings())]
fn search(tc: TestCase, config: Config) {
    let case = coverage::start_case();
    let nodes = tc.draw(gs::integers::<usize>().min_value(2).max_value(3));
    let naming = tc.draw(gs::sampled_from(&NAMINGS[..]));
    let prejoin = tc.draw(gs::booleans());
    let secondary = tc.draw(gs::booleans());
    let setup = Setup {
        nodes,
        naming,
        prejoin,
        secondary,
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
    case.passed();
}

/// A case: the hive `setup` makes, which `prefix` takes further, a generated walk from there,
/// and convergence.
fn walk(tc: TestCase, config: Config, setup: Setup, prefix: impl FnOnce(&TestCase, &mut World)) {
    let started = std::time::Instant::now();
    let mut world = World::new(setup);
    prefix(&tc, &mut world);
    let set_up = started.elapsed();
    hegel::stateful::machine(Search::new(&mut world))
        .steps(config.steps)
        .run(tc);
    let walked = started.elapsed();
    world.converge();
    if let Some(path) = std::env::var_os("MUSUBI_SEARCH_FINGERPRINTS") {
        let mut file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .unwrap();
        // In one write, so that shards running at once don't interleave their records.
        let record = format!("case {setup:?}\n{}\n", world.fingerprint());
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
    let case = coverage::start_case();
    let naming = tc.draw(gs::sampled_from(&NAMINGS[..]));
    let prejoin = tc.draw(gs::booleans());
    let secondary = tc.draw(gs::booleans());
    let setup = Setup {
        nodes: 4,
        naming,
        prejoin,
        secondary,
    };
    fired("setup:dropped_merge");
    walk(tc, config, setup, |tc, world| {
        // The files beta commits.
        let work = tc.draw(
            gs::vecs(gs::sampled_from(&FILES[..]))
                .min_size(1)
                .max_size(2),
        );
        let work: Vec<usize> = work
            .iter()
            .map(|file| FILES.iter().position(|f| f == file).unwrap())
            .collect();
        let kept = world.hold_dropped_merge(&work);
        world.sync(1);
        world.check_dropped_by(1, &kept);
    });
    case.passed();
}

#[test]
fn e2e_dropped_merge() {
    let _report = coverage::Report::new("dropped-merge");
    dropped_merge_search(Config::smoke());
}

/// The fifth shard searches from the dropped merge of `dropped_merge_search`, not from the
/// setups of `search`, so that the nightly run walks that start too: the same walk and
/// checks, with a report of its own.
#[test]
fn e2e_search_shard_4() {
    let _report = coverage::Report::new("shard-4-dropped-merge");
    dropped_merge_search(Config::shard(4));
}

#[test]
fn e2e_smoke() {
    let _report = coverage::Report::new("smoke");
    search(Config::smoke());
}

#[test]
fn e2e_join_after_upstream_rewrite() {
    let _report = coverage::Report::new("join-rewrite");
    join_after_upstream_rewrite(Config::smoke());
}

/// Reach the ambiguous admission boundary before continuing the ordinary generated walk.
/// The independent jj replay and import checks must accept the fetch and its replication.
#[hegel::standalone_function(config.settings())]
fn join_after_upstream_rewrite(tc: TestCase, config: Config) {
    let case = coverage::start_case();
    walk(
        tc,
        config,
        Setup {
            nodes: 2,
            naming: Naming::Own,
            prejoin: false,
            secondary: false,
        },
        |_, world| {
            world.origin.advance();
            world.jj(0, &["git", "fetch", "--remote", "origin"]);
            world.sync(0);
            world.origin.rewrite();
            world.join_existing_copy(2);
            // An ambiguous name would make this native revision lookup fail.
            world.raw_jj(
                2,
                &["log", "--no-graph", "-r", "main@origin", "-T", "commit_id"],
            );
        },
    );
    case.passed();
}

#[test]
fn e2e_search_shard_0() {
    let _report = coverage::Report::new("shard-0");
    search(Config::shard(0));
}

#[test]
fn e2e_search_shard_1() {
    let _report = coverage::Report::new("shard-1");
    search(Config::shard(1));
}

#[test]
fn e2e_search_shard_2() {
    let _report = coverage::Report::new("shard-2");
    search(Config::shard(2));
}

#[test]
fn e2e_search_shard_3() {
    let _report = coverage::Report::new("shard-3");
    search(Config::shard(3));
}
