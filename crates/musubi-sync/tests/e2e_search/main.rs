//! Generated end-to-end tests (docs/internals/testing.md, "Generated end-to-end tests"): a Hegel
//! state machine drives two or three real colocated repositories, each a musubi node of an
//! in-process hive, through local `jj` work, workspaces, a shared `origin`, git-side work,
//! partial syncs, and faults, then syncs to a fixed point and checks that the hive
//! converged. The rules can reach every row of the race catalogue (docs/internals/races.md) but
//! the documented refusals; `coverage` maps rows to rules.
//!
//! After every rule, every op head of every repository a sync or fault touched loads,
//! every `jj` command and sync step must succeed, and no import of git refs or of git's HEAD
//! changes a ref that git didn't move, except where jj itself would (`imports`). At every full
//! convergence (`checks`):
//! the fixture's `assert_converged`; every node's canonical head is the hub's; every
//! operation is on every machine; tags agree; each machine has its own workspaces, at
//! visible commits; no divergence and no bookmark or tag conflict that jj wouldn't make of
//! the same operations in one repository (`reference`), nor the same rebase done twice
//! (`ledger`); and every machine shows the others' workspaces at their working copies, and
//! git never sees them.
//!
//! `e2e_smoke` runs in the default suite. The search, `e2e_search_shard_*`, runs with
//! `cargo nextest run -p musubi-sync --profile search`; each shard has its own example
//! database under `target/tmp/e2e_search/`, and the run writes which rules fired to
//! `target/tmp/e2e_search/coverage.txt` (printed with `--no-capture`). Environment:
//!
//! - `MUSUBI_SEARCH_CASES`: test cases per shard (default 8; a case takes up to a few minutes when
//!   four shards run at once);
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
    let started = std::time::Instant::now();
    let world = Rc::new(RefCell::new(World::new(setup)));
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
