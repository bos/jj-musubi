//! The Antithesis workload's driver for musubi (antithesis/README.md).
//!
//! Three machines, `m1` to `m3`, each run musubi's daemon on a colocated jj repository at
//! `/root/repo`, syncing through the hub on `hub` over ssh. The driver is the user at all three:
//! it runs jj and musubi commands on them over ssh, one command at a time on each machine, as
//! a person typing would, while the daemons sync in the background. It records every commit a
//! command made, and an eventually checks, once faults stop, that the machines converge on
//! one history and that every recorded commit reached every machine.

mod remote;
mod workload;

use std::time::Duration;
use std::time::Instant;

use antithesis_instrumentation as _;
use hegel::TestCase;
use hegel::stateful::machine;

use crate::remote::Outcome;
use crate::workload::Workload;

/// Where every machine keeps its copy.
pub const REPO: &str = "/root/repo";

fn main_setup() -> Workload {
    antithesis_sdk::antithesis_init();
    let workload = Workload::from_env();
    setup(&workload);
    antithesis_sdk::lifecycle::setup_complete(&serde_json::json!({
        "machines": workload.machines,
    }));
    eprintln!("setup complete; waiting for /workload-active");
    while !std::path::Path::new("/workload-active").exists() {
        std::thread::sleep(Duration::from_millis(100));
    }
    antithesis_sdk::assert_reachable!("the workload starts");
    workload
}

#[hegel::main(phases = [hegel::Phase::Generate])]
fn main(tc: TestCase) {
    // Setup runs once, before hegel draws anything: `main` runs exactly one test case.
    let workload = main_setup();
    workload.start();
    machine(workload)
        .steps(i64::MAX)
        .min_concurrency(1)
        .max_concurrency(4)
        .run_concurrent(tc);
}

/// Prints `what` when it differs from the last thing printed this way, so a wait that
/// stalls says where without flooding the log.
struct Said(String);

impl Said {
    fn say(&mut self, what: String) {
        if what != self.0 {
            eprintln!("setup: {what}");
            self.0 = what;
        }
    }
}

/// Runs `script` on `host` until it succeeds, saying why it doesn't.
fn until_ok(host: &str, script: &str, said: &mut Said) -> String {
    loop {
        match remote::run(host, script, Duration::from_secs(120)) {
            Outcome::Ok { stdout, .. } => return stdout,
            other => said.say(format!("{host}: `{script}`: {}", other.describe())),
        }
        std::thread::sleep(Duration::from_millis(500));
    }
}

/// Makes the hive: a repository with one commit on the first machine, a hive of it on the
/// hub, and clones of it on the others. Every step can run again after a partial attempt.
fn setup(workload: &Workload) {
    let mut said = Said(String::new());
    let started = Instant::now();
    // Every machine's daemon runs: a musubi command run before it does would start one in
    // the background, and the container's own would then refuse to start.
    for host in &workload.machines {
        loop {
            let out = until_ok(host, "musubi status -T 'daemon_running'", &mut said);
            if out.trim() == "true" {
                break;
            }
            said.say(format!("{host}: the daemon isn't running yet"));
            std::thread::sleep(Duration::from_millis(500));
        }
    }
    let first = &workload.machines[0];
    until_ok(
        first,
        &format!(
            "set -e; mkdir -p {REPO}; cd {REPO}; \
             [ -d .jj ] || jj git init --colocate; \
             if ! jj log --no-graph -r main -T '' >/dev/null 2>&1; then \
               echo init > README; jj commit -m init; jj bookmark set main -r @-; \
             fi"
        ),
        &mut said,
    );
    let hub = &workload.hub;
    until_ok(
        first,
        &format!(
            "cd {REPO}; [ -n \"$(musubi status -T hive)\" ] || musubi create --hub {hub} 2>&1"
        ),
        &mut said,
    );
    for host in &workload.machines[1..] {
        until_ok(
            host,
            &format!(
                "[ -d {REPO}/.jj ] && cd {REPO} && [ -n \"$(musubi status -T hive)\" ] || \
                 {{ rm -rf {REPO}; musubi clone repo {REPO} --hub {hub} 2>&1; }}"
            ),
            &mut said,
        );
    }
    // Every copy has synced: the same head, all its work sent.
    loop {
        let statuses: Vec<_> = workload
            .machines
            .iter()
            .map(|host| workload::status(host))
            .collect();
        if let Some(first) = statuses[0].as_ref()
            && statuses.iter().all(|status| {
                status
                    .as_ref()
                    .is_some_and(|s| s.sent && s.problem.is_empty() && s.head == first.head)
            })
        {
            break;
        }
        said.say(format!("waiting for the copies to sync: {statuses:?}"));
        std::thread::sleep(Duration::from_millis(500));
    }
    eprintln!("setup took {:?}", started.elapsed());
}
