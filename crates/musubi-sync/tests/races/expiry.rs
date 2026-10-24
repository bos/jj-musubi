//! Forgetting copies that go unused (docs/internals/races.md, "Copies that go away"): each
//! copy records its `musubi.forget-after`, and a daemon forgets one whose latest work is older.

use std::time::Duration;
use std::time::SystemTime;

use crate::fixture::Fixture;

const HOUR: Duration = Duration::from_secs(3600);

/// Sets `musubi.forget-after` in machine `index`'s repo config, as `musubi join` does.
fn set_forget_after(hive: &Fixture, index: usize, value: &str) {
    hive.repo(index)
        .jj(&["config", "set", "--repo", "musubi.forget-after", value]);
}

/// A copy that records `musubi.forget-after` is forgotten once unused for longer, by any
/// other machine's daemon, and comes back with its next work. One that records nothing is
/// never forgotten, nor is a machine's own copy by its own daemon.
#[test]
fn unused_copies_are_forgotten_after_their_forget_after() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    let beta = hive.machine_key(1);
    let gamma = hive.machine_key(2);
    set_forget_after(&hive, 0, "1h");
    set_forget_after(&hive, 1, "1h");
    hive.sync();
    hive.sync();
    let activity = hive.node(0).activity().unwrap();
    let after = |key: &str| {
        activity
            .iter()
            .find(|copy| copy.key == key)
            .map(|copy| copy.forget_after)
    };
    assert_eq!(after(&beta), Some(Some(HOUR)));
    assert_eq!(after(&gamma), Some(None));

    let now = SystemTime::now();
    assert!(
        hive.node(0)
            .expire_idle(now, Duration::ZERO)
            .unwrap()
            .is_empty()
    );
    // alpha's own copy, set to 1h too, isn't its own daemon's to forget.
    let forgotten = hive
        .node(0)
        .expire_idle(now + 2 * HOUR, Duration::ZERO)
        .unwrap();
    assert_eq!(forgotten, ["beta"]);
    hive.sync();
    assert!(!hive.shown_machines().contains(&beta));
    assert!(hive.shown_machines().contains(&gamma));
    assert!(!hive.workspace_names(0).contains("beta/beta"));
    // A year on, gamma forgets alpha, set to 1h, and never gamma, which recorded nothing.
    let later = now + 365 * 24 * HOUR;
    assert_eq!(
        hive.node(2).expire_idle(later, Duration::ZERO).unwrap(),
        ["alpha"]
    );
    hive.sync();
    assert!(
        hive.node(0)
            .expire_idle(later, Duration::ZERO)
            .unwrap()
            .is_empty()
    );

    hive.commit(1, "b", "beta again");
    hive.sync();
    assert!(hive.shown_machines().contains(&beta));
    hive.assert_converged();
}

/// Changing a copy's `musubi.forget-after` is its work: recorded, it shows the copy again,
/// and the copy is forgotten by the new value.
#[test]
fn changing_forget_after_is_work() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let beta = hive.machine_key(1);
    set_forget_after(&hive, 1, "1h");
    hive.sync();
    let now = SystemTime::now();
    assert_eq!(
        hive.node(0)
            .expire_idle(now + 2 * HOUR, Duration::ZERO)
            .unwrap(),
        ["beta"]
    );
    hive.sync();
    assert!(!hive.shown_machines().contains(&beta));
    set_forget_after(&hive, 1, "never");
    hive.sync();
    hive.sync();
    assert!(hive.shown_machines().contains(&beta));
    assert!(
        hive.node(0)
            .expire_idle(now + 24 * HOUR, Duration::ZERO)
            .unwrap()
            .is_empty()
    );
    hive.assert_converged();
}
