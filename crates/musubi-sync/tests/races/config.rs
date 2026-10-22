//! jj repo config the hive shares (docs/design.md, "Hive settings").

use crate::fixture::Fixture;

const IMMUTABLE_HEADS: &str = r#"revset-aliases."immutable_heads()""#;

fn get(hive: &Fixture, index: usize, key: &str) -> Option<String> {
    let output = hive.repo(index).jj_output(&["config", "get", key]);
    output
        .status
        .success()
        .then(|| String::from_utf8(output.stdout).unwrap())
}

/// Settings that decide what may be rewritten must agree everywhere: one machine's change
/// reaches the others, and so does unsetting it.
#[test]
fn shared_config_reaches_every_machine() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let value = "builtin_immutable_heads() | description(glob:'release*')";
    hive.repo(0)
        .jj(&["config", "set", "--repo", IMMUTABLE_HEADS, value]);
    hive.sync();
    assert_eq!(get(&hive, 1, IMMUTABLE_HEADS), Some(format!("{value}\n")));
    hive.repo(1)
        .jj(&["config", "unset", "--repo", IMMUTABLE_HEADS]);
    hive.sync();
    hive.assert_converged();
    // Unset, jj's default applies again.
    assert_eq!(
        get(&hive, 0, IMMUTABLE_HEADS),
        Some("builtin_immutable_heads()\n".to_owned())
    );
}

/// Other repo config is each machine's own, unless `musubi.shared-config` names it.
#[test]
fn other_config_is_shared_only_when_named() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.repo(0)
        .jj(&["config", "set", "--repo", "aliases.mine", "['log']"]);
    hive.sync();
    assert_eq!(get(&hive, 1, "aliases.mine"), None);
    hive.repo(0).jj(&[
        "config",
        "set",
        "--repo",
        "musubi.shared-config",
        "['aliases.mine']",
    ]);
    hive.sync();
    hive.assert_converged();
    // Written as musubi normalizes TOML values.
    assert_eq!(
        get(&hive, 1, "aliases.mine"),
        Some("[\"log\"]\n".to_owned())
    );
}

/// Two machines set a shared key differently at once: they end up agreeing.
#[test]
fn shared_config_set_on_two_machines_at_once() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.repo(0)
        .jj(&["config", "set", "--repo", "git.private-commits", "'wip'"]);
    hive.repo(1)
        .jj(&["config", "set", "--repo", "git.private-commits", "'secret'"]);
    hive.sync();
    hive.assert_converged();
    // beta's write is the later.
    let expected = Some("secret\n".to_owned());
    assert_eq!(get(&hive, 0, "git.private-commits"), expected);
    assert_eq!(get(&hive, 1, "git.private-commits"), expected);
}

/// What each machine and the hive last agreed on is written again only when a setting
/// changes, not at every sync that brings operations: ext4 writes out at once a file that
/// replaces another.
#[cfg(unix)]
#[test]
fn settings_state_is_rewritten_only_for_settings() {
    use std::os::unix::fs::MetadataExt as _;
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let state = |hive: &Fixture, index: usize, name: &str| {
        hive.repo(index).repo_path().join("musubi").join(name)
    };
    // A link keeps the file's inode, so that a replacement can't be given it.
    for index in 0..2 {
        let state = |name| state(&hive, index, name);
        std::fs::hard_link(state("settings.json"), state("settings.before")).unwrap();
    }
    let replaced = |hive: &Fixture| {
        (0..2)
            .map(|index| {
                let inode = |name| std::fs::metadata(state(hive, index, name)).unwrap().ino();
                inode("settings.json") != inode("settings.before")
            })
            .collect::<Vec<_>>()
    };
    hive.commit(0, "f", "one");
    hive.commit(1, "g", "two");
    hive.sync();
    assert_eq!(replaced(&hive), [false, false]);
    hive.repo(0)
        .jj(&["config", "set", "--repo", "git.private-commits", "'wip'"]);
    hive.sync();
    assert_eq!(replaced(&hive), [true, true]);
}
