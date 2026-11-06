//! Repo config stays local, including the keys that control rewriting and Git pushes.

use crate::fixture::Fixture;

#[test]
fn repo_config_stays_local() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let key = r#"revset-aliases."immutable_heads()""#;
    hive.repo(0).jj(&["config", "set", "--repo", key, "none()"]);
    hive.repo(0)
        .jj(&["config", "set", "--repo", "git.private-commits", "'alpha'"]);
    hive.repo(1)
        .jj(&["config", "set", "--repo", "git.private-commits", "'beta'"]);
    hive.repo(1)
        .jj(&["config", "set", "--repo", "aliases.mine", "['log']"]);
    let before: Vec<Vec<u8>> = (0..2)
        .map(|i| std::fs::read(hive.repo(i).repo_config_path()).unwrap())
        .collect();
    hive.sync();
    hive.reopen(0);
    hive.reopen(1);
    hive.sync();
    hive.assert_converged();
    for (i, expected) in before.iter().enumerate() {
        assert_eq!(
            &std::fs::read(hive.repo(i).repo_config_path()).unwrap(),
            expected
        );
    }
    hive.repo(0)
        .jj(&["config", "unset", "--repo", "git.private-commits"]);
    hive.sync();
    assert_eq!(
        hive.repo(1).jj(&["config", "get", "git.private-commits"]),
        "beta\n"
    );
}
