//! Git remotes: fetches and pushes on different machines.

use std::path::PathBuf;

use musubi_testutil::TestEnv;

use crate::fixture::Fixture;

/// A bare `origin` with one commit on `main`, and each machine configured to use it.
fn with_origin(hive: &Fixture) -> PathBuf {
    let seed = create_origin(hive);
    let origin = hive.env.root().join("origin.git");
    for repo in &hive.repos {
        repo.jj(&["git", "remote", "add", "origin", origin.to_str().unwrap()]);
    }
    seed
}

/// A bare `origin` with one commit on `main`; returns the clone that seeded it.
pub fn create_origin(hive: &Fixture) -> PathBuf {
    let origin = hive.env.root().join("origin.git");
    let seed = hive.env.root().join("seed");
    std::fs::create_dir_all(&seed).unwrap();
    seed_git(
        hive,
        hive.env.root(),
        &[
            "init",
            "--quiet",
            "--bare",
            "--initial-branch=main",
            origin.to_str().unwrap(),
        ],
    );
    seed_git(hive, &seed, &["init", "--quiet", "--initial-branch=main"]);
    std::fs::write(seed.join("upstream"), "upstream 1").unwrap();
    seed_git(hive, &seed, &["add", "."]);
    seed_git(hive, &seed, &["commit", "--quiet", "-m", "upstream 1"]);
    seed_git(
        hive,
        &seed,
        &["push", "--quiet", origin.to_str().unwrap(), "main"],
    );
    seed
}

fn remotes(hive: &Fixture, index: usize) -> String {
    hive.repo(index).jj(&["git", "remote", "list"])
}

/// A remote added on one machine is added on every machine, so any machine can fetch it.
#[test]
fn remote_added_on_one_machine_reaches_the_others() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    create_origin(&hive);
    let origin = hive.env.root().join("origin.git");
    hive.repo(0)
        .jj(&["git", "remote", "add", "origin", origin.to_str().unwrap()]);
    hive.sync();
    assert_eq!(remotes(&hive, 1), remotes(&hive, 0));
    hive.repo(1).jj(&["git", "fetch"]);
    hive.sync();
    hive.assert_converged();
    assert!(hive.bookmarks(0).contains_key("main@origin"));
}

/// Renaming or removing a remote on one machine does it on every machine, as jj renames
/// or forgets its remote bookmarks everywhere.
#[test]
fn remote_renamed_and_removed_everywhere() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    with_origin(&hive);
    hive.repo(0).jj(&["git", "fetch"]);
    hive.sync();
    hive.repo(0)
        .jj(&["git", "remote", "rename", "origin", "upstream"]);
    hive.sync();
    hive.assert_converged();
    assert_eq!(remotes(&hive, 1), remotes(&hive, 0));
    assert!(
        remotes(&hive, 1).starts_with("upstream "),
        "{}",
        remotes(&hive, 1)
    );
    hive.repo(1).jj(&["git", "fetch", "--remote", "upstream"]);
    hive.sync();
    hive.assert_converged();
    assert!(hive.bookmarks(0).contains_key("main@upstream"));
    hive.repo(1).jj(&["git", "remote", "remove", "upstream"]);
    hive.sync();
    hive.assert_converged();
    assert_eq!(remotes(&hive, 0), "");
}

/// Two machines point a remote at different URLs at once: the later one wins everywhere.
#[test]
fn remote_changed_on_two_machines_at_once() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.repo(0).jj(&[
        "git",
        "remote",
        "add",
        "origin",
        "https://example.com/one.git",
    ]);
    hive.sync();
    hive.repo(0).jj(&[
        "git",
        "remote",
        "set-url",
        "origin",
        "https://example.com/two.git",
    ]);
    hive.repo(1).jj(&[
        "git",
        "remote",
        "set-url",
        "origin",
        "https://example.com/three.git",
    ]);
    hive.sync();
    hive.assert_converged();
    let expected = "origin https://example.com/three.git\n";
    assert_eq!(remotes(&hive, 0), expected);
    assert_eq!(remotes(&hive, 1), expected);
}

/// A machine upgrading from before writes were timed, which last applied a remote that the
/// hive has since removed (leaving no record of the removal, as the untimed version
/// didn't), removes it too, rather than bringing it back, and keeps its own new ones.
#[test]
fn an_upgraded_machine_takes_removals_made_before_times() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.sync();
    let beta = hive.repo(1);
    beta.jj(&[
        "git",
        "remote",
        "add",
        "gone",
        "https://example.com/gone.git",
    ]);
    // beta's settings state as the untimed version left it, having applied `gone`.
    let state = beta.repo_path().join("musubi/settings.json");
    let mut json: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&state).unwrap()).unwrap();
    json["settings"]["remotes"] =
        serde_json::json!({"gone": {"url": "https://example.com/gone.git"}});
    std::fs::write(&state, serde_json::to_vec(&json).unwrap()).unwrap();
    beta.jj(&[
        "git",
        "remote",
        "add",
        "mine",
        "https://example.com/mine.git",
    ]);
    hive.sync();
    hive.assert_converged();
    let expected = "mine https://example.com/mine.git\n";
    assert_eq!(remotes(&hive, 0), expected);
    assert_eq!(remotes(&hive, 1), expected);
}

/// A joining machine keeps its own remotes, even one by a name the hive once removed.
#[test]
fn a_joining_machine_keeps_a_remote_the_hive_removed() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    alpha.jj(&[
        "git",
        "remote",
        "add",
        "extra",
        "https://example.com/old.git",
    ]);
    // beta has its remote from before the hive removed one by that name.
    let beta = env.init_repo("beta");
    beta.jj(&[
        "git",
        "remote",
        "add",
        "extra",
        "https://example.com/new.git",
    ]);
    let mut hive = Fixture::join(env, vec![alpha]);
    hive.repo(0).jj(&["git", "remote", "remove", "extra"]);
    hive.sync();
    hive.add(beta);
    hive.sync();
    hive.assert_converged();
    let expected = "extra https://example.com/new.git\n";
    assert_eq!(remotes(&hive, 0), expected);
    assert_eq!(remotes(&hive, 1), expected);
}

/// One machine points a remote elsewhere while another gives it a push URL: two writes to
/// the remote, and the later one wins, whichever reaches the hub first, whichever machine
/// makes the merge, and whatever either does meanwhile.
fn conflicting_changes_to_a_remote(beta_first: bool, beta_works_on: bool) -> String {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.repo(0).jj(&["git", "remote", "add", "origin", ONE]);
    hive.sync();
    let alpha_changes = |hive: &mut Fixture| {
        hive.repo(0)
            .jj(&["git", "remote", "set-url", "origin", MOVED]);
        hive.hive.sync(0).unwrap();
    };
    if !beta_first {
        alpha_changes(&mut hive);
    }
    // beta, offline, records its change, and reaches the hub last.
    hive.repo(1)
        .git(&["config", "remote.origin.pushurl", MIRROR]);
    assert!(hive.hive.record_settings(1).unwrap());
    if beta_first {
        alpha_changes(&mut hive);
    }
    if beta_works_on {
        hive.commit(1, "b", "beta works on");
    }
    hive.sync();
    hive.assert_converged();
    assert_eq!(remotes(&hive, 0), remotes(&hive, 1));
    remotes(&hive, 0)
}

const ONE: &str = "https://example.com/one.git";
const MOVED: &str = "https://example.com/moved.git";
const MIRROR: &str = "https://example.com/mirror.git";

/// The later change wins, though it reaches the hub first.
#[test]
fn the_later_change_to_a_remote_wins() {
    assert_eq!(
        conflicting_changes_to_a_remote(true, false),
        format!("origin {MOVED}\n")
    );
}

/// The later change wins when it reaches the hub last, too.
#[test]
fn the_later_change_wins_reaching_the_hub_last() {
    assert_eq!(
        conflicting_changes_to_a_remote(false, false),
        format!("origin {ONE} (push: {MIRROR})\n")
    );
}

/// Working on after the earlier change doesn't make it win.
#[test]
fn working_on_after_the_earlier_change_makes_no_difference() {
    assert_eq!(
        conflicting_changes_to_a_remote(true, true),
        format!("origin {MOVED}\n")
    );
}

/// A machine that joins adds its own remotes to the hive's, but takes the hive's where
/// both have a remote of the same name pointing to different repositories.
#[test]
fn joining_machine_merges_its_remotes_with_the_hives() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    alpha.jj(&[
        "git",
        "remote",
        "add",
        "origin",
        "https://example.com/hive.git",
    ]);
    beta.jj(&[
        "git",
        "remote",
        "add",
        "origin",
        "https://example.com/beta.git",
    ]);
    beta.jj(&[
        "git",
        "remote",
        "add",
        "extra",
        "https://example.com/extra.git",
    ]);
    let mut hive = Fixture::join(env, vec![alpha, beta]);
    hive.sync();
    hive.assert_converged();
    let expected = "extra https://example.com/extra.git\norigin https://example.com/hive.git\n";
    assert_eq!(remotes(&hive, 0), expected);
    assert_eq!(remotes(&hive, 1), expected);
}

/// Machines that reach one repository by different URLs, over https and ssh, say, each
/// keep their own, joining or later: only a change to where a remote points replicates.
#[test]
fn machines_keep_their_own_spelling_of_a_shared_remote() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    let https = "https://example.com/team/project.git";
    let ssh = "git@example.com:team/project";
    alpha.jj(&["git", "remote", "add", "origin", https]);
    beta.jj(&["git", "remote", "add", "origin", ssh]);
    let mut hive = Fixture::join(env, vec![alpha, beta]);
    hive.sync();
    hive.assert_converged();
    assert_eq!(remotes(&hive, 0), format!("origin {https}\n"));
    assert_eq!(remotes(&hive, 1), format!("origin {ssh}\n"));
    // Respelling it is still nobody else's business.
    let respelled = "ssh://git@example.com/team/project.git";
    hive.repo(1)
        .jj(&["git", "remote", "set-url", "origin", respelled]);
    hive.sync();
    hive.sync();
    assert_eq!(remotes(&hive, 0), format!("origin {https}\n"));
    assert_eq!(remotes(&hive, 1), format!("origin {respelled}\n"));
    // Pointing it elsewhere is everybody's.
    let moved = "https://example.com/team/moved.git";
    hive.repo(1)
        .jj(&["git", "remote", "set-url", "origin", moved]);
    hive.sync();
    hive.sync();
    hive.assert_converged();
    assert_eq!(remotes(&hive, 0), format!("origin {moved}\n"));
    assert_eq!(remotes(&hive, 1), format!("origin {moved}\n"));
}

/// The same, when the machine whose spelling the hive has changes the remote: the other
/// machine takes each change, keeping its own spelling of whatever still names the same
/// repository.
#[test]
fn changes_to_a_remote_reach_machines_with_their_own_spelling() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    let https = "https://example.com/team/project.git";
    let ssh = "git@example.com:team/project";
    alpha.jj(&["git", "remote", "add", "origin", https]);
    beta.jj(&["git", "remote", "add", "origin", ssh]);
    let mut hive = Fixture::join(env, vec![alpha, beta]);
    hive.sync();
    // A push URL for another repository replicates; beta keeps its fetch URL.
    let mirror = "git@example.com:team/mirror";
    hive.repo(0)
        .git(&["config", "remote.origin.pushurl", mirror]);
    hive.sync();
    hive.sync();
    assert_eq!(
        remotes(&hive, 1),
        format!("origin {ssh} (push: {mirror})\n")
    );
    // A rename moves beta's remote, with its own spelling and remote-tracking refs.
    // jj won't rename a remote with a push URL; git will.
    hive.repo(0)
        .git(&["remote", "rename", "origin", "upstream"]);
    hive.sync();
    hive.sync();
    assert_eq!(
        remotes(&hive, 0),
        format!("upstream {https} (push: {mirror})\n")
    );
    assert_eq!(
        remotes(&hive, 1),
        format!("upstream {ssh} (push: {mirror})\n")
    );
    // Pointing it elsewhere moves beta too.
    let moved = "https://example.com/team/moved.git";
    hive.repo(0)
        .jj(&["git", "remote", "set-url", "upstream", moved]);
    hive.sync();
    hive.sync();
    hive.assert_converged();
    let expected = format!("upstream {moved} (push: {mirror})\n");
    assert_eq!(remotes(&hive, 0), expected);
    assert_eq!(remotes(&hive, 1), expected);
}

/// Two machines that reach one repository by different URLs, already synced.
fn spelled_two_ways(beta_push_url: Option<&str>) -> Fixture {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    alpha.jj(&["git", "remote", "add", "origin", HTTPS]);
    beta.jj(&["git", "remote", "add", "origin", SSH]);
    if let Some(push_url) = beta_push_url {
        beta.git(&["config", "remote.origin.pushurl", push_url]);
    }
    let mut hive = Fixture::join(env, vec![alpha, beta]);
    hive.sync();
    hive
}

const HTTPS: &str = "https://example.com/team/project.git";
const SSH: &str = "git@example.com:team/project";

/// A machine that fetches over https and pushes over ssh to the same repository drops its
/// push URL when the remote moves, rather than pushing to where it used to point.
#[test]
fn a_push_url_to_the_old_repository_goes_when_the_remote_moves() {
    let mut hive = spelled_two_ways(Some(SSH));
    let push_url = |hive: &Fixture| {
        hive.repo(1)
            .git(&["config", "--default", "", "--get", "remote.origin.pushurl"])
            .trim()
            .to_owned()
    };
    assert_eq!(push_url(&hive), SSH);
    let moved = "https://example.com/team/moved.git";
    hive.repo(0)
        .jj(&["git", "remote", "set-url", "origin", moved]);
    hive.sync();
    hive.sync();
    hive.assert_converged();
    assert_eq!(remotes(&hive, 0), format!("origin {moved}\n"));
    assert_eq!(remotes(&hive, 1), format!("origin {moved}\n"));
    assert_eq!(push_url(&hive), "");
}

/// A rename on the machine whose spelling the hive doesn't have renames the others' remote,
/// spelled as they spell it, rather than replacing it with the renamer's.
#[test]
fn a_rename_keeps_each_machines_spelling() {
    let mut hive = spelled_two_ways(None);
    hive.repo(1)
        .jj(&["git", "remote", "rename", "origin", "upstream"]);
    hive.sync();
    hive.sync();
    hive.assert_converged();
    assert_eq!(remotes(&hive, 0), format!("upstream {HTTPS}\n"));
    assert_eq!(remotes(&hive, 1), format!("upstream {SSH}\n"));
}

/// A machine that misses several changes, among them a respelling of what it last agreed
/// to, takes them all rather than reverting the last.
#[test]
fn a_machine_that_lags_behind_respellings_takes_later_changes() {
    let mut hive = spelled_two_ways(None);
    let alpha = |hive: &mut Fixture, args: &[&str]| {
        hive.repo(0).git(args);
        hive.hive.sync(0).unwrap();
    };
    alpha(
        &mut hive,
        &[
            "remote",
            "set-url",
            "origin",
            "https://example.com/team/q.git",
        ],
    );
    alpha(
        &mut hive,
        &[
            "remote",
            "set-url",
            "origin",
            "ssh://git@example.com/team/project.git",
        ],
    );
    let mirror = "git@example.com:team/mirror";
    alpha(&mut hive, &["config", "remote.origin.pushurl", mirror]);
    hive.sync();
    hive.sync();
    hive.assert_converged();
    assert_eq!(
        remotes(&hive, 0),
        format!("origin ssh://git@example.com/team/project.git (push: {mirror})\n")
    );
    assert_eq!(
        remotes(&hive, 1),
        format!("origin {SSH} (push: {mirror})\n")
    );
}

/// Runs `git` in `dir`, such as the clone that seeds origin, as origin's author, in the
/// tests' hermetic environment.
pub fn seed_git(hive: &Fixture, dir: &std::path::Path, args: &[&str]) {
    let out = hive
        .repo(0)
        .program(std::path::Path::new("git"))
        .current_dir(dir)
        .args(args)
        .env("GIT_AUTHOR_NAME", "o")
        .env("GIT_AUTHOR_EMAIL", "o@example.com")
        .env("GIT_COMMITTER_NAME", "o")
        .env("GIT_COMMITTER_EMAIL", "o@example.com")
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "git {args:?}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

fn advance_origin(hive: &Fixture, seed: &std::path::Path, n: usize) {
    let origin = hive.env.root().join("origin.git");
    let run = |args: &[&str]| seed_git(hive, seed, args);
    std::fs::write(seed.join("upstream"), format!("upstream {n}")).unwrap();
    run(&["commit", "--quiet", "-am", &format!("upstream {n}")]);
    run(&["push", "--quiet", origin.to_str().unwrap(), "main"]);
}

/// One machine fetches; the other sees the remote bookmark, and its own git gets the
/// matching remote-tracking ref.
#[test]
fn fetch_on_one_machine_reaches_the_other() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let _seed = with_origin(&hive);
    hive.repo(0).jj(&["git", "fetch"]);
    hive.sync();
    hive.assert_converged();
    let fetched = hive.bookmarks(0)["main@origin"].clone();
    assert_eq!(hive.bookmarks(1)["main@origin"], fetched);
    assert_eq!(
        hive.repo(1)
            .git(&["rev-parse", "refs/remotes/origin/main"])
            .trim(),
        fetched
    );
}

/// Both machines fetch, at different moments, while origin moves between the fetches.
/// The later fetch descends from the earlier one, so jj resolves the remote bookmark to the
/// newer commit rather than a conflict.
#[test]
fn concurrent_fetches_of_a_moving_remote() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let seed = with_origin(&hive);
    hive.repo(0).jj(&["git", "fetch"]);
    advance_origin(&hive, &seed, 2);
    hive.repo(1).jj(&["git", "fetch"]);
    hive.sync();
    hive.assert_converged();
    let main = &hive.bookmarks(0)["main@origin"];
    assert!(!main.starts_with("conflict:"), "{main}");
    let newest = hive.repo(1).git(&["rev-parse", "refs/remotes/origin/main"]);
    assert_eq!(main, newest.trim());
}

/// One machine pushes a bookmark; the other sees it tracked and pushed.
#[test]
fn push_from_one_machine() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let _seed = with_origin(&hive);
    hive.repo(0).jj(&["git", "fetch"]);
    hive.repo(0).jj(&["new", "main@origin"]);
    hive.commit(0, "feature", "feature");
    hive.repo(0)
        .jj(&["bookmark", "create", "feature", "-r", "@-"]);
    hive.repo(0).jj(&["git", "push", "--bookmark", "feature"]);
    hive.sync();
    hive.assert_converged();
    let feature = hive.commit_id(1, "feature");
    assert_eq!(hive.bookmarks(1)["feature@origin"], feature);
}

/// Whether remote bookmark `symbol` (`main@origin`) is tracked on machine `index`.
fn tracked(hive: &Fixture, index: usize, symbol: &str) -> bool {
    let template = r#"if(remote, name ++ "@" ++ remote ++ " " ++ if(tracked, "tracked", "untracked") ++ "\n")"#;
    let list = hive
        .repo(index)
        .jj(&["bookmark", "list", "--all-remotes", "-T", template]);
    list.lines()
        .find_map(|line| line.strip_prefix(symbol)?.strip_prefix(' '))
        == Some("tracked")
}

/// One machine stops tracking a remote bookmark; every machine stops, so a later fetch on
/// any of them moves the remote bookmark but leaves the local one where it was.
#[test]
fn untracking_a_remote_bookmark_reaches_every_machine() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let seed = with_origin(&hive);
    hive.repo(0).jj(&["git", "fetch"]);
    hive.repo(0).jj(&["bookmark", "track", "main@origin"]);
    hive.sync();
    hive.assert_converged();
    assert!(tracked(&hive, 1, "main@origin"));
    let upstream = hive.bookmarks(1)["main@"].clone();

    hive.repo(0).jj(&["bookmark", "untrack", "main@origin"]);
    hive.sync();
    assert!(!tracked(&hive, 1, "main@origin"));
    advance_origin(&hive, &seed, 2);
    hive.repo(1).jj(&["git", "fetch"]);
    hive.sync();
    hive.assert_converged();
    for index in [0, 1] {
        let bookmarks = hive.bookmarks(index);
        assert_eq!(bookmarks["main@"], upstream, "local main on {index}");
        assert_ne!(bookmarks["main@origin"], upstream, "main@origin on {index}");
        assert!(!tracked(&hive, index, "main@origin"), "{index}");
    }
}

/// A `file://` URL for `path`, as git takes one on any platform.
fn file_url(path: &std::path::Path) -> String {
    let path = path.to_string_lossy().replace('\\', "/");
    format!(
        "file://{}{path}",
        if path.starts_with('/') { "" } else { "/" }
    )
}

/// Whether any file under `dir` holds `needle`.
fn holds(dir: &std::path::Path, needle: &[u8]) -> bool {
    std::fs::read_dir(dir).unwrap().flatten().any(|entry| {
        let path = entry.path();
        if path.is_dir() {
            holds(&path, needle)
        } else {
            let bytes = std::fs::read(&path).unwrap_or_default();
            bytes.windows(needle.len()).any(|window| window == needle)
        }
    })
}

/// Remotes reach other machines as written and as git expands them through the writing
/// machine's `url.<base>.insteadOf` aliases (#34). A machine with the same alias keeps the
/// alias, one without it gets the expansion, and the writing machine keeps its own spelling.
/// Credentials in an https URL stay on their machine, and never reach the hub or another
/// machine (#33).
#[test]
fn remotes_go_as_written_and_as_expanded() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    let _seed = create_origin(&hive);
    let root = file_url(hive.env.root());
    // An alias alpha and beta have, in their own repositories' git config, and gamma lacks.
    for index in [0, 1] {
        hive.repo(index)
            .git(&["config", &format!("url.{root}/.insteadOf"), "musubi-test:"]);
    }
    let alpha = hive.repo(0);
    alpha.jj(&["git", "remote", "add", "origin", "musubi-test:origin.git"]);
    alpha.git(&["config", "remote.origin.pushurl", "musubi-test:origin.git"]);
    let token = "https://alpha:secret@example.com/team/backup.git";
    alpha.jj(&["git", "remote", "add", "backup", token]);
    // A redirect only alpha has, to a mirror: the others go where alpha's git does.
    alpha.git(&[
        "config",
        "url.https://mirror.example/.insteadOf",
        "https://example.com/",
    ]);
    alpha.jj(&[
        "git",
        "remote",
        "add",
        "upstream",
        "https://example.com/team/real",
    ]);
    hive.sync();
    hive.assert_converged();
    // As their git config spells them: jj shows URLs after git's aliases.
    let url = |index: usize, name: &str| {
        hive.repo(index)
            .git(&["config", &format!("remote.{name}.url")])
    };
    assert_eq!(url(0, "origin"), "musubi-test:origin.git\n");
    assert_eq!(url(0, "backup"), format!("{token}\n"));
    assert_eq!(url(1, "origin"), "musubi-test:origin.git\n");
    assert_eq!(url(2, "origin"), format!("{root}/origin.git\n"));
    let push = |index: usize| hive.repo(index).git(&["config", "remote.origin.pushurl"]);
    assert_eq!(push(1), "musubi-test:origin.git\n");
    assert_eq!(push(2), format!("{root}/origin.git\n"));
    let mirror = "https://mirror.example/team/real\n";
    assert_eq!(url(0, "upstream"), "https://example.com/team/real\n");
    assert_eq!(
        (url(1, "upstream"), url(2, "upstream")),
        (mirror.into(), mirror.into())
    );
    let stripped = "https://example.com/team/backup.git\n";
    assert_eq!(
        (url(1, "backup"), url(2, "backup")),
        (stripped.into(), stripped.into())
    );
    for index in [1, 2] {
        hive.repo(index).jj(&["git", "fetch", "--remote", "origin"]);
    }
    // Nor in the command that added the remote, which jj records with the operation.
    assert!(!holds(&hive.env.root().join("hub"), b"secret"));
    for index in [1, 2] {
        assert!(!holds(&hive.repo(index).path().join(".jj"), b"secret"));
    }
}

/// Two repositories created independently, each with a `main` at a different commit,
/// joining one hive: jj merges the histories at the root, and `main` is conflicted until
/// someone resolves it.
#[test]
fn joining_repositories_with_conflicting_bookmarks() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    for (repo, name) in [(&alpha, "alpha"), (&beta, "beta")] {
        repo.write_file(name, name);
        repo.jj(&["commit", "-m", name]);
        repo.jj(&["bookmark", "create", "main", "-r", "@-"]);
    }
    let mut hive = Fixture::join(env, vec![alpha, beta]);
    hive.assert_converged();
    assert!(hive.bookmarks(0)["main@"].starts_with("conflict:"));
}

/// Force-pushes `main` on origin to a sibling of its current commit: a new commit on the
/// current commit's parent.
fn force_origin(hive: &Fixture, seed: &std::path::Path, n: usize) {
    let origin = hive.env.root().join("origin.git");
    let run = |args: &[&str]| seed_git(hive, seed, args);
    run(&["reset", "--quiet", "--hard", "HEAD~"]);
    std::fs::write(seed.join("upstream"), format!("upstream {n}")).unwrap();
    run(&["commit", "--quiet", "-am", &format!("upstream {n}")]);
    run(&[
        "push",
        "--quiet",
        "--force",
        origin.to_str().unwrap(),
        "main",
    ]);
}

/// `main@origin` as the machine's latest operation records it. `--ignore-working-copy`
/// keeps jj from importing git refs first, as any other `jj` command would.
fn recorded_main_at_origin(hive: &Fixture, index: usize) -> String {
    let template = r#"if(remote == "origin", if(conflict, "conflict", normal_target.commit_id()))"#;
    hive.repo(index).jj(&[
        "--ignore-working-copy",
        "bookmark",
        "list",
        "--all-remotes",
        "main",
        "-T",
        template,
    ])
}

/// Two machines fetch while origin is force-pushed between their fetches, so the hive's
/// `main@origin` is conflicted. A third machine's `.git` still has the
/// `refs/remotes/origin/main` of its own earlier fetch, and every `jj` command resolves a
/// conflicted remote bookmark to what `.git` has. musubi writes one of the conflict's sides
/// there, the same on every machine, so the hive settles on one of the two fetches rather
/// than on the older commit. With `stale_record`, the third machine's `.git` has the fetch
/// of that machine instead, disagreeing with jj's record of it, as after `jj op restore`.
fn conflicted_fetches(stale_record: Option<usize>) {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    let seed = with_origin(&hive);
    hive.repo(2).jj(&["git", "fetch"]);
    hive.sync();
    let first = recorded_main_at_origin(&hive, 2);
    advance_origin(&hive, &seed, 2);
    hive.repo(0).jj(&["git", "fetch"]);
    let alphas = recorded_main_at_origin(&hive, 0);
    force_origin(&hive, &seed, 3);
    hive.repo(1).jj(&["git", "fetch"]);
    let betas = recorded_main_at_origin(&hive, 1);
    if let Some(fetcher) = stale_record {
        // Behind jj's back: fetch that machine's commit into a scratch ref, then point
        // gamma's remote-tracking ref at it.
        let gamma = hive.repo(2);
        let fetched = recorded_main_at_origin(&hive, fetcher);
        gamma.git(&[
            "fetch",
            "--quiet",
            hive.repo(fetcher).path().to_str().unwrap(),
            "+refs/remotes/origin/main:refs/scratch/main",
        ]);
        gamma.git(&["update-ref", "refs/remotes/origin/main", &fetched]);
        gamma.git(&["update-ref", "-d", "refs/scratch/main"]);
    }
    hive.sync();
    for index in 0..3 {
        assert_eq!(
            recorded_main_at_origin(&hive, index),
            "conflict",
            "on {index}"
        );
    }
    let git_main = |index: usize| {
        hive.repo(index)
            .git(&["rev-parse", "refs/remotes/origin/main"])
            .trim()
            .to_owned()
    };
    let side = git_main(2);
    assert!(
        side == alphas || side == betas,
        "{side} is not a fetched side"
    );
    assert_ne!(side, first);
    for index in 0..3 {
        assert_eq!(git_main(index), side, "git on {index}");
        hive.repo(index).jj(&["status"]);
        assert_eq!(recorded_main_at_origin(&hive, index), side, "on {index}");
    }
    hive.sync();
    hive.assert_converged();
    for index in 0..3 {
        assert_eq!(recorded_main_at_origin(&hive, index), side, "on {index}");
    }
}

#[test]
fn conflicted_remote_bookmark_resolves_to_a_fetched_side() {
    conflicted_fetches(None);
}

/// One of these two has gamma's `.git` on the side musubi doesn't choose.
#[test]
fn conflicted_remote_bookmark_resolves_despite_a_stale_record() {
    conflicted_fetches(Some(0));
    conflicted_fetches(Some(1));
}

/// A remote with a push URL and no URL reaches the others as it is, with no URL, not an
/// empty one.
#[test]
fn a_remote_without_a_url_reaches_the_others_without_one() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.repo(0)
        .git(&["config", "remote.mirror.pushurl", MIRROR]);
    hive.sync();
    hive.assert_converged();
    let config = |key: &str| {
        hive.repo(1)
            .git(&["config", "--default", "-", "--get", key])
    };
    assert_eq!(config("remote.mirror.pushurl"), format!("{MIRROR}\n"));
    assert_eq!(config("remote.mirror.url"), "-\n");
}
