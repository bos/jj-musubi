//! A hive of real repositories with an in-process hub.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::path::Path;

use musubi_jj::node::NodeRepo;
use musubi_jj::objects::Backend;
use musubi_sync::hive::Hive;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;

pub struct Fixture {
    pub env: TestEnv,
    pub repos: Vec<TestRepo>,
    pub hive: Hive,
}

impl Fixture {
    /// One colocated repository per name, each with its workspace named after it, all
    /// joined to a fresh hive and synced. Dozens of tests start from the same hive, so it is
    /// made once per build of the test binary for each set of names
    /// (`musubi_testutil::recorded`), and each test gets a copy, with nodes that know
    /// nothing of the hub yet, as after a restart.
    pub fn new(names: &[&str]) -> Self {
        let base = Path::new(env!("CARGO_TARGET_TMPDIR"));
        let name = format!("fixture-{}", names.join("-"));
        let saved = musubi_testutil::recorded(base, &name, |dir| {
            let env = TestEnv::new();
            let repos = names.iter().map(|name| env.init_repo(name)).collect();
            let Self { env, hive, .. } = Self::join(env, repos);
            // Its nodes finish writing what they realized as they close.
            drop(hive);
            env.save(dir);
        });
        let env = TestEnv::restore(&saved);
        let repos: Vec<TestRepo> = names.iter().map(|name| env.repo_handle(name)).collect();
        let mut hive = Hive::open(&env.root().join("hub")).unwrap();
        for repo in &repos {
            let node = NodeRepo::open(&repo.repo_path(), &repo.settings())
                .unwrap()
                .with_repo_config(Some(repo.repo_config_path()));
            hive.add(node).unwrap();
        }
        Self { env, repos, hive }
    }

    /// Joins already-created repositories to a fresh hive and syncs.
    pub fn join(env: TestEnv, repos: Vec<TestRepo>) -> Self {
        let mut fixture = Self::unsynced(env, repos);
        fixture.sync();
        fixture
    }

    /// Joins repositories without syncing.
    pub fn unsynced(env: TestEnv, repos: Vec<TestRepo>) -> Self {
        let mut hive = Hive::new(&env.root().join("hub"), Backend::Git).unwrap();
        for repo in &repos {
            let mut node = NodeRepo::open(&repo.repo_path(), &repo.settings())
                .unwrap()
                .with_repo_config(Some(repo.repo_config_path()));
            node.create_join_operation(&format!("musubi: {} joins", repo.machine()))
                .unwrap();
            hive.add(node).unwrap();
        }
        Self { env, repos, hive }
    }

    /// Joins another repository to the hive, without syncing.
    pub fn add(&mut self, repo: TestRepo) {
        let mut node = NodeRepo::open(&repo.repo_path(), &repo.settings())
            .unwrap()
            .with_repo_config(Some(repo.repo_config_path()));
        node.create_join_operation(&format!("musubi: {} joins", repo.machine()))
            .unwrap();
        self.hive.add(node).unwrap();
        self.repos.push(repo);
    }

    pub fn sync(&mut self) {
        self.try_sync().unwrap();
    }

    pub fn try_sync(&mut self) -> anyhow::Result<()> {
        self.hive.sync_all()
    }

    pub fn repo(&self, index: usize) -> &TestRepo {
        &self.repos[index]
    }

    /// Writes a file and commits it with `message` as the description.
    pub fn commit(&self, index: usize, file: &str, message: &str) {
        let repo = self.repo(index);
        repo.write_file(file, message);
        repo.jj(&["commit", "-m", message]);
    }

    /// The commit id of the single visible commit whose first description line is
    /// `message`.
    pub fn commit_id(&self, index: usize, message: &str) -> String {
        let ids: Vec<String> = self
            .visible(index)
            .into_iter()
            .filter_map(|line| {
                let mut fields = line.splitn(3, ' ');
                let (id, _change, subject) = (fields.next()?, fields.next()?, fields.next()?);
                (subject == message).then(|| id.to_owned())
            })
            .collect();
        assert_eq!(
            ids.len(),
            1,
            "expected one commit described {message:?}, got {ids:?}"
        );
        ids[0].clone()
    }

    /// Every bookmark with its targets, from `jj bookmark list --all-remotes`.
    pub fn bookmarks(&self, index: usize) -> BTreeMap<String, String> {
        // A tracked remote bookmark with no local bookmark lists as a deleted local
        // bookmark; skip those.
        let template = r#"if(present, name ++ "@" ++ remote ++ "\t" ++ if(conflict, "conflict:" ++ added_targets.map(|c| c.commit_id()).join(","), normal_target.commit_id()) ++ "\n")"#;
        self.repo(index)
            .jj(&["bookmark", "list", "--all-remotes", "-T", template])
            .lines()
            .filter_map(|line| line.split_once('\t'))
            .map(|(name, target)| (name.to_owned(), target.to_owned()))
            .collect()
    }

    /// The workspaces this machine's view has, with their working-copy commits: its own,
    /// and the other machines' as `<machine>/<workspace>`.
    pub fn workspaces(&self, index: usize) -> BTreeMap<String, String> {
        let template = r#"name ++ "\t" ++ target.commit_id() ++ "\n""#;
        self.repo(index)
            .jj(&["workspace", "list", "-T", template])
            .lines()
            .filter_map(|line| line.split_once('\t'))
            .map(|(name, target)| (name.to_owned(), target.to_owned()))
            .collect()
    }

    /// Visible commits with their change ids and descriptions.
    pub fn visible(&self, index: usize) -> BTreeSet<String> {
        let template =
            r#"commit_id ++ " " ++ change_id ++ " " ++ description.first_line() ++ "\n""#;
        self.repo(index)
            .jj(&["log", "--no-graph", "-r", "all()", "-T", template])
            .lines()
            .map(str::to_owned)
            .collect()
    }

    /// The number of operations in the repository's op log.
    pub fn op_count(&self, index: usize) -> usize {
        self.repo(index)
            .jj(&["op", "log", "--no-graph", "-T", "id ++ \"\\n\""])
            .lines()
            .count()
    }

    /// The hive's invariants once synced: running `jj` everywhere and syncing again
    /// reaches a fixed point within a few rounds (each machine's next command may reset its
    /// own git HEAD after a rebase, which replicates once, but nothing ping-pongs); then
    /// every machine agrees on visible commits and bookmarks, each machine shows the other
    /// machines' working copies where they are, each colocated repository's git branches
    /// match its bookmarks that are not conflicted or on the root commit, and `jj status`
    /// changes nothing.
    pub fn assert_converged(&mut self) {
        let mut settled = false;
        for _ in 0..3 {
            let head = self.hive.hub_head();
            for index in 0..self.repos.len() {
                self.repo(index).jj(&["status"]);
            }
            self.sync();
            if self.hive.hub_head() == head {
                settled = true;
                break;
            }
        }
        assert!(
            settled,
            "the hive keeps changing: running jj and syncing never settles"
        );
        let workspaces: Vec<BTreeMap<String, String>> =
            (0..self.repos.len()).map(|i| self.workspaces(i)).collect();
        let own = |ws: &BTreeMap<String, String>| -> Vec<String> {
            ws.iter()
                .filter(|(name, _)| !name.contains('/'))
                .map(|(_, commit)| commit.clone())
                .collect()
        };
        for (index, shown) in workspaces.iter().enumerate() {
            let mut shown: Vec<String> = shown
                .iter()
                .filter(|(name, _)| name.contains('/'))
                .map(|(_, commit)| commit.clone())
                .collect();
            let mut actual: Vec<String> = (0..self.repos.len())
                .filter(|&other| other != index)
                .flat_map(|other| own(&workspaces[other]))
                .collect();
            shown.sort();
            actual.sort();
            assert_eq!(shown, actual, "other machines' working copies on {index}");
        }
        let first_visible = self.visible(0);
        let first_bookmarks = local_bookmarks(&self.bookmarks(0));
        for index in 0..self.repos.len() {
            assert_eq!(
                self.visible(index),
                first_visible,
                "visible commits differ on {index}"
            );
            let bookmarks = self.bookmarks(index);
            assert_eq!(
                local_bookmarks(&bookmarks),
                first_bookmarks,
                "bookmarks differ on {index}"
            );
            self.assert_git_matches(index, &bookmarks);
            let before = self.op_count(index);
            self.repo(index).jj(&["status"]);
            assert_eq!(
                self.op_count(index),
                before,
                "`jj status` on {index} created an operation"
            );
        }
    }

    fn assert_git_matches(&self, index: usize, bookmarks: &BTreeMap<String, String>) {
        // A repository that isn't colocated keeps its git store inside `.jj`, with no
        // `.git` to check.
        if self.repo(index).repo_path().join("store/git").is_dir() {
            return;
        }
        let refs = self.repo(index).git(&[
            "for-each-ref",
            "--format=%(refname:short) %(objectname)",
            "refs/heads",
        ]);
        let git: BTreeMap<String, String> = refs
            .lines()
            .filter_map(|line| line.split_once(' '))
            .map(|(name, id)| (name.to_owned(), id.to_owned()))
            .collect();
        for (name, target) in bookmarks {
            let Some(local) = name.strip_suffix('@') else {
                continue;
            };
            // git has no root commit, so jj leaves a branch where it was when its bookmark
            // moves there, as when concurrent operations abandon the commit under it.
            let root = !target.is_empty() && target.bytes().all(|b| b == b'0');
            if target.starts_with("conflict:") || root {
                continue;
            }
            assert_eq!(
                git.get(local),
                Some(target),
                "git branch {local} on {index}"
            );
        }
    }
}

/// Local bookmarks only (`name@` with an empty remote).
pub fn local_bookmarks(all: &BTreeMap<String, String>) -> BTreeMap<String, String> {
    all.iter()
        .filter(|(name, _)| name.ends_with('@'))
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect()
}
