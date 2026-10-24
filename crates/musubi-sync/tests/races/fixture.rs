//! A hive of real repositories with an in-process hub.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::path::Path;
use std::sync::Arc;

use futures::TryStreamExt as _;
use futures::executor::block_on;
use jj_lib::backend::CommitId;
use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::object_id::ObjectId as _;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use jj_lib::repo::RepoLoader;
use jj_lib::revset::RevsetExpression;
use musubi_jj::node::NodeRepo;
use musubi_jj::objects::Backend;
use musubi_sync::hive::Hive;
use musubi_sync::node::Clock;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;

/// The environment's clock, for its nodes: their operations take their times from it, as
/// the `jj` commands' do, and they judge copies unused by it.
pub struct TestClock(pub musubi_testutil::Clock);

impl Clock for TestClock {
    fn now(&self) -> std::time::SystemTime {
        self.0.now()
    }

    fn tick(&self, repo: &mut NodeRepo) {
        repo.set_settings(self.0.retime(repo.loader().settings()));
    }
}

/// Adds `node` to `hive`, keeping `env`'s time.
pub fn add_node(hive: &mut Hive, env: &TestEnv, node: NodeRepo) {
    let index = hive.add(node).unwrap();
    hive.members[index]
        .adapter
        .set_clock(Box::new(TestClock(env.clock())));
}

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
        Self::recorded(names, "", |_| {})
    }

    /// As `new`, with `setup` run on the hive once it is synced, before it is recorded under
    /// `key`, a name of its own for the setup.
    pub fn recorded(names: &[&str], key: &str, setup: impl FnOnce(&mut Self)) -> Self {
        let base = Path::new(env!("CARGO_TARGET_TMPDIR"));
        let mut name = format!("fixture-{}", names.join("-"));
        if !key.is_empty() {
            name = format!("{name}-{key}");
        }
        let saved = musubi_testutil::recorded(base, &name, |dir| {
            let env = TestEnv::new();
            let repos = names.iter().map(|name| env.init_repo(name)).collect();
            let mut fixture = Self::join(env, repos);
            setup(&mut fixture);
            let Self { env, repos, hive } = fixture;
            // Its nodes finish writing what they realized as they close.
            drop(hive);
            // Where jj keeps each repository's config, which a copy keeps in the same place
            // in its own environment: asking jj for each test's copy would start it again.
            let configs: Vec<String> = repos
                .iter()
                .map(|repo| {
                    let path = repo.repo_config_path();
                    let path = path
                        .strip_prefix(env.root())
                        .expect("jj keeps repo config in the environment's home");
                    path.to_str().unwrap().to_owned()
                })
                .collect();
            env.save(dir);
            std::fs::write(dir.join("configs"), configs.join("\n")).unwrap();
            // Gone even where MUSUBI_KEEP_TEST_DIRS keeps the rest: jj takes a repository
            // whose recorded path is still there for a copy, and gives a copy a config of its
            // own.
            std::fs::remove_dir_all(env.root()).unwrap();
        });
        let env = TestEnv::restore(&saved);
        let repos: Vec<TestRepo> = names.iter().map(|name| env.repo_handle(name)).collect();
        let configs = std::fs::read_to_string(saved.join("configs")).unwrap();
        let mut hive = Hive::open(&env.root().join("hub")).unwrap();
        for (repo, config) in repos.iter().zip(configs.lines()) {
            let node = NodeRepo::open(&repo.repo_path(), &repo.settings())
                .unwrap()
                .with_repo_config(Some(env.root().join(config)));
            add_node(&mut hive, &env, node);
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
            add_node(&mut hive, &env, node);
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
        add_node(&mut self.hive, &self.env, node);
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

    /// Machine `index`'s identity in the hive, the key its workspaces are under.
    pub fn machine_key(&self, index: usize) -> String {
        self.hive.members[index]
            .adapter
            .repo()
            .machine()
            .key()
            .to_owned()
    }

    /// The node of machine `index`, to act on as musubi's commands do, with its time moved
    /// on to now.
    pub fn node(&mut self, index: usize) -> &mut NodeRepo {
        self.hive.members[index].adapter.repo_mut()
    }

    /// The names of the workspaces in machine `index`'s view, read in process, so that
    /// reading them snapshots nothing: a snapshot is work, which would bring a machine the
    /// hive has forgotten back.
    pub fn workspace_names(&self, index: usize) -> BTreeSet<String> {
        self.load(index)
            .view()
            .wc_commit_ids()
            .keys()
            .map(|name| name.as_str().to_owned())
            .collect()
    }

    /// The machines whose workspaces the hub's head has: those present, with workspaces.
    pub fn shown_machines(&self) -> BTreeSet<String> {
        self.hub_workspaces()
            .iter()
            .filter_map(|key| key.split_once('/'))
            .map(|(machine, _)| machine.to_owned())
            .collect()
    }

    /// The workspaces the hub's head has, by key: `<machine key>/<workspace>`.
    fn hub_workspaces(&self) -> BTreeSet<String> {
        let store = self.hive.hub.store();
        let head = store.head().1;
        if head == store.canonical().root_operation_id() {
            return BTreeSet::new();
        }
        store
            .canonical()
            .read_operation_view(head)
            .unwrap()
            .wc_commit_ids
            .into_keys()
            .map(|key| key.as_str().to_owned())
            .collect()
    }

    /// The repository at its head, read in process: unlike a `jj` command, reading it
    /// snapshots nothing and imports nothing from git.
    pub fn load(&self, index: usize) -> Arc<ReadonlyRepo> {
        let repo = self.repo(index);
        let loader = RepoLoader::init_from_file_system(
            &repo.settings(),
            &repo.repo_path(),
            &default_backend_factories(),
        )
        .unwrap();
        block_on(loader.load_at_head()).unwrap()
    }

    /// The hive's invariants once synced: running `jj` everywhere and syncing again
    /// reaches a fixed point within a few rounds (each machine's next command may reset its
    /// own git HEAD after a rebase, which replicates once, but nothing ping-pongs); then
    /// every machine agrees on visible commits and bookmarks, each machine shows the
    /// working copies of the other machines the hive hasn't forgotten, where they are, each
    /// colocated repository's git branches match its bookmarks that are not conflicted or on
    /// the root commit, and `jj status` changes nothing.
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
        // Read in process, which spares a few hundred `jj` commands over the catalogue:
        // every machine has run `jj status` since the hive last changed, so a command would
        // snapshot and import nothing first.
        let repos: Vec<Arc<ReadonlyRepo>> = (0..self.repos.len()).map(|i| self.load(i)).collect();
        let workspaces: Vec<BTreeMap<String, String>> = repos
            .iter()
            .map(|repo| {
                repo.view()
                    .wc_commit_ids()
                    .iter()
                    .map(|(name, id)| (name.as_str().to_owned(), id.hex()))
                    .collect()
            })
            .collect();
        let shown_machines = self.shown_machines();
        let keys: Vec<String> = (0..self.repos.len()).map(|i| self.machine_key(i)).collect();
        // A machine's own workspaces: those named without a `/`, and those the hub's head
        // gives it, as `beta/x` of `alpha#1a2b/beta/x`.
        let published = self.hub_workspaces();
        let is_own = |index: usize, name: &str| {
            !name.contains('/') || published.contains(&format!("{}/{name}", keys[index]))
        };
        for (index, shown) in workspaces.iter().enumerate() {
            let mut shown: Vec<String> = shown
                .iter()
                .filter(|(name, _)| !is_own(index, name))
                .map(|(_, commit)| commit.clone())
                .collect();
            let mut actual: Vec<String> = (0..self.repos.len())
                .filter(|&other| other != index && shown_machines.contains(&keys[other]))
                .flat_map(|other| {
                    workspaces[other]
                        .iter()
                        .filter(move |(name, _)| is_own(other, name))
                        .map(|(_, commit)| commit.clone())
                })
                .collect();
            shown.sort();
            actual.sort();
            assert_eq!(shown, actual, "other machines' working copies on {index}");
        }
        let visible: Vec<BTreeSet<String>> = repos.iter().map(visible).collect();
        let bookmarks: Vec<BTreeMap<String, String>> = repos.iter().map(local_bookmarks).collect();
        for index in 0..self.repos.len() {
            assert_eq!(
                visible[index], visible[0],
                "visible commits differ on {index}"
            );
            assert_eq!(
                bookmarks[index], bookmarks[0],
                "bookmarks differ on {index}"
            );
            self.assert_git_matches(index, &bookmarks[index]);
            self.repo(index).jj(&["status"]);
            assert_eq!(
                self.load(index).op_id(),
                repos[index].op_id(),
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
        for (local, target) in bookmarks {
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

/// Visible commits with their change ids and descriptions' first lines.
fn visible(repo: &Arc<ReadonlyRepo>) -> BTreeSet<String> {
    let revset = RevsetExpression::visible_heads()
        .ancestors()
        .evaluate(repo.as_ref())
        .unwrap();
    let ids: Vec<CommitId> = block_on(revset.stream().try_collect()).unwrap();
    ids.iter()
        .map(|id| {
            let commit = repo.store().get_commit(id).unwrap();
            let subject = commit.description().lines().next().unwrap_or_default();
            format!("{} {} {subject}", id.hex(), commit.change_id().hex())
        })
        .collect()
}

/// Local bookmarks with their targets: a commit id, or `conflict:` and the ids it adds.
fn local_bookmarks(repo: &Arc<ReadonlyRepo>) -> BTreeMap<String, String> {
    repo.view()
        .local_bookmarks()
        .map(|(name, target)| {
            let target = match target.as_normal() {
                Some(id) => id.hex(),
                None => {
                    let added: Vec<String> = target.adds().flatten().map(|id| id.hex()).collect();
                    format!("conflict:{}", added.join(","))
                }
            };
            (name.as_str().to_owned(), target)
        })
        .collect()
}
