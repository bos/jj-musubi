//! What a node does with replies no honest hub sends that its decoders accept: well formed,
//! but wrong (docs/internals/testing.md, "Faults"). [`crate::faults`] gives a node's calls
//! replies that are malformed on the wire; here the protocol core and the repository take
//! replies made of real ones, mixed up: a head the hub doesn't have, operations it never
//! sent together, bundles from elsewhere in the sync.

#![allow(clippy::unwrap_used)]

use std::collections::HashSet;
use std::path::Path;

use hegel::HealthCheck;
use hegel::TestCase;
use hegel::generators as gs;
use musubi_core::message::HeadKind;
use musubi_core::message::RecordState;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_core::node::LocalRepo as _;
use musubi_jj::node::NodeRepo;
use musubi_jj::objects::Backend;
use musubi_sync::Attachment;
use musubi_sync::OpId;
use musubi_sync::hive::Hive;
use musubi_sync::node::Clock;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;

const ALPHA: usize = 0;
const BETA: usize = 1;

/// A node that gets replies a buggy hub might send, in place of some of the real ones,
/// ends its sync, failing or not, without panicking; and once the hub answers honestly
/// again, both machines come to show the same commits, everyone's among them, a node whose
/// sync failed restarting as the daemon does. So nothing the replies made it stage, realize
/// or believe keeps it from the hub's history for good.
///
/// The nodes run in process (`Hive`): the daemon's driver, which reopens the repository
/// after a failure, isn't part of it, nor is the transport, which [`crate::faults`] tests.
///
/// alpha has a commit of its own to push, and beta's to fetch, which come in a fetch of
/// several operations with their objects: the wrong replies are made of those, of the
/// replies before, of the operations and bundles alpha sent, and of its own head.
#[hegel::test(test_cases = 30, suppress_health_check = [HealthCheck::TooSlow])]
fn nodes_recover_from_wrong_replies(tc: TestCase) {
    let (_env, repos, mut hive) = fixture();
    let mut lies = tc.draw(gs::integers::<usize>().min_value(1).max_value(3));
    let mut seen = Seen::default();
    // alpha's own operation, before the hub has it: a hub may say it accepted that.
    for head in hive.members[ALPHA].adapter.heads().unwrap() {
        seen.op(&head);
    }
    let synced = hive.sync_through(ALPHA, &mut |request, reply| {
        seen.request(request);
        seen.reply(&reply);
        if lies > 0 && tc.draw(gs::booleans()) {
            lies -= 1;
            lie(&tc, &seen)
        } else {
            reply
        }
    });
    if let Err(err) = synced {
        eprintln!("the sync with wrong replies failed: {err:#}");
        hive.restart(ALPHA);
    }

    settle(&mut hive);
    let (alpha, beta) = (visible(&repos[ALPHA]), visible(&repos[BETA]));
    assert_eq!(alpha, beta);
    for work in ["from alpha", "one from beta", "two from beta"] {
        assert!(alpha.contains(work), "{work:?} is missing:\n{alpha}");
    }
}

/// Syncs every node until a whole round changes nothing, restarting a node whose sync
/// fails, as the daemon does, a few times at most.
fn settle(hive: &mut Hive) {
    let mut failures = 0;
    for _ in 0..20 {
        let mut steps = 0;
        for node in [ALPHA, BETA] {
            match hive.sync(node) {
                Ok(taken) => steps += taken,
                Err(err) if failures < 5 => {
                    eprintln!("node {node} failed to sync: {err:#}");
                    failures += 1;
                    steps += 1;
                    hive.restart(node);
                }
                Err(err) => panic!("node {node} never synced again: {err:#}"),
            }
        }
        if steps == 0 {
            return;
        }
    }
    panic!("the hive did not converge");
}

/// What alpha has sent and been sent, in the order it first appeared, for lies to be made
/// of. Never in the order of ids, which differ between runs: Hegel replays a case exactly.
#[derive(Default)]
struct Seen {
    replies: Vec<Reply<OpId, Attachment>>,
    ops: Vec<OpId>,
    known_ops: HashSet<OpId>,
    seqs: Vec<u64>,
    attachments: Vec<Attachment>,
    /// Never empty once alpha has polled, as every sync starts by doing.
    records: Vec<RecordState>,
}

impl Seen {
    fn op(&mut self, op: &OpId) {
        if self.known_ops.insert(op.clone()) {
            self.ops.push(op.clone());
        }
    }

    fn records(&mut self, records: &RecordState) {
        if !self.records.contains(records) {
            self.records.push(records.clone());
        }
    }

    fn request(&mut self, request: &Request<OpId, Attachment>) {
        match request {
            // A request's haves name commits, and a reply can't carry them as a bundle.
            Request::Fetch { base, records, .. } => {
                self.op(base);
                self.records(records);
            }
            Request::GetObjects { for_ops, base, .. } => {
                for op in for_ops {
                    self.op(op);
                }
                self.op(base);
            }
            Request::Push {
                machine: _,
                ops,
                ops_attachment,
                objects,
                expected,
                new,
                records,
                dropped,
            } => {
                for op in ops.iter().chain(dropped) {
                    self.op(op);
                }
                self.op(expected);
                self.op(new);
                self.records(records);
                self.attachments.push(ops_attachment.clone());
                self.attachments.push(objects.clone());
            }
        }
    }

    fn reply(&mut self, reply: &Reply<OpId, Attachment>) {
        match reply {
            Reply::Head {
                seq, head, records, ..
            } => {
                self.seqs.push(*seq);
                self.op(head);
                self.records(records);
            }
            Reply::Fetched {
                seq,
                head,
                ops,
                ops_attachment,
                objects,
                records,
                new_records,
                ..
            } => {
                self.seqs.push(*seq);
                self.op(head);
                self.records(records);
                for op in new_records.iter().flatten() {
                    self.op(op);
                }
                for entry in ops {
                    self.op(&entry.id);
                    for op in &entry.parents {
                        self.op(op);
                    }
                }
                self.attachments.push(ops_attachment.clone());
                self.attachments.push(objects.clone());
            }
            Reply::Objects {
                for_ops,
                attachment,
            } => {
                for op in for_ops {
                    self.op(op);
                }
                self.attachments.push(attachment.clone());
            }
            Reply::Refused { records } => self.records(records),
        }
        self.replies.push(reply.clone());
    }
}

/// A reply made of what alpha has seen, the real reply to this request last among them:
/// a head, a fetch or objects with any of their parts wrong, or the reply to another
/// request, as from a hub that mixed them up.
fn lie(tc: &TestCase, seen: &Seen) -> Reply<OpId, Attachment> {
    match tc.draw(gs::integers::<u8>().max_value(3)) {
        0 => Reply::Head {
            kind: tc.draw(gs::sampled_from(vec![
                HeadKind::Head,
                HeadKind::Accepted,
                HeadKind::Rejected,
                HeadKind::Incomplete,
                HeadKind::Notify,
            ])),
            seq: seq(tc, seen),
            head: pick(tc, &seen.ops).clone(),
            records: pick(tc, &seen.records).clone(),
        },
        1 => fetched(tc, seen),
        2 => Reply::Objects {
            for_ops: ops(tc, seen),
            attachment: pick(tc, &seen.attachments).clone(),
        },
        _ => pick(tc, &seen.replies).clone(),
    }
}

/// A fetch alpha was sent, or an empty one, with any of its parts wrong: its head, its
/// operations dropped, repeated, reordered or with other parents, its bundles others alpha
/// sent or was sent, or its records others alpha has seen.
fn fetched(tc: &TestCase, seen: &Seen) -> Reply<OpId, Attachment> {
    let fetches: Vec<_> = seen
        .replies
        .iter()
        .filter(|reply| matches!(reply, Reply::Fetched { .. }))
        .collect();
    let Reply::Fetched {
        mut seq,
        mut head,
        mut ops,
        mut ops_attachment,
        mut objects,
        mut records,
        records_from,
        new_records,
        pruned,
    } = (if fetches.is_empty() {
        Reply::Fetched {
            seq: 0,
            head: seen.ops[0].clone(),
            ops: vec![],
            ops_attachment: Attachment::None,
            objects: Attachment::None,
            records: seen.records[0].clone(),
            records_from: 0,
            new_records: vec![],
            pruned: seen.records[0].clone(),
        }
    } else {
        (*pick(tc, &fetches)).clone()
    })
    else {
        unreachable!()
    };
    if tc.draw(gs::booleans()) {
        seq = self::seq(tc, seen);
    }
    if tc.draw(gs::booleans()) {
        head = pick(tc, &seen.ops).clone();
    }
    if !ops.is_empty() {
        let at = tc.draw(gs::integers::<usize>().max_value(ops.len() - 1));
        match tc.draw(gs::integers::<u8>().max_value(4)) {
            0 => {
                ops.remove(at);
            }
            1 => ops.insert(at, ops[at].clone()),
            2 => ops.reverse(),
            3 => ops[at].parents = self::ops(tc, seen),
            _ => {}
        }
    }
    if tc.draw(gs::booleans()) {
        ops_attachment = pick(tc, &seen.attachments).clone();
    }
    if tc.draw(gs::booleans()) {
        objects = pick(tc, &seen.attachments).clone();
    }
    if tc.draw(gs::booleans()) {
        records = pick(tc, &seen.records).clone();
    }
    Reply::Fetched {
        seq,
        head,
        ops,
        ops_attachment,
        objects,
        records,
        records_from,
        new_records,
        pruned,
    }
}

/// A sequence number near one alpha has seen, or the largest.
fn seq(tc: &TestCase, seen: &Seen) -> u64 {
    let near = if seen.seqs.is_empty() {
        0
    } else {
        *pick(tc, &seen.seqs)
    };
    match tc.draw(gs::integers::<u8>().max_value(3)) {
        0 => near.saturating_sub(1),
        1 => near,
        2 => near.saturating_add(1),
        _ => u64::MAX,
    }
}

/// A few operations alpha has seen.
fn ops(tc: &TestCase, seen: &Seen) -> Vec<OpId> {
    (0..tc.draw(gs::integers::<usize>().max_value(3)))
        .map(|_| pick(tc, &seen.ops).clone())
        .collect()
}

fn pick<'a, T>(tc: &TestCase, items: &'a [T]) -> &'a T {
    &items[tc.draw(gs::integers::<usize>().max_value(items.len() - 1))]
}

/// The environment's clock, for its nodes, so that a case replays exactly.
struct TestClock(musubi_testutil::Clock);

impl Clock for TestClock {
    fn now(&self) -> std::time::SystemTime {
        self.0.now()
    }

    fn tick(&self, repo: &mut NodeRepo) {
        repo.set_settings(self.0.retime(repo.loader().settings()));
    }
}

/// alpha and beta, joined to a hive: beta has pushed two commits, and alpha has one of its
/// own, and knows nothing of beta's. Made once per build of the test binary
/// (`musubi_testutil::recorded`); each case gets a copy, with nodes that know nothing of
/// the hub yet, as after a restart.
fn fixture() -> (TestEnv, Vec<TestRepo>, Hive) {
    let names = ["alpha", "beta"];
    let saved = musubi_testutil::recorded(Path::new(env!("CARGO_TARGET_TMPDIR")), "lies", |dir| {
        let env = TestEnv::new();
        let repos: Vec<TestRepo> = names.iter().map(|name| env.init_repo(name)).collect();
        let mut hive = Hive::new(&env.root().join("hub"), Backend::GIT).unwrap();
        for repo in &repos {
            let mut node = open(repo, &repo.repo_config_path());
            node.create_join_operation(&format!("musubi: {} joins", repo.machine()))
                .unwrap();
            add(&mut hive, &env, node);
        }
        hive.sync_all().unwrap();
        let beta = &repos[BETA];
        beta.write_file("one", "one");
        beta.jj(&["commit", "-m", "one from beta"]);
        beta.write_file("two", "two");
        beta.jj(&["commit", "-m", "two from beta"]);
        hive.sync(BETA).unwrap();
        repos[ALPHA].write_file("alpha", "alpha");
        repos[ALPHA].jj(&["commit", "-m", "from alpha"]);
        // Its nodes finish writing what they realized as they close.
        drop(hive);
        // Where jj keeps each repository's config, which a copy keeps in the same place in
        // its own environment.
        let configs: Vec<String> = repos
            .iter()
            .map(|repo| {
                let path = repo.repo_config_path();
                let path = path.strip_prefix(env.root()).unwrap();
                path.to_str().unwrap().to_owned()
            })
            .collect();
        env.save(dir);
        std::fs::write(dir.join("configs"), configs.join("\n")).unwrap();
        // jj takes a repository whose recorded path is still there for a copy.
        std::fs::remove_dir_all(env.root()).unwrap();
    });
    let env = TestEnv::restore(&saved);
    let repos: Vec<TestRepo> = names.iter().map(|name| env.repo_handle(name)).collect();
    let configs = std::fs::read_to_string(saved.join("configs")).unwrap();
    let mut hive = Hive::open(&env.root().join("hub")).unwrap();
    for (repo, config) in repos.iter().zip(configs.lines()) {
        let node = open(repo, &env.root().join(config));
        add(&mut hive, &env, node);
    }
    (env, repos, hive)
}

fn open(repo: &TestRepo, config: &Path) -> NodeRepo {
    NodeRepo::open(&repo.repo_path(), &repo.settings())
        .unwrap()
        .with_repo_config(Some(config.to_owned()))
}

fn add(hive: &mut Hive, env: &TestEnv, node: NodeRepo) {
    let index = hive.add(node).unwrap();
    hive.members[index]
        .adapter
        .set_clock(Box::new(TestClock(env.clock())));
}

fn visible(repo: &TestRepo) -> String {
    repo.jj(&[
        "log",
        "--no-graph",
        "-r",
        "all()",
        "-T",
        "commit_id ++ \" \" ++ description.first_line() ++ \"\\n\"",
    ])
}
