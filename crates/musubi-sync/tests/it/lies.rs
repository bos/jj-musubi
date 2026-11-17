//! What a node does with replies no honest hub sends that its decoders accept: well formed,
//! but wrong (docs/internals/testing.md, "Faults"). [`crate::faults`] gives a node's calls
//! replies that are malformed on the wire; here the protocol core and the repository take
//! replies made of real ones, mixed up: a head the hub doesn't have, operations it never
//! sent together, bundles from elsewhere in the sync.

#![allow(clippy::unwrap_used)]

use std::collections::HashSet;
use std::path::Path;

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
use musubi_sync::wire::map_reply;
use musubi_sync::wire::map_request;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;

use crate::faults::brief;
use crate::faults::pick;

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
#[hegel::test(profile = "slow-cases", test_cases = 30)]
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
        if lies > 0 && tc.draw_named("lie_here", gs::booleans()) {
            lies -= 1;
            let wrong = lie(&tc, &seen);
            tc.note(&format!(
                "to {}, instead of {}, the hub says {}",
                seen.describe_request(request),
                seen.describe(&reply),
                seen.describe(&wrong),
            ));
            wrong
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

    /// `op` as `op#n`, by when alpha first saw it: ids differ between runs, this doesn't.
    fn name(&self, op: &OpId) -> String {
        self.ops
            .iter()
            .position(|seen| seen == op)
            .map_or_else(|| "op#?".to_owned(), |n| format!("op#{n}"))
    }

    fn describe_attachment(attachment: &Attachment) -> String {
        match attachment {
            Attachment::None => "none".to_owned(),
            Attachment::Bundle(_) | Attachment::File(_) => "a bundle".to_owned(),
            Attachment::Haves(commits) => format!("{} haves", commits.len()),
        }
    }

    /// A reply with its operations by [`Self::name`], its attachments by kind, and no more
    /// than a few hundred characters.
    fn describe(&self, reply: &Reply<OpId, Attachment>) -> String {
        let reply = map_reply(
            reply.clone(),
            |op| self.name(&op),
            |attachment| Ok(Self::describe_attachment(&attachment)),
        );
        brief(&format!("{:?}", reply.unwrap()))
    }

    fn describe_request(&self, request: &Request<OpId, Attachment>) -> String {
        let request = map_request(
            request.clone(),
            |op| self.name(&op),
            |attachment| Ok(Self::describe_attachment(&attachment)),
        );
        brief(&format!("{:?}", request.unwrap()))
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

/// What a lie is made of.
#[derive(Clone, Copy, Debug)]
enum Lie {
    Head,
    Fetched,
    Objects,
    /// The reply to another request, as from a hub that mixed them up.
    Another,
}

/// A reply made of what alpha has seen, the real reply to this request last among them:
/// a head, a fetch or objects with any of their parts wrong, or the reply to another
/// request, as from a hub that mixed them up.
#[hegel::test_helper]
fn lie(tc: &TestCase, seen: &Seen) -> Reply<OpId, Attachment> {
    let mut kinds = vec![Lie::Head, Lie::Fetched];
    // None until a request or a reply has carried a bundle.
    if !seen.attachments.is_empty() {
        kinds.push(Lie::Objects);
    }
    kinds.push(Lie::Another);
    let kind = tc.draw(gs::sampled_from(kinds));
    match kind {
        Lie::Head => {
            let head_kind = tc.draw(gs::sampled_from(vec![
                HeadKind::Head,
                HeadKind::Accepted,
                HeadKind::Rejected,
                HeadKind::Incomplete,
                HeadKind::Notify,
            ]));
            Reply::Head {
                kind: head_kind,
                seq: seq(tc, seen),
                head: pick(tc, "head", &seen.ops).clone(),
                records: pick(tc, "records", &seen.records).clone(),
            }
        }
        Lie::Fetched => fetched(tc, seen),
        Lie::Objects => Reply::Objects {
            for_ops: ops(tc, seen),
            attachment: pick(tc, "attachment", &seen.attachments).clone(),
        },
        Lie::Another => pick(tc, "reply", &seen.replies).clone(),
    }
}

/// What a fetch's operations suffer, if anything.
#[derive(Clone, Copy, Debug)]
enum OpsDamage {
    Untouched,
    /// One is missing.
    Dropped,
    /// One comes twice.
    Repeated,
    Reversed,
    /// One has other parents.
    Reparented,
}

/// A fetch alpha was sent, or an empty one, with any of its parts wrong: its head, its
/// operations dropped, repeated, reordered or with other parents, its bundles others alpha
/// sent or was sent, or its records others alpha has seen.
#[hegel::test_helper]
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
        (*pick(tc, "fetch", &fetches)).clone()
    })
    else {
        unreachable!()
    };
    let other_seq = tc.draw(gs::booleans());
    if other_seq {
        seq = self::seq(tc, seen);
    }
    let other_head = tc.draw(gs::booleans());
    if other_head {
        head = pick(tc, "head", &seen.ops).clone();
    }
    if !ops.is_empty() {
        let at = tc.draw(gs::integers::<usize>().max_value(ops.len() - 1));
        let damage = tc.draw(gs::sampled_from(vec![
            OpsDamage::Untouched,
            OpsDamage::Dropped,
            OpsDamage::Repeated,
            OpsDamage::Reversed,
            OpsDamage::Reparented,
        ]));
        match damage {
            OpsDamage::Untouched => {}
            OpsDamage::Dropped => {
                ops.remove(at);
            }
            OpsDamage::Repeated => ops.insert(at, ops[at].clone()),
            OpsDamage::Reversed => ops.reverse(),
            OpsDamage::Reparented => ops[at].parents = self::ops(tc, seen),
        }
    }
    let other_ops_attachment = tc.draw(gs::booleans());
    if other_ops_attachment {
        ops_attachment = pick(tc, "ops_attachment", &seen.attachments).clone();
    }
    let other_objects = tc.draw(gs::booleans());
    if other_objects {
        objects = pick(tc, "objects", &seen.attachments).clone();
    }
    let other_records = tc.draw(gs::booleans());
    if other_records {
        records = pick(tc, "records", &seen.records).clone();
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

/// How a lie's sequence number differs from one alpha has seen.
#[derive(Clone, Copy, Debug)]
enum SeqLie {
    Same,
    Before,
    After,
    Largest,
}

/// A sequence number near one alpha has seen, or the largest.
#[hegel::test_helper]
fn seq(tc: &TestCase, seen: &Seen) -> u64 {
    let near = if seen.seqs.is_empty() {
        0
    } else {
        *pick(tc, "seq", &seen.seqs)
    };
    let shift = tc.draw(gs::sampled_from(vec![
        SeqLie::Same,
        SeqLie::Before,
        SeqLie::After,
        SeqLie::Largest,
    ]));
    match shift {
        SeqLie::Same => near,
        SeqLie::Before => near.saturating_sub(1),
        SeqLie::After => near.saturating_add(1),
        SeqLie::Largest => u64::MAX,
    }
}

/// A few operations alpha has seen.
#[hegel::test_helper]
fn ops(tc: &TestCase, seen: &Seen) -> Vec<OpId> {
    let count = tc.draw(gs::integers::<usize>().max_value(3));
    (0..count)
        .map(|_| pick(tc, "op", &seen.ops).clone())
        .collect()
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
