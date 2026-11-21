//! `NodeRepo::canonical_view` and `NodeRepo::own_of_view` against `owned`, `canonView` and
//! `ownOfView` in formal/Musubi/Ownership.lean, through the oracle (docs/internals/conformance.md,
//! "Workspace ownership").
//!
//! Each case writes one translation's evidence into a joined repository: canonical parents with
//! their presence, or the root alone as after a trim; local parents standing for them, marked
//! and recording private and reserved names; a target for an undo, restore or revert; and a
//! local operation with its view and namespace context. It runs `canonical_view` on it, writes
//! the canonical operation it returns, and runs `own_of_view` on that. The names it puts under
//! this machine's key, and those `own_of_view` owns, must be the oracle's.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::collections::BTreeSet;

use hegel::TestCase;
use hegel::generators as gs;
use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::Operation as StoreOperation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::OperationMetadata;
use jj_lib::op_store::View;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::ref_name::WorkspaceNameBuf;
use musubi_testutil::TestEnv;
use pollster::FutureExt as _;
use serde_json::Value;
use serde_json::json;

use super::FIXUP_ATTRIBUTE;
use super::NodeRepo;
use super::view::LOCAL_WORKSPACES;
use super::view::RESERVED_WORKSPACES;
use crate::canonical::namespace;
use crate::canonical::namespace::Namespace;
use crate::op_attrs::OpAttrs;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
use crate::oracle::Oracle;
use crate::presence::FORGET_ATTRIBUTE;
use crate::presence::Kind;
use crate::presence::WORK_ATTRIBUTE;
use crate::workspaces;

/// Other machines: two named alike, whose suffixes start alike, and one named as this one is.
const OTHERS: [&str; 4] = [
    "beta#bbbb1111",
    "beta#bbbb2222",
    "gamma#cccc3333",
    "alpha#aaaa4444",
];

/// Workspaces of other machines.
const WORKSPACES: [&str; 2] = ["default", "x"];

/// Local names: plain ones, and ones shown, or once shown, as other machines' workspaces.
const NAMES: [&str; 14] = [
    "alpha",
    "default",
    "x",
    "beta/x",
    "beta/default",
    "beta-bbbb/x",
    "beta-bbbb1111/x",
    "beta-bbbb2222/x",
    "beta-bbbb2222-/x",
    "gamma/x",
    "gamma/default",
    "gamma-cccc/x",
    "alpha/x",
    "alpha-aaaa/x",
];

/// A joined repository, kept across cases: every case writes operations of its own, each
/// distinct, so what one case leaves is never read by another.
struct Fixture {
    _env: TestEnv,
    node: NodeRepo,
    me: String,
    /// Every working copy's commit.
    commit: CommitId,
    /// The local operation after joining, on which local parents are written.
    head: LocalOp,
    local_metadata: OperationMetadata,
    local_view: View,
    join: CanonicalOp,
    canonical_metadata: OperationMetadata,
    canonical_view: View,
    count: u64,
}

impl Fixture {
    fn new() -> Self {
        let env = TestEnv::new();
        let repo = env.init_repo("alpha");
        let mut node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
        let join = node.create_join_operation("musubi: test joins").unwrap();
        let me = node.machine.key().to_owned();
        let head = node.local_heads().unwrap().pop().unwrap();
        let op_store = node.loader.op_store().clone();
        let local = op_store.read_operation(&head.0).block_on().unwrap();
        let local_view = op_store.read_view(&local.view_id).block_on().unwrap();
        let commit = local_view.wc_commit_ids.values().next().unwrap().clone();
        let canonical = node.canonical.read_operation(&join).unwrap();
        let canonical_view = node.canonical.read_view(&canonical.view_id).unwrap();
        Self {
            _env: env,
            node,
            me,
            commit,
            head,
            local_metadata: local.metadata,
            local_view,
            join,
            canonical_metadata: canonical.metadata,
            canonical_view,
            count: 0,
        }
    }

    fn nonce(&mut self) -> String {
        self.count += 1;
        self.count.to_string()
    }

    /// Writes a canonical operation with these keys, `(machine, workspace)`.
    fn canonical(
        &mut self,
        parents: &[CanonicalOp],
        keys: &[(String, String)],
        attributes: BTreeMap<String, String>,
    ) -> CanonicalOp {
        let mut view = self.canonical_view.clone();
        view.wc_commit_ids = keys
            .iter()
            .map(|(machine, workspace)| {
                (
                    workspaces::workspace_key(machine, workspace),
                    self.commit.clone(),
                )
            })
            .collect();
        let mut metadata = self.canonical_metadata.clone();
        metadata.description = format!("canonical {}", self.nonce());
        metadata.workspace_name = None;
        metadata.attributes = attributes;
        let op = StoreOperation {
            view_id: self.node.canonical.write_view(&view).unwrap(),
            parents: parents.iter().map(|parent| parent.0.clone()).collect(),
            metadata,
            commit_predecessors: Some(BTreeMap::new()),
        };
        self.node.canonical.write_operation(&op).unwrap()
    }

    /// Writes a local operation with these workspace names.
    fn local(
        &mut self,
        parents: &[LocalOp],
        names: &BTreeSet<&str>,
        mut attributes: BTreeMap<String, String>,
        command: bool,
        description: Option<String>,
    ) -> (LocalOp, StoreOperation, View) {
        let mut view = self.local_view.clone();
        view.wc_commit_ids = names
            .iter()
            .map(|name| (WorkspaceNameBuf::from(*name), self.commit.clone()))
            .collect();
        let op_store = self.node.loader.op_store().clone();
        let mut metadata = self.local_metadata.clone();
        metadata.description = description.unwrap_or_else(|| "local".to_owned());
        // Distinct operations, whatever else they share.
        attributes.insert("musubi-test.nonce".to_owned(), self.nonce());
        metadata.attributes = attributes;
        metadata.workspace_name = command.then(|| WorkspaceNameBuf::from("alpha"));
        let op = StoreOperation {
            view_id: op_store.write_view(&view).block_on().unwrap(),
            parents: parents.iter().map(|parent| parent.0.clone()).collect(),
            metadata,
            commit_predecessors: Some(BTreeMap::new()),
        };
        let id = LocalOp(op_store.write_operation(&op).block_on().unwrap());
        (id, op, view)
    }

    /// Attributes of a realization of `canonical` that records `private` and `reserved`.
    fn marked(
        &self,
        canonical: &CanonicalOp,
        private: &BTreeSet<&str>,
        reserved: &BTreeSet<&str>,
    ) -> BTreeMap<String, String> {
        let mut attributes = BTreeMap::new();
        OpAttrs(&mut attributes).set_canonical(canonical);
        if !private.is_empty() {
            let record = Namespace {
                source: self.me.clone(),
                known: BTreeSet::from([self.me.clone()]),
                names: private
                    .iter()
                    .map(|name| {
                        (
                            (*name).to_owned(),
                            workspaces::workspace_key(&self.me, name)
                                .as_str()
                                .to_owned(),
                        )
                    })
                    .collect(),
            };
            attributes.insert(LOCAL_WORKSPACES.to_owned(), record.encode());
        }
        if !reserved.is_empty() {
            attributes.insert(
                RESERVED_WORKSPACES.to_owned(),
                serde_json::to_string(&reserved.iter().collect::<Vec<_>>()).unwrap(),
            );
        }
        attributes
    }
}

thread_local! {
    static FIXTURE: RefCell<Option<Fixture>> = const { RefCell::new(None) };
}

/// A machine key as the oracle reads it.
fn key(machine: &str) -> Value {
    let (name, suffix) = machine.split_once('#').unwrap();
    json!({"name": name, "suffix": suffix})
}

fn wkey(machine: &str, workspace: &str) -> Value {
    json!({"machine": key(machine), "workspace": workspace})
}

/// Some of `NAMES`.
type Names = BTreeSet<&'static str>;

/// Where the operation started from.
#[derive(Clone, Debug)]
enum Source {
    Parents,
    /// An undo, redo or restore of a target with this view, private record and own names.
    Restore(Names, Names, Names),
    /// A revert of such a target, whose parent is the first local parent.
    Revert(Names, Names, Names),
    /// An undo whose target jj has collected.
    Collected,
}

/// A namespace context: its source, names with their keys, and machines known.
#[derive(Clone, Debug)]
struct Context {
    source: String,
    names: BTreeMap<&'static str, (String, String)>,
    known: BTreeSet<String>,
}

/// One translation's evidence.
#[derive(Clone, Debug)]
struct Scenario {
    /// Whether a trim left the operation on the root alone.
    trimmed: bool,
    /// Other machines whose work the parents' histories have.
    known: BTreeSet<&'static str>,
    /// Whether the hive has forgotten this machine at the parents.
    absent: bool,
    /// This machine's workspaces as of its latest work.
    worked: BTreeSet<&'static str>,
    /// Each canonical parent's keys, `(machine, workspace)`, and the local parent standing for
    /// it: its view, private record and reserved names.
    parents: Vec<Parent>,
    view: BTreeSet<&'static str>,
    command: bool,
    /// A name of the view that the operation's description says it added, and whether as
    /// `jj workspace rename` rather than `jj workspace add` says it, where it goes back to no
    /// older view.
    adds: Option<(&'static str, bool)>,
    fixup: bool,
    source: Source,
    context: Option<Context>,
}

#[derive(Clone, Debug)]
struct Parent {
    /// What happened on this parent's line of history alone.
    extra: Extra,
    keys: Vec<(String, String)>,
    view: BTreeSet<&'static str>,
    private: BTreeSet<&'static str>,
    reserved: BTreeSet<&'static str>,
}

/// What a parent's line of history adds to the history the parents share: a machine joining,
/// or a forget of this machine, so that the parents of a merge can know different machines and
/// disagree on whether this one is present.
#[derive(Clone, Debug)]
enum Extra {
    Nothing,
    Joins(&'static str),
    ForgetsThis,
}

fn names(tc: &TestCase, max: usize) -> BTreeSet<&'static str> {
    tc.draw(gs::vecs(gs::sampled_from(NAMES.to_vec())).max_size(max))
        .into_iter()
        .collect()
}

fn scenario(tc: &TestCase, me: &str) -> Scenario {
    let trimmed = tc.draw(gs::weighted_booleans(1.0 / 3.0));
    let known: BTreeSet<&str> = tc
        .draw(gs::vecs(gs::sampled_from(OTHERS.to_vec())).max_size(3))
        .into_iter()
        .collect();
    let absent = tc.draw(gs::weighted_booleans(1.0 / 4.0));
    let worked = names(tc, 2);
    let joinable: Vec<&str> = OTHERS
        .iter()
        .copied()
        .filter(|machine| !known.contains(machine))
        .collect();
    let count = if trimmed {
        1
    } else {
        1 + tc.draw(gs::integers::<usize>().max_value(1))
    };
    let parents = (0..count)
        .map(|_| {
            let extra = match tc.draw(gs::integers::<u8>().max_value(3)) {
                0 if !joinable.is_empty() => {
                    Extra::Joins(tc.draw(gs::sampled_from(joinable.clone())))
                }
                1 if !absent => Extra::ForgetsThis,
                _ => Extra::Nothing,
            };
            // A forget of this machine removes its workspaces from the view.
            let present = !absent && !matches!(extra, Extra::ForgetsThis);
            let mut owners: Vec<&str> = present.then_some(me).into_iter().collect();
            owners.extend(known.iter().copied());
            if let Extra::Joins(machine) = extra {
                owners.push(machine);
            }
            let keys = if owners.is_empty() {
                vec![]
            } else {
                tc.draw(gs::vecs(gs::integers::<usize>().max_value(owners.len() - 1)).max_size(4))
                    .into_iter()
                    .map(|owner| {
                        let workspace = if owners[owner] == me {
                            tc.draw(gs::sampled_from(NAMES.to_vec()))
                        } else {
                            tc.draw(gs::sampled_from(WORKSPACES.to_vec()))
                        };
                        (owners[owner].to_owned(), workspace.to_owned())
                    })
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect()
            };
            Parent {
                extra,
                keys,
                view: names(tc, 5),
                private: names(tc, 2),
                reserved: names(tc, 1)
                    .into_iter()
                    .filter(|name| name.contains('/'))
                    .collect(),
            }
        })
        .collect();
    let source = match tc.draw(gs::integers::<u8>().max_value(5)) {
        0 => Source::Restore(names(tc, 5), names(tc, 2), names(tc, 2)),
        1 => Source::Revert(names(tc, 5), names(tc, 2), names(tc, 2)),
        2 => Source::Collected,
        _ => Source::Parents,
    };
    let view = match &source {
        Source::Restore(view, _, _) => view.clone(),
        _ => names(tc, 6),
    };
    let context = tc.draw(gs::booleans()).then(|| {
        let source = if tc.draw(gs::weighted_booleans(0.8)) {
            me.to_owned()
        } else {
            OTHERS[0].to_owned()
        };
        let mut names: BTreeMap<&str, (String, String)> = BTreeMap::new();
        let mut keys = BTreeSet::new();
        for _ in 0..tc.draw(gs::integers::<usize>().max_value(4)) {
            let name = tc.draw(gs::sampled_from(NAMES.to_vec()));
            let owner = tc.draw(gs::integers::<usize>().max_value(OTHERS.len()));
            let entry = if owner == OTHERS.len() {
                (source.clone(), name.to_owned())
            } else {
                (
                    OTHERS[owner].to_owned(),
                    tc.draw(gs::sampled_from(WORKSPACES.to_vec())).to_owned(),
                )
            };
            // A context names each workspace once, and its source's under their own names.
            if entry.0 == source && entry.1 != name || !keys.insert(entry.clone()) {
                continue;
            }
            names.insert(name, entry);
        }
        let mut known: BTreeSet<String> =
            names.values().map(|(machine, _)| machine.clone()).collect();
        known.insert(source.clone());
        known.extend(
            tc.draw(gs::vecs(gs::sampled_from(OTHERS.to_vec())).max_size(2))
                .into_iter()
                .map(str::to_owned),
        );
        Context {
            source,
            names,
            known,
        }
    });
    // Mostly a name shown, or once shown, as another machine's, the only kind it decides.
    let slashed: Vec<&str> = view
        .iter()
        .copied()
        .filter(|name| name.contains('/'))
        .collect();
    let adds = if slashed.is_empty() || !tc.draw(gs::weighted_booleans(0.6)) {
        None
    } else {
        Some((tc.draw(gs::sampled_from(slashed)), tc.draw(gs::booleans())))
    };
    Scenario {
        trimmed,
        known,
        absent,
        worked,
        parents,
        view,
        command: tc.draw(gs::booleans()),
        adds,
        fixup: tc.draw(gs::weighted_booleans(1.0 / 8.0)),
        source,
        context,
    }
}

/// `own_names` of a canonical view with these keys, as the model's `ownNames` reads it.
fn own_names(
    me: &str,
    keys: &[(String, String)],
    present: bool,
    worked: &BTreeSet<&str>,
) -> BTreeSet<String> {
    let own: BTreeSet<String> = keys
        .iter()
        .filter(|(machine, _)| machine == me)
        .map(|(_, workspace)| workspace.clone())
        .collect();
    if own.is_empty() && !present {
        worked.iter().map(|name| (*name).to_owned()).collect()
    } else {
        own
    }
}

/// Writes the scenario, runs both functions on it, and checks them against the oracle. Returns
/// the oracle's reply.
fn check(fx: &mut Fixture, s: &Scenario) -> Value {
    let me = fx.me.clone();
    // The parents' shared history: this machine's latest work, the other machines' work, and a
    // forget of this machine where the hive has forgotten it.
    let mine: Vec<(String, String)> = s
        .worked
        .iter()
        .map(|name| (me.clone(), (*name).to_owned()))
        .collect();
    let join = fx.join.clone();
    let mut tip = fx.canonical(
        std::slice::from_ref(&join),
        &mine,
        BTreeMap::from([(WORK_ATTRIBUTE.to_owned(), me.clone())]),
    );
    for machine in &s.known {
        tip = fx.canonical(
            &[tip],
            &[],
            BTreeMap::from([(WORK_ATTRIBUTE.to_owned(), (*machine).to_owned())]),
        );
    }
    if s.absent {
        tip = fx.canonical(
            &[tip],
            &[],
            BTreeMap::from([(FORGET_ATTRIBUTE.to_owned(), me.clone())]),
        );
    }
    let present_at_tip = !s.absent;
    let mut known: BTreeSet<String> = s
        .known
        .iter()
        .map(|machine| (*machine).to_owned())
        .collect();
    known.insert(me.clone());

    let mut canonical_parents = vec![];
    let mut locals = vec![];
    let mut parents_json = vec![];
    let mut present_at_parents = vec![];
    let mut known_at_parents = known.clone();
    let mut private = BTreeSet::new();
    let mut start = BTreeSet::new();
    for parent in &s.parents {
        let mut known_here = known.clone();
        let mut present_here = present_at_tip;
        let line = match parent.extra {
            Extra::Nothing => tip.clone(),
            Extra::Joins(machine) => {
                known_here.insert(machine.to_owned());
                fx.canonical(
                    std::slice::from_ref(&tip),
                    &[],
                    BTreeMap::from([(WORK_ATTRIBUTE.to_owned(), machine.to_owned())]),
                )
            }
            Extra::ForgetsThis => {
                present_here = false;
                fx.canonical(
                    std::slice::from_ref(&tip),
                    &[],
                    BTreeMap::from([(FORGET_ATTRIBUTE.to_owned(), me.clone())]),
                )
            }
        };
        let canonical = fx.canonical(std::slice::from_ref(&line), &parent.keys, BTreeMap::new());
        let presence = fx.node.presence(&canonical).unwrap();
        assert_eq!(presence.is_present(&me), present_here);
        assert_eq!(presence.known(), &known_here);
        let attributes = fx.marked(&canonical, &parent.private, &parent.reserved);
        let head = fx.head.clone();
        let (local, _, _) = fx.local(&[head], &parent.view, attributes, false, None);
        fx.node
            .insert_map(local.clone(), canonical.clone())
            .unwrap();
        private.extend(parent.private.intersection(&parent.view).copied());
        start.extend(parent.view.iter().copied());
        parents_json.push(json!({
            "keys": parent.keys.iter().map(|(machine, workspace)| wkey(machine, workspace)).collect::<Vec<_>>(),
            "known": known_here.iter().map(|machine| key(machine)).collect::<Vec<_>>(),
            "present": present_here,
            "worked": s.worked,
            "reserved": parent.reserved,
        }));
        present_at_parents.push(present_here);
        known_at_parents.extend(known_here);
        canonical_parents.push(canonical);
        locals.push(local);
    }

    // The target of an undo, restore or revert, on the first local parent.
    let (description, source_json, private) = match &s.source {
        Source::Parents => (
            s.adds.map(|(name, renamed)| {
                let name = WorkspaceName::new(name).as_symbol();
                if renamed {
                    format!("Renamed workspace 'default' to '{name}'")
                } else {
                    format!("add workspace '{name}'")
                }
            }),
            json!({"kind": "parents"}),
            private,
        ),
        Source::Collected => {
            let gone = OperationId::new(vec![0xab; 64]);
            (
                Some(format!("restore to operation {}", gone.hex())),
                json!({"kind": "collected"}),
                BTreeSet::new(),
            )
        }
        Source::Restore(view, record, own) | Source::Revert(view, record, own) => {
            let keys: Vec<(String, String)> = own
                .iter()
                .map(|name| (me.clone(), (*name).to_owned()))
                .collect();
            let canonical = fx.canonical(std::slice::from_ref(&tip), &keys, BTreeMap::new());
            let attributes = fx.marked(&canonical, record, &BTreeSet::new());
            let (target, _, _) = fx.local(&locals[..1], view, attributes, false, None);
            fx.node.insert_map(target.clone(), canonical).unwrap();
            let mut restored = own_names(&me, &s.parents[0].keys, present_at_parents[0], &s.worked);
            restored.extend(own_names(&me, &keys, present_at_tip, &s.worked));
            match &s.source {
                Source::Restore(..) => (
                    Some(format!("restore to operation {}", target.0.hex())),
                    json!({"kind": "restore", "names": view, "own": restored}),
                    record.intersection(view).copied().collect(),
                ),
                _ => (
                    Some(format!("revert operation {}", target.0.hex())),
                    json!({"kind": "revert", "names": s.parents[0].view, "own": restored}),
                    s.parents[0]
                        .private
                        .intersection(&s.parents[0].view)
                        .copied()
                        .collect(),
                ),
            }
        }
    };
    let private: BTreeSet<&str> = private.intersection(&s.view).copied().collect();

    let (local, raw, view) = fx.local(&locals, &s.view, BTreeMap::new(), s.command, description);
    let mut metadata = raw.metadata.clone();
    metadata.workspace_name = metadata
        .workspace_name
        .map(|name| workspaces::workspace_key(&me, name.as_str()));
    if s.fixup {
        metadata
            .attributes
            .insert(FIXUP_ATTRIBUTE.to_owned(), "1".to_owned());
    }
    if let Some(context) = &s.context {
        let namespace = Namespace {
            source: context.source.clone(),
            names: context
                .names
                .iter()
                .map(|(name, (machine, workspace))| {
                    (
                        (*name).to_owned(),
                        workspaces::workspace_key(machine, workspace)
                            .as_str()
                            .to_owned(),
                    )
                })
                .collect(),
            known: context.known.clone(),
        };
        metadata
            .attributes
            .insert(namespace::ATTRIBUTE.to_owned(), namespace.encode());
    }
    assert_eq!(
        fx.node
            .private_workspace_names(&raw, &view.wc_commit_ids)
            .unwrap()
            .iter()
            .map(|name| name.as_str())
            .collect::<BTreeSet<_>>(),
        private,
        "private names"
    );

    let canonical_parents = if s.trimmed {
        vec![fx.node.canonical.root_operation_id().clone()]
    } else {
        canonical_parents
    };
    let kind = Kind::of(&metadata);
    let (canonical_view, _) = fx
        .node
        .canonical_view(
            &local,
            view.clone(),
            &canonical_parents,
            None,
            &kind,
            &metadata,
        )
        .unwrap();
    let written = StoreOperation {
        view_id: fx.node.canonical.write_view(&canonical_view).unwrap(),
        parents: canonical_parents
            .iter()
            .map(|parent| parent.0.clone())
            .collect(),
        metadata: metadata.clone(),
        commit_predecessors: Some(BTreeMap::new()),
    };
    let written = fx.node.canonical.write_operation(&written).unwrap();
    let own = fx
        .node
        .own_of_view(view.wc_commit_ids.clone(), &written, &raw)
        .unwrap();

    // What the canonical operation gets besides this machine's names, by construction: its
    // presence, as the presence rule merges the parents' (a forget on one line hides this
    // machine at the merge), and the other machines' workspaces, which jj's merge of the parents
    // keeps all of: no parent's line removes one.
    let present = s.command || !s.trimmed && present_at_parents.iter().all(|present| *present);
    let known_at: BTreeSet<String> = if s.trimmed {
        s.command.then(|| me.clone()).into_iter().collect()
    } else {
        known_at_parents
    };
    let others: BTreeSet<(String, String)> = if s.trimmed {
        BTreeSet::new()
    } else {
        s.parents
            .iter()
            .flat_map(|parent| parent.keys.iter())
            .filter(|(machine, _)| *machine != me)
            .cloned()
            .collect()
    };
    let presence = fx.node.presence(&written).unwrap();
    assert_eq!(
        presence.is_present(&me),
        present,
        "presence at the operation"
    );
    assert_eq!(
        presence.known(),
        &known_at,
        "machines known at the operation"
    );
    let keys: BTreeSet<(String, String)> = canonical_view
        .wc_commit_ids
        .keys()
        .map(|key| {
            let (machine, workspace) = workspaces::split_key(key.as_str()).unwrap();
            (machine.to_owned(), workspace.to_owned())
        })
        .collect();
    assert_eq!(
        keys.iter()
            .filter(|(machine, _)| *machine != me)
            .cloned()
            .collect::<BTreeSet<_>>(),
        others,
        "other machines' workspaces at the operation"
    );
    let worked = (!present && !s.trimmed).then(|| s.worked.clone());

    let request = json!({
        "op": "ownership",
        "me": key(&me),
        "view": s.view,
        "private": private,
        "parents": if s.trimmed { vec![Value::Null] } else { parents_json },
        "start": start,
        "source": source_json,
        "command": s.command,
        "adds": match s.source {
            Source::Parents => s.adds.map(|(name, _)| name).into_iter().collect::<Vec<_>>(),
            _ => vec![],
        },
        "fixup": s.fixup,
        "context": s.context.as_ref().map(|context| json!({
            "source": key(&context.source),
            "names": context.names.iter().map(|(name, (machine, workspace))| json!({
                "name": name,
                "key": wkey(machine, workspace),
            })).collect::<Vec<_>>(),
            "known": context.known.iter().map(|machine| key(machine)).collect::<Vec<_>>(),
        })),
        "facts": {
            "present": present,
            "known": known_at.iter().map(|machine| key(machine)).collect::<Vec<_>>(),
            "worked": worked,
            "others": others.iter().map(|(machine, workspace)| wkey(machine, workspace)).collect::<Vec<_>>(),
        },
    });
    // Ownership requests leave the oracle as they found it.
    let reply = Oracle::with(|oracle| oracle.call(&request));
    assert_eq!(reply["ok"], true, "the oracle refused {request}: {reply}");
    let model_keys: BTreeSet<(String, String)> = reply["keys"]
        .as_array()
        .unwrap()
        .iter()
        .map(|key| {
            let machine = format!(
                "{}#{}",
                key["machine"]["name"].as_str().unwrap(),
                key["machine"]["suffix"].as_str().unwrap()
            );
            (machine, key["workspace"].as_str().unwrap().to_owned())
        })
        .collect();
    assert_eq!(keys, model_keys, "canonical_view's keys\n{request}");
    let names = |value: &Value| -> BTreeSet<String> {
        value
            .as_array()
            .unwrap()
            .iter()
            .map(|name| name.as_str().unwrap().to_owned())
            .collect()
    };
    assert_eq!(
        own.keys()
            .map(|name| name.as_str().to_owned())
            .collect::<BTreeSet<_>>(),
        names(&reply["ownOfView"]),
        "own_of_view\n{request}"
    );
    reply
}

fn with_fixture<T>(f: impl FnOnce(&mut Fixture) -> T) -> T {
    FIXTURE.with(|fixture| {
        let mut fixture = fixture.borrow_mut();
        f(fixture.get_or_insert_with(Fixture::new))
    })
}

/// Both functions against the model, on evidence drawn to clash: names shown as another
/// machine's under every prefix it could take, private and reserved names, contexts of this
/// machine's and another's, the root alone after a trim, merges, and operations that go back to
/// an older one.
#[hegel::test(profile = "slow-cases", test_cases = 200)]
fn ownership_conforms(tc: TestCase) {
    with_fixture(|fx| {
        let s = scenario(&tc, &fx.me.clone());
        check(fx, &s);
    });
}

/// After a trim to the root (#167): only the context says `beta/beta` is beta's. Both functions
/// leave it beta's, as `own_of_view` before its fix didn't (`unfixed`).
#[test]
fn a_trimmed_command_leaves_what_its_context_gives_others() {
    with_fixture(|fx| {
        let me = fx.me.clone();
        let s = Scenario {
            trimmed: true,
            known: BTreeSet::new(),
            absent: false,
            worked: BTreeSet::new(),
            parents: vec![Parent {
                extra: Extra::Nothing,
                keys: vec![],
                view: BTreeSet::from(["alpha", "beta/x"]),
                private: BTreeSet::new(),
                reserved: BTreeSet::new(),
            }],
            view: BTreeSet::from(["alpha", "beta/x"]),
            command: true,
            adds: None,
            fixup: false,
            source: Source::Parents,
            context: Some(Context {
                source: me.clone(),
                names: BTreeMap::from([
                    ("alpha", (me.clone(), "alpha".to_owned())),
                    ("beta/x", (OTHERS[0].to_owned(), "x".to_owned())),
                ]),
                known: BTreeSet::from([me.clone(), OTHERS[0].to_owned()]),
            }),
        };
        let reply = check(fx, &s);
        assert_eq!(reply["owned"], json!(["alpha"]));
        assert_eq!(reply["ownOfView"], json!(["alpha"]));
        assert_eq!(reply["unfixed"], json!(["alpha", "beta/x"]));
    });
}

/// Judged against its parents (`ContextBasis::Parents`), a context gives another machine only
/// names in the views of the operation's local parents: here `default`, which this operation
/// added, stays this machine's, though the context gives it to beta.
#[test]
fn a_context_against_the_parents_gives_others_only_their_names() {
    with_fixture(|fx| {
        let me = fx.me.clone();
        let s = Scenario {
            trimmed: false,
            known: BTreeSet::new(),
            absent: false,
            worked: BTreeSet::new(),
            parents: vec![Parent {
                extra: Extra::Nothing,
                keys: vec![(me.clone(), "alpha".to_owned())],
                view: BTreeSet::from(["alpha"]),
                private: BTreeSet::new(),
                reserved: BTreeSet::new(),
            }],
            view: BTreeSet::from(["alpha", "default"]),
            command: false,
            adds: None,
            fixup: false,
            source: Source::Parents,
            context: Some(Context {
                source: me.clone(),
                names: BTreeMap::from([("default", (OTHERS[0].to_owned(), "x".to_owned()))]),
                known: BTreeSet::from([me.clone(), OTHERS[0].to_owned()]),
            }),
        };
        let reply = check(fx, &s);
        assert_eq!(reply["owned"], json!(["alpha", "default"]));
    });
}

/// A command that says it added one workspace makes only that one: `jj workspace add --name
/// beta/x`, whose view also has `beta-bbbb/x`, as `jj op abandon` of a restore that brought it
/// back can leave, keeps `beta/x` this machine's and drops `beta-bbbb/x`.
#[test]
fn a_command_makes_only_the_workspace_it_says_it_added() {
    with_fixture(|fx| {
        let me = fx.me.clone();
        let s = Scenario {
            trimmed: false,
            known: BTreeSet::from([OTHERS[0]]),
            absent: false,
            worked: BTreeSet::new(),
            parents: vec![Parent {
                extra: Extra::Nothing,
                keys: vec![
                    (me.clone(), "alpha".to_owned()),
                    (OTHERS[0].to_owned(), "default".to_owned()),
                ],
                view: BTreeSet::from(["alpha", "beta/default"]),
                private: BTreeSet::new(),
                reserved: BTreeSet::new(),
            }],
            view: BTreeSet::from(["alpha", "beta/default", "beta/x", "beta-bbbb/x"]),
            command: true,
            adds: Some(("beta/x", false)),
            fixup: false,
            source: Source::Parents,
            context: None,
        };
        let reply = check(fx, &s);
        assert_eq!(reply["owned"], json!(["alpha", "beta/x"]));
    });
}
