//! Stop the real local leave or join after each durable membership write, reopen its files,
//! and compare both the stopped state and the result of retrying with the Lean model.

#![allow(clippy::unwrap_used)]

use std::cell::Cell;
use std::collections::HashSet;
use std::fs;

use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::repo::RepoLoader;
use musubi_hub::hub_dir::HiveInfo;
use musubi_hub::hub_dir::Joined;
use musubi_jj::presence::FORGET_ATTRIBUTE;
use musubi_jj::remote_url::JoinRemotes;
use musubi_testutil::TestEnv;
use pollster::FutureExt as _;
use serde_json::Value;
use serde_json::json;

use super::Oracle;
use super::hive;
use crate::config::Entry;
use crate::config::HiveConfig;
use crate::config::UserState;
use crate::config::state_dir;
use crate::copy::Found;
use crate::copy::check;
use crate::join;
use crate::leave;
use crate::repo::Located;
use crate::settings;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Write {
    MarkLeft,
    MarkHistory,
    RetireKey,
    DropEntry,
    ClearKey,
    ClearRecord,
    KeepKey,
    PutEntry,
    JoinRecord,
}

const LEAVE: [Write; 6] = [
    Write::MarkLeft,
    Write::MarkHistory,
    Write::RetireKey,
    Write::DropEntry,
    Write::ClearKey,
    Write::ClearRecord,
];
const JOIN: [Write; 3] = [Write::KeepKey, Write::PutEntry, Write::JoinRecord];

thread_local! {
    static INTERRUPT: Cell<Option<Write>> = const { Cell::new(None) };
}

const INTERRUPTED: i32 = 76;

pub(crate) fn after(write: Write) {
    if INTERRUPT.get() == Some(write) {
        std::process::exit(INTERRUPTED);
    }
}

#[test]
fn detach_and_rejoin_conform_at_write_boundaries() {
    let reply = Oracle::spawn().call(&json!({
        "op": "copy-detach",
        "old": {"key": 0, "hive": 0, "cid": 0},
        "fresh": {"key": 1, "hive": 0, "cid": 0},
    }));
    assert_eq!(reply["ok"], true, "{reply}");
    assert_eq!(reply["leave"].as_array().unwrap().len(), LEAVE.len() + 1);
    assert_eq!(reply["join"].as_array().unwrap().len(), JOIN.len() + 1);

    let env = TestEnv::new();
    let exe = std::env::current_exe().unwrap();
    for (phase, count) in [("leave", LEAVE.len()), ("join", JOIN.len())] {
        for cut in 0..count {
            // Each child gets its own jj and musubi state without changing the environment
            // of other tests in this process.
            let repo = env.init_repo(&format!("{phase}-{cut}"));
            for retry in [false, true] {
                let result = repo
                    .program(&exe)
                    .args([
                        "--exact",
                        "copy::conformance::detach::detachment_process",
                        "--ignored",
                        "--nocapture",
                    ])
                    .env(
                        "MUSUBI_DETACH_CASE",
                        json!([phase, cut, retry, reply]).to_string(),
                    )
                    .output()
                    .unwrap();
                let stdout = String::from_utf8_lossy(&result.stdout);
                let matched = if retry {
                    result.status.success() && stdout.contains("1 passed")
                } else {
                    result.status.code() == Some(INTERRUPTED)
                };
                assert!(
                    matched,
                    "{phase} write {cut} (retry {retry}): {stdout}\n{}",
                    String::from_utf8_lossy(&result.stderr)
                );
            }
        }
    }
}

/// The hub has accepted the request. Use the same local key selection and writes as join,
/// through the actual jj checkout and state directory.
fn join_locally(located: &Located, accepted: &Joined) -> anyhow::Result<()> {
    let settings = settings::load(&located.workspace_root, &located.repo_path)?;
    let machine = join::joining_machine(located, Some("laptop"), &settings)?;
    join::keep_join_key(located, &machine)?;
    let before = HiveConfig::load(&located.repo_path)?;
    join::become_node(
        located,
        accepted,
        "test-hub",
        false,
        before.as_ref(),
        &JoinRemotes::default(),
        None,
    )
}

#[test]
#[ignore = "run in an isolated jj and musubi environment by the conformance test"]
fn detachment_process() {
    let case: Value = serde_json::from_str(&std::env::var("MUSUBI_DETACH_CASE").unwrap()).unwrap();
    let phase = case[0].as_str().unwrap();
    let index = usize::try_from(case[1].as_u64().unwrap()).unwrap();
    let retry = case[2].as_bool().unwrap();
    let expected = &case[3];
    let located = Located::find(&std::env::current_dir().unwrap()).unwrap();
    let saved = state_dir().unwrap().join("test-fixture.json");
    if retry {
        let (old, fresh, accepted): (Entry, Option<Entry>, Joined) =
            serde_json::from_slice(&fs::read(saved).unwrap()).unwrap();
        let cut = &expected[phase][index + 1];
        assert_eq!(snapshot(&located, &old, fresh.as_ref()), cut["prefix"]);
        if phase == "leave" {
            // Join uses this same path to finish an interrupted leave before selecting a key.
            leave::finish_detaching(&located).unwrap();
            assert_eq!(snapshot(&located, &old, None), cut["retry"]);
        }
        let fresh = fresh.unwrap_or_else(|| candidate(&located, &old));
        join_locally(&located, &accepted).unwrap();
        let joined = if phase == "join" {
            &cut["retry"]
        } else {
            &expected["join"][JOIN.len()]["prefix"]
        };
        assert_eq!(snapshot(&located, &old, Some(&fresh)), *joined);
        return;
    }

    let settings = settings::load(&located.workspace_root, &located.repo_path).unwrap();
    let initial = join::joining_machine(&located, Some("laptop"), &settings).unwrap();
    let backend = located
        .open_as(&settings, initial)
        .unwrap()
        .join_summary()
        .unwrap()
        .backend;
    let accepted = Joined {
        hive: HiveInfo {
            id: hive(0).into(),
            name: "app".to_owned(),
            backend,
            clone_config: Default::default(),
            urls: vec![],
            machines: vec![],
        },
        created: false,
        reason: String::new(),
        present: vec![],
    };
    join_locally(&located, &accepted).unwrap();
    let before = Found::read(&located.repo_path).unwrap();
    let old = UserState::load()
        .unwrap()
        .entry(before.key.as_deref().unwrap())
        .unwrap()
        .clone();
    let record = before.record.unwrap();
    assert_eq!(
        snapshot(&located, &old, None),
        expected["leave"][0]["prefix"]
    );

    if phase == "leave" {
        fs::write(
            saved,
            serde_json::to_vec(&(&old, None::<Entry>, &accepted)).unwrap(),
        )
        .unwrap();
        INTERRUPT.set(Some(LEAVE[index]));
        leave::detach(&located, Some(&record)).unwrap();
    } else {
        leave::detach(&located, Some(&record)).unwrap();
        let fresh = candidate(&located, &old);
        assert_eq!(
            snapshot(&located, &old, Some(&fresh)),
            expected["join"][0]["prefix"]
        );
        fs::write(
            saved,
            serde_json::to_vec(&(&old, Some(&fresh), &accepted)).unwrap(),
        )
        .unwrap();
        INTERRUPT.set(Some(JOIN[index]));
        join_locally(&located, &accepted).unwrap();
    }
    panic!("the command did not reach the interruption point");
}

fn candidate(located: &Located, old: &Entry) -> Entry {
    let settings = settings::load(&located.workspace_root, &located.repo_path).unwrap();
    let machine = join::joining_machine(located, Some("laptop"), &settings).unwrap();
    assert_ne!(machine.key(), old.key);
    Entry {
        key: machine.key().to_owned(),
        ..old.clone()
    }
}

fn snapshot(located: &Located, old: &Entry, fresh: Option<&Entry>) -> Value {
    let found = Found::read(&located.repo_path).unwrap();
    let state = UserState::load().unwrap();
    assert!(state.copies.len() <= 1, "{:?}", state.copies);
    let key_id = |key: &str| {
        if key == old.key {
            0
        } else {
            assert!(fresh.is_some_and(|entry| entry.key == key), "{key}");
            1
        }
    };
    let cid = found.config_id.as_ref().map(|id| {
        assert_eq!(id, &old.config_id);
        0
    });
    let record = found.record.as_ref().map(|record| {
        assert_eq!(record.hive, old.hive);
        assert_eq!(record.config_id, old.config_id);
        json!({"hive": 0, "cid": 0, "state": record.state})
    });
    let entry = state.copies.first().map(|entry| {
        assert_eq!(entry.path, old.path);
        assert_eq!(entry.hive, old.hive);
        assert_eq!(entry.config_id, old.config_id);
        json!({"key": key_id(&entry.key), "hive": 0, "cid": 0})
    });
    let retired = match fs::read(located.repo_path.join("musubi/retired-keys.json")) {
        Ok(bytes) => {
            let keys: Vec<String> = serde_json::from_slice(&bytes).unwrap();
            assert_eq!(keys, [old.key.as_str()]);
            true
        }
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => false,
        Err(err) => panic!("reading retired keys: {err}"),
    };
    json!({
        "repo": {"key": found.key.as_deref().map(key_id), "cid": cid, "record": record},
        "entry": entry,
        "marker": has_detach_marker(located, &old.key),
        "retired": retired,
        "oldCheck": check(old, &found).is_ok(),
        "freshCheck": fresh.is_some_and(|entry| check(entry, &found).is_ok()),
    })
}

fn has_detach_marker(located: &Located, old: &str) -> bool {
    let settings = settings::load(&located.workspace_root, &located.repo_path).unwrap();
    let loader = RepoLoader::init_from_file_system(
        &settings,
        &located.repo_path,
        &default_backend_factories(),
    )
    .unwrap();
    let store = loader.op_store();
    let mut heads = loader.op_heads_store().get_op_heads().block_on().unwrap();
    let mut seen = HashSet::new();
    while let Some(id) = heads.pop() {
        if !seen.insert(id.clone()) {
            continue;
        }
        let op = store.read_operation(&id).block_on().unwrap();
        if op.metadata.description == "musubi: detach this copy"
            && op
                .metadata
                .attributes
                .get(FORGET_ATTRIBUTE)
                .map(String::as_str)
                == Some(old)
        {
            return true;
        }
        heads.extend(op.parents);
    }
    false
}
