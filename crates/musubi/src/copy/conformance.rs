//! [`standing`], [`refine`] and [`check`] against the Lean model's
//! (`formal/Musubi/Copies.lean`), through the oracle (docs/internals/conformance.md, "Copies"):
//! every record, key, config-id and entry over two hives, two keys and two config-ids, with
//! every answer to `refine`'s two questions, in one request.

#![allow(clippy::unwrap_used)]

use std::path::PathBuf;

use serde_json::Value;
use serde_json::json;
use uuid::Uuid;

use super::Found;
use super::Standing;
use super::check;
use super::refine;
use super::standing;
use crate::config::Entry;
use crate::config::HiveConfig;
use crate::config::Membership;

#[path = "../../../musubi-core/tests/support/oracle.rs"]
#[allow(dead_code, clippy::unwrap_used)]
mod oracle;

use oracle::Oracle;

/// Each id, hive, key and config-id alike, is 0 or 1.
const IDS: [u64; 2] = [0, 1];

const STATES: [(Membership, &str); 3] = [
    (Membership::Joined, "joined"),
    (Membership::Left, "left"),
    (Membership::Removed, "removed"),
];

/// A record as the model has it: hive, config-id and state.
type Record = (u64, u64, usize);

/// An entry as the model has it: key, hive and config-id.
type ModelEntry = (u64, u64, u64);

struct Case {
    record: Option<Record>,
    key: Option<u64>,
    config_id: Option<u64>,
    entry: Option<ModelEntry>,
    /// Whether the entry's path holds the copy the entry names, and is this repository's
    /// directory: what [`refine`] is given.
    elsewhere_holds: bool,
    same_directory: bool,
}

fn options<T: Copy>(values: &[T]) -> Vec<Option<T>> {
    std::iter::once(None)
        .chain(values.iter().copied().map(Some))
        .collect()
}

fn cases() -> Vec<Case> {
    let mut records = vec![];
    let mut entries = vec![];
    for a in IDS {
        for b in IDS {
            for state in 0..STATES.len() {
                records.push((a, b, state));
            }
            for c in IDS {
                entries.push((a, b, c));
            }
        }
    }
    let mut cases = vec![];
    for record in options(&records) {
        for key in options(&IDS) {
            for config_id in options(&IDS) {
                for entry in options(&entries) {
                    for elsewhere_holds in [false, true] {
                        for same_directory in [false, true] {
                            cases.push(Case {
                                record,
                                key,
                                config_id,
                                entry,
                                elsewhere_holds,
                                same_directory,
                            });
                        }
                    }
                }
            }
        }
    }
    cases
}

fn hive(id: u64) -> Uuid {
    Uuid::from_u128(u128::from(id) + 1)
}

fn key(id: u64) -> String {
    format!("laptop#{id}")
}

fn config_id(id: u64) -> String {
    format!("config-{id}")
}

fn found(case: &Case) -> Found {
    Found {
        record: case.record.map(|(id, config, state)| HiveConfig {
            hive: hive(id),
            name: Some("app".to_owned()),
            hub: "hub".to_owned(),
            node: "laptop".to_owned(),
            config_id: config_id(config),
            state: STATES[state].0,
        }),
        key: case.key.map(key),
        config_id: case.config_id.map(config_id),
    }
}

fn entry(case: &Case) -> Option<Entry> {
    case.entry.map(|(k, id, config)| Entry {
        key: key(k),
        hive: hive(id),
        config_id: config_id(config),
        path: PathBuf::from("/src/app"),
    })
}

fn request(case: &Case) -> Value {
    let record = case
        .record
        .map(|(hive, cid, state)| json!({"hive": hive, "cid": cid, "state": STATES[state].1}));
    let entry = case
        .entry
        .map(|(key, hive, cid)| json!({"key": key, "hive": hive, "cid": cid}));
    json!({
        "repo": {"key": case.key, "cid": case.config_id, "record": record},
        "entry": entry,
        "elsewhereHolds": case.elsewhere_holds,
        "sameDirectory": case.same_directory,
    })
}

fn name(standing: Standing) -> &'static str {
    match standing {
        Standing::Outside => "outside",
        Standing::Removed => "removed",
        Standing::Copy => "copy",
        Standing::Broken => "broken",
        Standing::Duplicate => "duplicate",
        Standing::Unknown => "unknown",
    }
}

#[test]
fn decisions_conformance() {
    let cases = cases();
    let mut oracle = Oracle::spawn();
    let reply = oracle.call(&json!({
        "op": "copies",
        "cases": cases.iter().map(request).collect::<Vec<_>>(),
    }));
    assert_eq!(reply["ok"], true, "the oracle refused the cases: {reply}");
    let modelled = reply["copies"].as_array().unwrap();
    assert_eq!(modelled.len(), cases.len());
    let mut differ = vec![];
    for (case, modelled) in cases.iter().zip(modelled) {
        let found = found(case);
        let entry = entry(case);
        let standing = standing(&found, entry.as_ref());
        let computed = json!({
            "standing": name(standing),
            "refined": name(refine(standing, case.elsewhere_holds, case.same_directory)),
            "check": entry.as_ref().map(|entry| check(entry, &found).is_ok()),
        });
        let modelled = json!({
            "standing": modelled["standing"],
            "refined": modelled["refined"],
            "check": modelled["check"],
        });
        if computed != modelled {
            differ.push(format!(
                "{}: copy.rs says {computed}, the model {modelled}",
                request(case)
            ));
        }
    }
    assert!(
        differ.is_empty(),
        "{} of {} cases differ:\n{}",
        differ.len(),
        cases.len(),
        differ.join("\n")
    );
}
