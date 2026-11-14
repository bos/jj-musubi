//! The two finite native fixtures against the executable lifecycle oracle. Raw immutable
//! bodies, retained fingerprints and native hash observations are inputs. Selected Rust
//! maps, policy booleans and effect order are comparison targets, never oracle premises.

use super::*;
use crate::oracle::Oracle;
use jj_lib::content_hash::blake2b_hash;
use jj_lib::op_store::{RefTarget, RemoteRefState};
use serde_json::json;

fn ref_target(target: &RefTarget) -> Value {
    // Preserve signs, order, multiplicity and absent terms; do not flatten to a commit set.
    json!({
        "removes": target.removes().map(|id| id.as_ref().map(|id| id.hex())).collect::<Vec<_>>(),
        "adds": target.adds().map(|id| id.as_ref().map(|id| id.hex())).collect::<Vec<_>>()
    })
}

fn raw_view(view: &View) -> Value {
    let mut heads = view.head_ids.iter().map(|id| id.hex()).collect::<Vec<_>>();
    heads.sort();
    let refs = |entries: &BTreeMap<jj_lib::ref_name::RefNameBuf, RefTarget>| {
        entries
            .iter()
            .map(|(name, target)| (name.as_str().to_owned(), ref_target(target)))
            .collect::<BTreeMap<_, _>>()
    };
    let remotes = view.remote_views.iter().map(|(name, remote)| {
        let entries = |entries: &BTreeMap<jj_lib::ref_name::RefNameBuf, jj_lib::op_store::RemoteRef>| {
            entries.iter().map(|(name, value)| (name.as_str().to_owned(), json!({
                "target": ref_target(&value.target),
                "state": match value.state { RemoteRefState::New => "new", RemoteRefState::Tracked => "tracked" }
            }))).collect::<BTreeMap<_, _>>()
        };
        (name.as_str(), json!({"bookmarks": entries(&remote.bookmarks), "tags": entries(&remote.tags)}))
    }).collect::<BTreeMap<_, _>>();
    json!({
        "heads": heads,
        "bookmarks": refs(&view.local_bookmarks), "tags": refs(&view.local_tags),
        "remotes": remotes,
        "gitRefs": view.git_refs.iter().map(|(name, target)|
            (name.as_str(), ref_target(target))).collect::<BTreeMap<_, _>>(),
        "gitHeads": view.git_heads.iter().map(|(name, target)|
            (name.as_str(), ref_target(target))).collect::<BTreeMap<_, _>>(),
        "workspaces": view.wc_commit_ids.iter().map(|(name, id)|
            json!([name.as_str(), id.hex()])).collect::<Vec<_>>()
    })
}

fn raw_body(id: &OperationId, op: &RawOperation, view: &View, original: Option<String>) -> Value {
    let metadata = &op.metadata;
    if !op.parents.is_empty() {
        assert_eq!(ViewId::new(blake2b_hash(view).to_vec()), op.view_id);
    }
    let mut without_parents = op.clone();
    without_parents.parents.clear();
    let fingerprint = OperationId::new(blake2b_hash(&without_parents).to_vec()).hex();
    let predecessors = op.commit_predecessors.as_ref().map(|entries| {
        entries
            .iter()
            .map(|(id, old)| json!([id.hex(), old.iter().map(|id| id.hex()).collect::<Vec<_>>()]))
            .collect::<Vec<_>>()
    });
    json!({
        "id": id.hex(), "viewId": op.view_id.hex(), "original": original,
        "parents": op.parents.iter().map(|id| id.hex()).collect::<Vec<_>>(),
        "fingerprint": fingerprint,
        "metadata": {
            "start": {"millis": metadata.time.start.timestamp.0, "offset": metadata.time.start.tz_offset},
            "end": {"millis": metadata.time.end.timestamp.0, "offset": metadata.time.end.tz_offset},
            "description": metadata.description, "username": metadata.username,
            "hostname": metadata.hostname, "isSnapshot": metadata.is_snapshot,
            "workspaceName": metadata.workspace_name.as_ref().map(|name| name.as_str()),
            "attributes": metadata.attributes
        },
        "predecessors": predecessors, "view": raw_view(view)
    })
}

fn record(before: &crate::records::RecordDigest, data: &Record) -> Value {
    json!({"before": jj_lib::hex_util::encode_hex(before.bytes()),
        "identity": jj_lib::hex_util::encode_hex(before.then(data).bytes()),
        "names": data.ops().iter().map(|id| id.0.0.hex()).collect::<Vec<_>>()})
}

fn records_chain(prefix: &RecordPrefix, data: &[Record]) -> Vec<Value> {
    let mut before = prefix.digest.clone();
    data.iter()
        .map(|entry| {
            let result = record(&before, entry);
            before = before.then(entry);
            result
        })
        .collect()
}

fn earlier(rows: Option<&Value>) -> Vec<Value> {
    rows.and_then(Value::as_array)
        .into_iter()
        .flatten()
        .map(|entry| {
            let bytes = entry[0]
                .as_str()
                .unwrap()
                .as_bytes()
                .chunks_exact(2)
                .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
                .collect::<Vec<_>>();
            let before = crate::records::RecordDigest::from_bytes(&bytes);
            let record_data = Record::new(entry[1].as_array().unwrap().iter().map(|id| {
                HubOp(CanonicalOp(
                    OperationId::try_from_hex(id.as_str().unwrap()).unwrap(),
                ))
            }));
            record(&before, &record_data)
        })
        .collect()
}

fn selected_physical(repo: &TestRepo) -> Value {
    let git = gix::open(repo.path()).unwrap();
    let target = git
        .try_find_reference("refs/heads/x")
        .unwrap()
        .map(|reference| reference.target().try_id().unwrap().to_string());
    json!({"scope": "refs/heads/x", "target": target})
}

fn raw_capture(node: &NodeRepo, repo: &TestRepo, inputs: &Inputs) -> Value {
    let identity_file = |name: &str| {
        inputs
            .evidence
            .get(std::path::Path::new(name))
            .map(|bytes| std::str::from_utf8(bytes).unwrap())
    };
    let evidence = |name: &str| {
        inputs
            .evidence
            .get(std::path::Path::new(name))
            .map(|bytes| std::str::from_utf8(bytes).unwrap())
            .unwrap_or("")
    };
    let originals = evidence("originals")
        .lines()
        .map(|line| {
            let fields = line.split_whitespace().collect::<Vec<_>>();
            assert_eq!(fields.len(), 2);
            json!({"original": fields[0], "fingerprint": fields[1]})
        })
        .collect::<Vec<_>>();
    let joins = evidence("joins")
        .lines()
        .map(|line| {
            let fields = line.split_whitespace().collect::<Vec<_>>();
            assert_eq!(fields.len(), 3);
            json!({"physical": fields[0], "canonical": fields[1], "fingerprint": fields[2]})
        })
        .collect::<Vec<_>>();
    let disk = records(&node.repo_path);
    let base = fs::read_to_string(node.repo_path.join("musubi/accepted_base"))
        .ok()
        .map(|text| text.trim().to_owned());
    let prefix = RecordPrefix::none();
    let (count, digest) = node.record_state();
    assert_eq!(
        count,
        node.applied_records().len() as u64,
        "the two finite fixtures have no opaque/pruned prefix"
    );
    let mut expected = BTreeMap::<String, BTreeMap<String, Value>>::new();
    for ((operation, name), value) in &inputs.expected {
        expected.entry(operation.0.hex()).or_default().insert(
            name.as_str().to_owned(),
            value.as_ref().map_or(Value::Null, ref_target),
        );
    }
    let expected = expected
        .into_iter()
        .map(|(operation, values)| json!({"operation": operation, "values": values}))
        .collect::<Vec<_>>();
    json!({
        "identitySourceState": {
            "schema": 1,
            "files": {
                "checkpoint": identity_file("records.json"),
                "steps": identity_file("superseded"),
                "hubRenamings": identity_file("hub-renamings"),
                "acceptedBase": identity_file("accepted_base"),
                "acceptedPush": identity_file("accepted_push")
            },
            "memory": node.native_identity_state()
        },
        "heads": inputs.heads.iter().map(|id| id.0.hex()).collect::<Vec<_>>(),
        "nativeManifest": inputs.native.keys().map(|id| id.0.hex()).collect::<Vec<_>>(),
        "canonicalManifest": inputs.canonical.keys().map(|id| id.0.hex()).collect::<Vec<_>>(),
        "physicalRoot": node.root_op_id().0.hex(), "canonicalRoot": node.canonical.root_operation_id().0.hex(),
        "native": inputs.native.iter().map(|(id, (op, view))| {
            if id != node.root_op_id() {
                assert_eq!(OperationId::new(blake2b_hash(op).to_vec()), id.0,
                    "raw native hash observation must match complete stored body");
            }
            raw_body(&id.0, op, view, None)
        }).collect::<Vec<_>>(),
        "canonical": inputs.canonical.iter().map(|(id, (op, view))| {
            let original = if id == node.canonical.root_operation_id() { id.0.clone() }
                else {
                    assert_eq!(OperationId::new(blake2b_hash(op).to_vec()), id.0);
                    let mut original = op.clone();
                    original.metadata.attributes.remove("musubi.presence");
                    let parents = original.metadata.attributes.remove("musubi.original-parents").unwrap();
                    original.parents = parents.split(' ').map(|id| OperationId::try_from_hex(id).unwrap()).collect();
                    let original = OperationId::new(blake2b_hash(&original).to_vec());
                    assert_eq!(original, node.canonical.original_id(id).unwrap());
                    original
                };
            raw_body(&id.0, op, view, Some(original.hex()))
        }).collect::<Vec<_>>(),
        "originals": originals, "joins": joins, "expected": expected,
        "physical": selected_physical(repo),
        "saved": {"base": base,
            "prefixCount": prefix.count, "prefixDigest": jj_lib::hex_util::encode_hex(prefix.digest.bytes()),
            "count": count, "digest": jj_lib::hex_util::encode_hex(digest.bytes()),
            "applied": records_chain(&prefix, node.applied_records()),
            "custody": earlier(disk.get("custody")), "earlier": earlier(disk.get("earlier")),
            "pending": node.pending_drops().ops().iter().map(|id| id.0.0.hex()).collect::<Vec<_>>(),
            "rawFile": disk},
        "receipt": inputs.receipt.as_ref().map(|receipt| {
            let records = records_chain(&receipt.prefix, &receipt.records);
            let identity = records.last().map(|record| record["identity"].clone())
                .unwrap_or_else(|| json!(jj_lib::hex_util::encode_hex(receipt.prefix.digest.bytes())));
            let mut locals = receipt.locals.iter().map(|(old, new)|
                (old.0.hex(), new.iter().map(|id| id.0.hex()).collect::<Vec<_>>())).collect::<Vec<_>>();
            locals.sort();
            json!({"heads": receipt.heads.iter().map(|id| id.0.hex()).collect::<Vec<_>>(),
                "prefixCount": receipt.prefix.count,
                "prefixDigest": jj_lib::hex_util::encode_hex(receipt.prefix.digest.bytes()),
                "identity": identity, "records": records, "locals": locals,
                "base": receipt.base.as_ref().map(|id| id.0.0.hex()), "switched": receipt.switched,
                "sources": receipt.sources.iter().map(|(a, b)|
                    json!([a.0.hex(), b.0.hex()])).collect::<Vec<_>>()})
        })
    })
}

fn strings_in(value: &Value, size: usize, found: &mut BTreeSet<String>) {
    match value {
        Value::String(text) => {
            if (text.starts_with('{') || text.starts_with('['))
                && let Ok(raw_file) = serde_json::from_str::<Value>(text)
            {
                strings_in(&raw_file, size, found);
            }
            for word in text.split_whitespace() {
                if word.len() == size && word.bytes().all(|byte| byte.is_ascii_hexdigit()) {
                    found.insert(word.to_owned());
                }
            }
        }
        Value::Array(values) => {
            for value in values {
                strings_in(value, size, found);
            }
        }
        Value::Object(values) => {
            for (key, value) in values {
                strings_in(&Value::String(key.clone()), size, found);
                strings_in(value, size, found);
            }
        }
        _ => {}
    }
}

fn request(
    kind: &str,
    me: &str,
    before: Value,
    after: Value,
    incoming: Value,
    target: Value,
) -> Value {
    let mut request = json!({"op": "nativeLifecycle", "schema": 1, "kind": kind, "me": me,
        "before": before, "after": after, "incoming": incoming, "target": target});
    let physical = ["before", "after"]
        .into_iter()
        .flat_map(|snapshot| {
            request[snapshot]["native"]
                .as_array()
                .unwrap()
                .iter()
                .map(|body| body["id"].as_str().unwrap().to_owned())
        })
        .collect::<BTreeSet<_>>();
    let canonical = ["before", "after"]
        .into_iter()
        .flat_map(|snapshot| {
            request[snapshot]["canonical"]
                .as_array()
                .unwrap()
                .iter()
                .map(|body| body["id"].as_str().unwrap().to_owned())
        })
        .collect::<BTreeSet<_>>();
    let mut original = BTreeSet::new();
    let mut commits = BTreeSet::new();
    strings_in(&request, 128, &mut original);
    strings_in(&request, 40, &mut commits);
    // Digests are a separate namespace. Include the root and every independently observed
    // raw digest; a physical/canonical hash can never be used without an explicit lookup.
    let digests = original.clone();
    request["ids"] = json!({"physical": physical, "canonical": canonical,
        "original": original, "commits": commits, "digests": digests});
    request
}

fn ordinal(request: &Value, domain: &str, id: &str) -> u64 {
    request["ids"][domain]
        .as_array()
        .unwrap()
        .iter()
        .position(|value| value == id)
        .unwrap() as u64
}

fn model_id(value: &Value) -> u64 {
    value["value"].as_u64().unwrap()
}

fn call(oracle: &mut Oracle, request: &Value) -> Value {
    if let Some(path) = std::env::var_os("MUSUBI_NATIVE_LIFECYCLE_DUMP") {
        let path = std::path::Path::new(&path);
        fs::create_dir_all(path).unwrap();
        fs::write(
            path.join(format!("{}.json", request["kind"].as_str().unwrap())),
            serde_json::to_vec_pretty(request).unwrap(),
        )
        .unwrap();
    }
    oracle.call(request)
}

fn model_bindings(value: &Value) -> BTreeMap<String, u64> {
    value
        .as_array()
        .unwrap()
        .iter()
        .map(|row| {
            let name = row[0]
                .as_array()
                .unwrap()
                .iter()
                .map(|c| c.as_str().unwrap())
                .collect::<String>();
            (name, row[1].as_u64().unwrap())
        })
        .collect()
}

#[test]
fn receipt_custody_materialization_matches_lifecycle_oracle() {
    let mut fx = Fixture::new();
    fx.repo
        .jj(&["describe", "-m", "unpublished native survivor"]);
    head(&mut fx.node);
    let before = capture(&fx.node);
    assert!(before.receipt.is_none());
    let raw_before = raw_capture(&fx.node, &fx.repo, &before);
    let prefix = RecordPrefix::none();
    assert!(fx.records.iter().any(|record| record.ops().len() > 1));
    let records = records_chain(&prefix, &fx.records);
    let incoming = json!({"prefixDigest": jj_lib::hex_util::encode_hex(prefix.digest.bytes()),
        "identity": records.last().unwrap()["identity"], "records": records});
    let effects = record_stores(&mut fx.node);
    fx.node.prepare_records(&prefix, &fx.records).unwrap();
    fx.node.settle().unwrap();
    let after = capture(&fx.node);
    let raw_after = raw_capture(&fx.node, &fx.repo, &after);
    let mut request = request(
        "receipt",
        fx.node.machine().key(),
        raw_before,
        raw_after,
        incoming,
        Value::Null,
    );
    request["observed"] = json!({"writes": effects.lock().unwrap().iter().filter_map(|event|
        match event {
            Event::Write { op, .. } => Some(OperationId::new(blake2b_hash(op).to_vec()).hex()),
            _ => None,
        }).collect::<Vec<_>>()});
    let mut oracle = Oracle::spawn();
    let reply = call(&mut oracle, &request);
    assert_eq!(
        reply["ok"], true,
        "native receipt interpretation/conformance gap: {reply}"
    );
    assert_eq!(reply["constructedActions"], true);
    assert_eq!(reply["sameRunCustody"], true);
    let receipt = after.receipt.as_ref().unwrap();
    assert_eq!(
        reply["computed"]["base"],
        receipt
            .base
            .as_ref()
            .map(|id| json!({"value": ordinal(&request, "canonical", &id.0.0.hex())}))
            .unwrap_or(Value::Null)
    );
    let expected_custody = fx
        .records
        .iter()
        .map(|record| {
            record
                .ops()
                .iter()
                .map(|id| ordinal(&request, "canonical", &id.0.0.hex()))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let computed_custody = reply["custody"]
        .as_array()
        .unwrap()
        .iter()
        .map(|record| {
            record["names"]
                .as_array()
                .unwrap()
                .iter()
                .map(model_id)
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    assert_eq!(computed_custody, expected_custody);
    let mut before_digest = prefix.digest.clone();
    let expected_disk = serde_json::to_value(
        fx.records
            .iter()
            .map(|record| {
                let expected = (
                    jj_lib::hex_util::encode_hex(before_digest.bytes()),
                    record
                        .ops()
                        .iter()
                        .map(|id| id.0.0.hex())
                        .collect::<Vec<_>>(),
                );
                before_digest = before_digest.then(record);
                expected
            })
            .collect::<Vec<_>>(),
    )
    .unwrap();
    let effects = effects.lock().unwrap();
    let writes = effects
        .iter()
        .filter_map(|event| match event {
            Event::Write { op, records } => {
                Some((OperationId::new(blake2b_hash(op).to_vec()), records))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(!writes.is_empty());
    let expected = reply["computed"]["nativeWrites"]
        .as_array()
        .unwrap()
        .iter()
        .map(|body| model_id(&body["id"]))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        writes
            .iter()
            .map(|(id, _)| ordinal(&request, "physical", &id.hex()))
            .collect::<BTreeSet<_>>(),
        expected
    );
    for (_, disk) in writes {
        assert_eq!(disk["custody"], expected_disk);
    }
    let mut incomplete = request.clone();
    incomplete["before"]["canonical"]
        .as_array_mut()
        .unwrap()
        .pop();
    assert_eq!(
        oracle.call(&incomplete)["ok"],
        false,
        "incomplete raw graph must fail interpretation"
    );
}

#[test]
fn second_name_publication_matches_lifecycle_oracle() {
    let mut fx = Fixture::new();
    fx.repo.jj(&["workspace", "forget", "b"]);
    fx.repo.jj(&["workspace", "rename", "b"]);
    fx.node.advance(&fx.incoming).unwrap();
    let child = fx.node.realize(&fx.child).unwrap();
    fx.node.settle().unwrap();
    let target_raw = raw(&fx.node, &child);
    let target = fx
        .node
        .own_of_view(target_raw.1.wc_commit_ids, &fx.child, &target_raw.0)
        .unwrap();
    assert_eq!(
        target.keys().map(|name| name.as_str()).collect::<Vec<_>>(),
        ["b"]
    );
    let path = fx._env.root().join("new-a");
    fx.repo.jj(&[
        "workspace",
        "add",
        "--name",
        "a",
        "-r",
        "b@",
        path.to_str().unwrap(),
    ]);
    fx.repo
        .jj(&["--ignore-working-copy", "bookmark", "set", "x", "-r", "a@"]);
    fx.repo.jj(&["--ignore-working-copy", "git", "export"]);
    // Actor prelude, before capture: establish complete original/parent evidence for the
    // real native command. The observer never canonicalizes or writes an identity.
    head(&mut fx.node);
    let before = capture(&fx.node);
    assert!(before.receipt.is_none());
    let current = fx.node.own_at_heads(&before.heads).unwrap();
    assert_eq!(
        current.keys().map(|name| name.as_str()).collect::<Vec<_>>(),
        ["a", "b"]
    );
    let expected = PerMachine::of(&raw(&fx.node, &before.heads[0]).1);
    let raw_before = raw_capture(&fx.node, &fx.repo, &before);
    let events = Arc::new(Mutex::new(Vec::new()));
    let observed = events.clone();
    let _observer = Observe::new(move |event| observed.lock().unwrap().push(event));
    let _effects = record_stores(&mut fx.node);
    let published = fx.node.advance(&fx.child).unwrap();
    let after = capture(&fx.node);
    let raw_after = raw_capture(&fx.node, &fx.repo, &after);
    let request = request(
        "publication",
        fx.node.machine().key(),
        raw_before,
        raw_after,
        Value::Null,
        json!(fx.child.0.hex()),
    );
    let reply = call(&mut Oracle::spawn(), &request);
    assert_eq!(
        reply["ok"], true,
        "native publication interpretation/conformance gap: {reply}"
    );
    assert_eq!(reply["constructedActions"], true);
    assert_eq!(reply["sameRunCustody"], true);
    let actual =
        |bindings: &BTreeMap<jj_lib::ref_name::WorkspaceNameBuf, jj_lib::backend::CommitId>| {
            bindings
                .iter()
                .map(|(name, id)| {
                    (
                        name.as_str().to_owned(),
                        ordinal(&request, "commits", &id.hex()),
                    )
                })
                .collect::<BTreeMap<_, _>>()
        };
    assert_eq!(
        model_bindings(&reply["git"]["currentOwned"]),
        actual(&current)
    );
    assert_eq!(
        model_bindings(&reply["git"]["targetOwned"]),
        actual(&target)
    );
    assert_eq!(reply["git"]["known"], true);
    assert_eq!(reply["git"]["present"], false);
    assert_eq!(reply["git"]["rootBase"], false);
    assert_eq!(reply["git"]["useCurrent"], true);
    assert_eq!(reply["mergeBeforeExport"], true);
    let events = events.lock().unwrap();
    let sources = events
        .iter()
        .find_map(|event| match event {
            Event::Sources(ids) => Some(ids),
            _ => None,
        })
        .unwrap();
    assert_eq!(sources, &before.heads);
    let export = events
        .iter()
        .position(|event| matches!(event, Event::Export(_)))
        .unwrap();
    let reread = events
        .iter()
        .rposition(|event| matches!(event, Event::Reread { .. }))
        .unwrap();
    assert!(reread < export);
    let Event::Export(first) = &events[export] else {
        unreachable!()
    };
    let (first_op, _) = raw(&fx.node, first);
    assert!(first_op.parents.len() > 1);
    assert_eq!(
        first_op
            .parents
            .iter()
            .map(|id| ordinal(&request, "physical", &id.hex()))
            .collect::<Vec<_>>(),
        reply["orderedMergeInputs"]
            .as_array()
            .unwrap()
            .iter()
            .map(model_id)
            .collect::<Vec<_>>()
    );
    assert_eq!(PerMachine::of(&raw(&fx.node, &published).1), expected);
    assert_eq!(request["before"]["physical"], request["after"]["physical"]);
}
