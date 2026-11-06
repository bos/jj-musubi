//! What a hub remembers about each hive for matching repositories to it: every remote URL
//! a copy has recorded when joining, and every root commit it has stored. Both only grow. The
//! index is a cache, updated as heads are accepted and rebuilt from the store's operations
//! and objects when it is missing.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use musubi_jj::files;
use musubi_jj::op_id::CanonicalOp;
use musubi_jj::remote_url::{JOIN_HIVE, JOIN_URL_PREFIX, JoinRemotes, RemoteBinding};
use musubi_jj::workspaces;
use serde::Deserialize;
use serde::Serialize;

use crate::store::HubStore;
use crate::store::StoreError;

const FILE: &str = "index.json";

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct HiveIndex {
    /// Remote URL hints recorded by copies when they explicitly join.
    pub urls: BTreeSet<String>,
    /// Every scoped name binding recorded by accepted joins. Multiple values are a conflict.
    pub remote_bindings: BTreeMap<String, BTreeSet<RemoteBinding>>,
    /// Hex ids of stored commits whose only parent is the root commit.
    pub roots: BTreeSet<String>,
    /// Machine keys with workspaces in the accepted head's view.
    pub machines: BTreeSet<String>,
}

impl HiveIndex {
    pub fn load(hive_dir: &Path) -> Option<Self> {
        serde_json::from_slice(&fs::read(hive_dir.join(FILE)).ok()?).ok()
    }

    pub fn save(&self, hive_dir: &Path) -> std::io::Result<()> {
        let json = serde_json::to_vec_pretty(self).map_err(std::io::Error::other)?;
        files::replace(&hive_dir.join(FILE), &json)
    }

    /// The index of everything `store` holds.
    pub fn rebuild(store: &HubStore) -> Result<Self, StoreError> {
        let mut index = Self::default();
        let ops: Vec<OperationId> = store
            .canonical()
            .operation_ids()?
            .into_iter()
            .map(|op| op.0)
            .collect();
        index.add(store, &ops, &[])?;
        index.machines = head_machines(store)?;
        Ok(index)
    }

    /// Adds what the operations accepted since `since` brought.
    pub fn update(&mut self, store: &HubStore, since: &OperationId) -> Result<(), StoreError> {
        let ops = store.ops_since(store.head().1, since)?;
        let haves: Vec<CommitId> = store
            .required_commits(std::slice::from_ref(since))?
            .into_iter()
            .collect();
        self.add(store, &ops, &haves)?;
        self.machines = head_machines(store)?;
        Ok(())
    }

    fn add(
        &mut self,
        store: &HubStore,
        ops: &[OperationId],
        haves: &[CommitId],
    ) -> Result<(), StoreError> {
        for id in ops {
            let operation = store.canonical().read_operation(&CanonicalOp(id.clone()))?;
            if operation
                .metadata
                .attributes
                .get(JOIN_HIVE)
                .map(String::as_str)
                == store.directory().file_name().and_then(|name| name.to_str())
            {
                for (name, binding) in
                    JoinRemotes::recorded_bindings(&operation.metadata.attributes)
                {
                    self.remote_bindings
                        .entry(name)
                        .or_default()
                        .insert(binding);
                }
            }
            self.urls.extend(
                operation
                    .metadata
                    .attributes
                    .iter()
                    .filter(|(key, _)| key.starts_with(JOIN_URL_PREFIX))
                    .map(|(_, url)| url.clone()),
            );
        }
        let wants: Vec<CommitId> = store.required_commits(ops)?.into_iter().collect();
        let objects = store.object_store();
        let absent = objects.missing(&wants)?;
        let present: Vec<CommitId> = wants.into_iter().filter(|c| !absent.contains(c)).collect();
        for root in objects.roots(&present, haves)? {
            self.roots.insert(root.hex());
        }
        Ok(())
    }
}

fn head_machines(store: &HubStore) -> Result<BTreeSet<String>, StoreError> {
    let head = CanonicalOp(store.head().1.clone());
    if head == *store.canonical().root_operation_id() {
        return Ok(BTreeSet::new());
    }
    let operation = store.canonical().read_operation(&head)?;
    let view = store.canonical().read_view(&operation.view_id)?;
    Ok(view
        .wc_commit_ids
        .keys()
        .filter_map(|key| workspaces::split_key(key.as_str()))
        .map(|(machine, _)| machine.to_owned())
        .collect())
}
