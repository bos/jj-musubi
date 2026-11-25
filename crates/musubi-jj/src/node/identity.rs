//! The keys a checkout used before detaching, in the order in which it retired them.

use std::collections::HashMap;
use std::fs;
use std::io;
use std::path::Path;

use jj_lib::op_store::OpStore;
use jj_lib::op_store::Operation;
use jj_lib::op_store::OperationId;
use pollster::FutureExt as _;

use super::NameMemos;
use super::NodeError;
use super::NodeRepo;
use crate::presence::FORGET_ATTRIBUTE;
use crate::workspaces::Machine;

const HISTORY: &str = "retired-keys.json";
const DETACH: &str = "musubi: detach this copy";

#[derive(Default)]
pub(super) struct History {
    retired: Vec<Machine>,
    // The newest detach in each native operation's ancestry, including itself.
    after: HashMap<OperationId, usize>,
    pub(super) names: HashMap<String, NameMemos>,
}

impl History {
    pub(super) fn load(dir: &Path) -> Result<Self, NodeError> {
        let path = dir.join(HISTORY);
        let error = |source| NodeError::Io {
            path: path.clone(),
            source,
        };
        let bytes = match fs::read(&path) {
            Ok(bytes) => bytes,
            Err(err) if err.kind() == io::ErrorKind::NotFound => return Ok(Self::default()),
            Err(err) => return Err(error(err)),
        };
        let keys: Vec<String> = serde_json::from_slice(&bytes)
            .map_err(io::Error::other)
            .map_err(error)?;
        Ok(Self {
            retired: keys.into_iter().map(Machine::from_key).collect(),
            ..Self::default()
        })
    }

    /// The machine that owned a native operation when it was written. A detach switches the
    /// key only for its descendants. The marker survives when jj rewrites operation parents
    /// and when musubi copies a shared operation back into the native history.
    pub(super) fn machine_for(
        &mut self,
        store: &dyn OpStore,
        op: &Operation,
    ) -> Result<Option<&Machine>, NodeError> {
        if self.retired.is_empty() {
            return Ok(None);
        }
        let mut pending: Vec<(OperationId, Option<Vec<OperationId>>)> =
            op.parents.iter().cloned().map(|id| (id, None)).collect();
        while let Some((id, parents)) = pending.pop() {
            if self.after.contains_key(&id) {
                continue;
            }
            if let Some(parents) = parents {
                let epoch = self.after_parents(&parents);
                self.after.insert(id, epoch);
                continue;
            }
            let op = store.read_operation(&id).block_on()?;
            if let Some(epoch) = self.detach_index(&op) {
                self.after.insert(id, epoch + 1);
            } else {
                pending.push((id, Some(op.parents.clone())));
                pending.extend(op.parents.into_iter().map(|id| (id, None)));
            }
        }
        Ok(self.retired.get(self.after_parents(&op.parents)))
    }

    pub(super) fn retired(&self, machine: &Machine) -> bool {
        self.retired.contains(machine)
    }

    pub(super) fn has_retired_keys(&self) -> bool {
        !self.retired.is_empty()
    }

    pub(super) fn retired_keys(&self) -> impl Iterator<Item = &str> {
        self.retired.iter().map(Machine::key)
    }

    fn after_parents(&self, parents: &[OperationId]) -> usize {
        parents
            .iter()
            .filter_map(|id| self.after.get(id).copied())
            .max()
            .unwrap_or(0)
    }

    fn detach_index(&self, op: &Operation) -> Option<usize> {
        if op.metadata.description != DETACH {
            return None;
        }
        let key = op.metadata.attributes.get(FORGET_ATTRIBUTE)?;
        self.retired.iter().position(|machine| machine.key() == key)
    }
}

impl NodeRepo {
    /// Ends this key's part in the checkout's history. The local operation keeps the working
    /// copies, and its shared view forgets the key. Commands from then on can use a fresh key
    /// without changing the shared form of any earlier operation.
    pub fn retire_machine(&mut self) -> Result<(), NodeError> {
        if self.identities.retired.last() == Some(&self.machine) {
            return Ok(());
        }
        let repo = self.merged_repo()?;
        let mut tx = repo.start_transaction();
        tx.set_attribute(FORGET_ATTRIBUTE.to_owned(), self.machine.key().to_owned());
        tx.commit(DETACH).block_on()?;
        let keys: Vec<_> = self
            .identities
            .retired
            .iter()
            .chain(std::iter::once(&self.machine))
            .map(Machine::key)
            .collect();
        let path = self.repo_path.join("musubi").join(HISTORY);
        let error = |source| NodeError::Io {
            path: path.clone(),
            source,
        };
        let bytes = serde_json::to_vec(&keys)
            .map_err(io::Error::other)
            .map_err(error)?;
        crate::files::replace(&path, &bytes).map_err(error)
    }

    /// Removes the active key after retiring it. A later join chooses a new one.
    pub fn clear_machine(repo_path: &Path) -> Result<(), NodeError> {
        let path = super::machine_path(repo_path);
        match fs::remove_file(&path) {
            Ok(()) => Ok(()),
            Err(err) if err.kind() == io::ErrorKind::NotFound => Ok(()),
            Err(source) => Err(NodeError::Io { path, source }),
        }
    }
}
