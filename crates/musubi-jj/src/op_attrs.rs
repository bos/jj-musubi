//! Typed access to the attributes musubi and jj record on an operation.
//!
//! Operations are hashed and replicated, so each method reads or writes exactly the key and
//! value string the attribute has always had: a change here changes operation ids.

use std::borrow::Borrow;
use std::borrow::BorrowMut;
use std::collections::BTreeMap;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;

use crate::canonical::origin;
use crate::node::CANONICAL_ATTRIBUTE;
use crate::node::CHECKPOINT_ATTRIBUTE;
use crate::node::FIXUP_ATTRIBUTE;
use crate::node::INTENT_ATTRIBUTE;
use crate::node::LOCAL_WORKSPACES;
use crate::node::PublicationError;
use crate::node::RESERVED_WORKSPACES;
use crate::op_id::CanonicalOp;

/// What jj records of the command that made an operation, as one string.
const ARGS: &str = "args";
const RECONCILED_FROM: &str = "musubi.reconciled-from";

/// A view of operation attributes: an operation's `metadata.attributes`, shared or mutable, or
/// the attributes a transaction will set.
pub(crate) struct OpAttrs<M>(pub M);

impl<M: Borrow<BTreeMap<String, String>>> OpAttrs<M> {
    fn has(&self, key: &str) -> bool {
        self.0.borrow().contains_key(key)
    }

    /// Whether this is a fix-up, which changes no view.
    pub fn is_fixup(&self) -> bool {
        self.has(FIXUP_ATTRIBUTE)
    }

    /// Whether this is a step of a publication cleanup's checkpoint.
    pub fn is_checkpoint(&self) -> bool {
        self.has(CHECKPOINT_ATTRIBUTE)
    }

    /// Whether this declares the commits it retains on purpose.
    pub fn has_intent(&self) -> bool {
        self.has(INTENT_ATTRIBUTE)
    }
}

/// Readers whose answer borrows from the attributes themselves, not from the view.
impl<'a> OpAttrs<&'a BTreeMap<String, String>> {
    fn get(&self, key: &str) -> Option<&'a str> {
        self.0.get(key).map(String::as_str)
    }

    /// The hex id of the canonical operation this local one realizes, as marked.
    pub fn canonical(&self) -> Option<&'a str> {
        self.get(CANONICAL_ATTRIBUTE)
    }

    /// The commits this declares it retains on purpose, decoded one at a time so that a
    /// caller checking each stops at the first that fails, or `None` without a declaration.
    pub fn intent(
        &self,
    ) -> Result<
        Option<impl Iterator<Item = Result<CommitId, PublicationError>> + use<>>,
        PublicationError,
    > {
        let Some(text) = self.get(INTENT_ATTRIBUTE) else {
            return Ok(None);
        };
        let ids: Vec<String> =
            serde_json::from_str(text).map_err(PublicationError::MalformedIntent)?;
        Ok(Some(ids.into_iter().map(|id| {
            CommitId::try_from_hex(&id).ok_or(PublicationError::InvalidIntentCommit)
        })))
    }

    /// The command jj records as having made this.
    pub fn args(&self) -> Option<&'a str> {
        self.get(ARGS)
    }

    /// The presence a contraction stamped this with.
    pub fn presence(&self) -> Option<&'a str> {
        self.get(origin::PRESENCE)
    }
}

impl<M: BorrowMut<BTreeMap<String, String>>> OpAttrs<M> {
    fn set(&mut self, key: &str, value: String) {
        self.0.borrow_mut().insert(key.to_owned(), value);
    }

    pub fn set_canonical(&mut self, id: &CanonicalOp) {
        self.set(CANONICAL_ATTRIBUTE, id.0.hex());
    }

    pub fn remove_reconciled_from(&mut self) {
        self.0.borrow_mut().remove(RECONCILED_FROM);
    }

    /// Marks step `step` of the checkpoint of the cleanup reviewed as `token`.
    pub fn set_checkpoint(&mut self, token: &str, step: usize) {
        self.set(CHECKPOINT_ATTRIBUTE, format!("{token}:{step}"));
    }

    /// Declares `ids` retained on purpose, as a JSON array of hex ids in the order given.
    pub fn set_intent<'a>(
        &mut self,
        ids: impl IntoIterator<Item = &'a CommitId>,
    ) -> Result<(), serde_json::Error> {
        let hex: Vec<_> = ids.into_iter().map(CommitId::hex).collect();
        let text = serde_json::to_string(&hex)?;
        self.set(INTENT_ATTRIBUTE, text);
        Ok(())
    }

    /// Drops the workspace names only this copy knows, which no canonical operation carries.
    pub fn remove_private_workspaces(&mut self) {
        let attributes = self.0.borrow_mut();
        attributes.remove(LOCAL_WORKSPACES);
        attributes.remove(RESERVED_WORKSPACES);
    }

    pub fn args_mut(&mut self) -> Option<&mut String> {
        self.0.borrow_mut().get_mut(ARGS)
    }

    pub fn set_presence(&mut self, stamp: String) {
        self.set(origin::PRESENCE, stamp);
    }

    pub fn remove_presence(&mut self) {
        self.0.borrow_mut().remove(origin::PRESENCE);
    }
}
