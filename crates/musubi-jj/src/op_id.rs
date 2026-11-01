//! The two kinds of operation id a machine holds (docs/internals/design.md, "Vocabulary"):
//! each is an ordinary jj operation id, and nothing in one tells it from the other, so these
//! keep a local id from being taken for a canonical one, or the reverse. jj-lib hands out
//! bare ids, which are wrapped where they come from.
//!
//! A canonical id can name an operation in more than one way, which [`HubOp`] and [`NodeOp`]
//! tell apart.
//!
//! [`HubOp`]: crate::records::HubOp
//! [`NodeOp`]: crate::node::NodeOp

use jj_lib::op_store::Operation;
use jj_lib::op_store::OperationId;

/// An operation in this machine's own jj op store, `.jj/repo/op_store`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocalOp(pub OperationId);

/// An operation in a canonical op store, the form of an operation that is replicated.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CanonicalOp(pub OperationId);

impl LocalOp {
    /// The parents of `op`, a local operation.
    pub fn parents_of(op: &Operation) -> Vec<Self> {
        op.parents.iter().cloned().map(Self).collect()
    }
}

impl CanonicalOp {
    /// The parents of `op`, a canonical operation.
    pub fn parents_of(op: &Operation) -> Vec<Self> {
        op.parents.iter().cloned().map(Self).collect()
    }
}
