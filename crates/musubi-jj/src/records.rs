//! Records: the sets of canonical operations a hive dropped, each at once, in the order its hub
//! took them (docs/internals/design.md, "Abandoning operations"). Each names operations as the
//! hub's history had them before it. Two parties compare the records they took by count and
//! digest.

use jj_lib::content_hash::blake2b_hash;
use jj_lib::object_id::ObjectId as _;

use crate::op_id::CanonicalOp;

/// A canonical operation as the hub's history names it, with the hub's records dropped, and
/// nothing else: what the protocol speaks of. A machine that dropped operations it has yet to
/// publish names some of the history otherwise (`NodeOp`).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HubOp(pub CanonicalOp);

/// The operations a hive dropped at once, sorted, without duplicates.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Record(Vec<HubOp>);

impl Record {
    pub fn new(ops: impl IntoIterator<Item = HubOp>) -> Self {
        let mut ops: Vec<HubOp> = ops.into_iter().collect();
        ops.sort();
        ops.dedup();
        Self(ops)
    }

    pub fn ops(&self) -> &[HubOp] {
        &self.0
    }

    pub fn contains(&self, op: &HubOp) -> bool {
        self.0.binary_search(op).is_ok()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// A digest of a list of records: of no records, or of a digest and the record after it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RecordDigest(Vec<u8>);

impl RecordDigest {
    /// The digest of no records.
    pub fn root() -> Self {
        Self(vec![0; 64])
    }

    /// The digest of the records this one digests, then `record`.
    pub fn then(&self, record: &Record) -> Self {
        let parts: Vec<Vec<u8>> = std::iter::once(self.0.clone())
            .chain(record.ops().iter().map(|op| op.0.0.to_bytes()))
            .collect();
        Self(blake2b_hash(&parts).to_vec())
    }

    /// The digest of `records`.
    pub fn of(records: &[Record]) -> Self {
        records
            .iter()
            .fold(Self::root(), |prev, record| prev.then(record))
    }

    /// The digest as the protocol carries it.
    pub fn bytes(&self) -> &[u8] {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use jj_lib::op_store::OperationId;

    use super::*;

    fn op(byte: u8) -> HubOp {
        HubOp(CanonicalOp(OperationId::from_bytes(&[byte; 64])))
    }

    /// A digest tells records apart by their operations and their order, and is the same
    /// however the list is folded.
    #[test]
    fn digests_tell_records_apart() {
        let (a, b) = (op(1), op(2));
        let records = [Record::new([a.clone()]), Record::new([b.clone()])];
        let digest = RecordDigest::of(&records);
        assert_ne!(
            digest,
            RecordDigest::of(&[Record::new([b.clone()]), Record::new([a.clone()])])
        );
        assert_ne!(
            digest,
            RecordDigest::of(&[Record::new([a.clone(), b.clone()])])
        );
        assert_eq!(
            digest,
            RecordDigest::root().then(&records[0]).then(&records[1])
        );
        assert_eq!(RecordDigest::of(&[]), RecordDigest::root());
        assert_eq!(Record::new([b.clone(), a.clone(), b]).ops(), [op(1), op(2)]);
    }
}
