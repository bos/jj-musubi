//! An operation's original parents distinguish originals even when all their other fields
//! agree. Contraction preserves them; a fresh operation replaces any supplied attribute.

use jj_lib::content_hash::blake2b_hash;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::Operation;
use jj_lib::op_store::OperationId;

use super::CanonicalError;
use super::log::ID_LEN;

pub(crate) const ORIGINAL_PARENTS: &str = "musubi.original-parents";

pub(super) fn fresh(op: &Operation) -> Operation {
    let mut op = op.clone();
    if op.parents.is_empty() {
        op.parents.push(OperationId::from_bytes(&[0; ID_LEN]));
    }
    let parents = op
        .parents
        .iter()
        .map(OperationId::hex)
        .collect::<Vec<_>>()
        .join(" ");
    op.metadata
        .attributes
        .insert(ORIGINAL_PARENTS.to_owned(), parents);
    op
}

/// The original operation's hash, recomputed from immutable material rather than trusting
/// a peer's claimed hash. Original parents need not remain in the contracted history.
pub(super) fn identity(op: &Operation) -> Result<OperationId, CanonicalError> {
    let malformed = || CanonicalError::MalformedOperation("original parents".to_owned());
    let mut original = op.clone();
    let parents = original
        .metadata
        .attributes
        .remove(ORIGINAL_PARENTS)
        .ok_or_else(malformed)?;
    original.parents = parents
        .split(' ')
        .map(|hex| {
            if hex.len() != ID_LEN * 2
                || !hex
                    .bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            {
                return Err(malformed());
            }
            OperationId::try_from_hex(hex).ok_or_else(malformed)
        })
        .collect::<Result<_, _>>()?;
    Ok(OperationId::new(blake2b_hash(&original).to_vec()))
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]
    use jj_lib::op_store::ViewId;

    use super::*;

    #[test]
    fn original_parent_encoding_is_pinned_and_cannot_be_supplied_by_a_caller() {
        let mut op = Operation::make_root(ViewId::from_bytes(&[1; ID_LEN]));
        op.parents = vec![OperationId::from_bytes(&[2; ID_LEN])];
        let original = OperationId::new(blake2b_hash(&op).to_vec());
        op.metadata
            .attributes
            .insert(ORIGINAL_PARENTS.to_owned(), "forged".to_owned());
        let written = fresh(&op);
        assert_eq!(identity(&written).unwrap(), original);
        let encoded = super::super::codec::encode_operation(&written);
        assert_eq!(
            encoded,
            [
                vec![0x0a, 64],
                vec![1; 64],
                vec![0x12, 64],
                vec![2; 64],
                vec![
                    0x1a, 0xa3, 0x01, 0x0a, 0, 0x12, 0, 0x32, 0x9c, 0x01, 0x0a, 0x17
                ],
                b"musubi.original-parents".to_vec(),
                vec![0x12, 0x80, 0x01],
                b"02".repeat(64),
                vec![0x28, 1],
            ]
            .concat()
        );
    }
}
