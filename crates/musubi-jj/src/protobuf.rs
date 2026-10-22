//! Protobuf's wire format read directly, for what decoding with prost hides: an encoding's
//! exact bytes, and fields its schema doesn't know.

/// Takes a varint off the front of `bytes`.
pub(crate) fn varint(bytes: &mut &[u8]) -> Option<u64> {
    let mut value = 0;
    for shift in (0..64).step_by(7) {
        let (&byte, rest) = bytes.split_first()?;
        *bytes = rest;
        value |= u64::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return Some(value);
        }
    }
    None
}

/// Takes a field off the front of an encoded message: its key, and its payload, which for a
/// length-delimited field is what its length covers. `None` if it is malformed, or of a
/// wire type no message uses (a group's, or one protobuf doesn't define).
pub(crate) fn next_field<'a>(bytes: &mut &'a [u8]) -> Option<(u64, &'a [u8])> {
    let key = varint(bytes)?;
    let start = *bytes;
    let len = match key & 7 {
        0 => {
            varint(bytes)?;
            return Some((key, &start[..start.len() - bytes.len()]));
        }
        1 => 8,
        2 => usize::try_from(varint(bytes)?).ok()?,
        5 => 4,
        _ => return None,
    };
    let (payload, rest) = bytes.split_at_checked(len)?;
    *bytes = rest;
    Some((key, payload))
}
