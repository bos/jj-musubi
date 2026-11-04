//! Normalizing peer encodings and checking that they name exactly what jj decodes.

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::Operation;
use jj_lib::op_store::RemoteRef;
use jj_lib::op_store::RemoteView;
use jj_lib::op_store::View;

use super::CanonicalError;
use crate::protobuf::next_field;

/// What an operation or view arriving in a bundle turned out to be, once decoded.
pub(super) struct Admitted {
    pub(super) kind: &'static str,
    /// The error for one whose encoding names other commits than its decoding does.
    pub(super) malformed: fn(String) -> CanonicalError,
    pub(super) expected: String,
    pub(super) actual: String,
    /// Whether its encoding names exactly the commits its decoding does.
    pub(super) names_its_commits: bool,
}

/// Whether an operation or view is what it says it is, and may be stored.
pub(super) fn admit(checked: Admitted) -> Result<(), CanonicalError> {
    let Admitted {
        kind,
        malformed,
        expected,
        actual,
        names_its_commits,
    } = checked;
    if expected != actual {
        Err(CanonicalError::HashMismatch {
            kind,
            expected,
            actual,
        })
    } else if !names_its_commits {
        Err(malformed(expected))
    } else {
        Ok(())
    }
}

/// A view's bytes as a function of its content alone, which view deltas are between, and
/// which the store holds. jj encodes `head_ids`, a set, and `wc_commit_ids`, a map, in
/// hash order, so two stores can be given different bytes for one view. Sorting the
/// top-level fields, and the entries of those two among them, leaves nothing to chance,
/// without decoding the view. The result is a valid encoding of the same view, for any
/// encoding this jj-lib writes. `None` if `encoded` isn't a protobuf message.
pub(super) fn normal_view(encoded: &[u8]) -> Option<Vec<u8>> {
    /// `head_ids` and `wc_commit_ids`.
    const UNORDERED: [u32; 2] = [1, 8];
    let mut fields = top_level_fields(encoded)?;
    // Stable, so other repeated fields keep their order.
    fields.sort_by(|(number, bytes), (other_number, other_bytes)| {
        number.cmp(other_number).then_with(|| {
            if UNORDERED.contains(number) {
                bytes.cmp(other_bytes)
            } else {
                std::cmp::Ordering::Equal
            }
        })
    });
    let mut normal = Vec::with_capacity(encoded.len());
    for (_, bytes) in fields {
        normal.extend_from_slice(bytes);
    }
    Some(normal)
}

/// Calls `each` with the number and payload of every length-delimited field of an encoded
/// message, in order; fields of other wire types hold no id or message. `None` if the
/// message, or `each`, finds it malformed.
pub(super) fn each_field<'a>(
    mut bytes: &'a [u8],
    mut each: impl FnMut(u32, &'a [u8]) -> Option<()>,
) -> Option<()> {
    while !bytes.is_empty() {
        let (key, payload) = next_field(&mut bytes)?;
        if key & 7 == 2 {
            each(u32::try_from(key >> 3).ok()?, payload)?;
        }
    }
    Some(())
}

/// The last field `number` of an encoded message, which is what prost decodes a singular
/// field as, if there is one.
fn last_field(bytes: &[u8], number: u32) -> Option<Option<&[u8]>> {
    let mut last = None;
    each_field(bytes, |n, payload| {
        if n == number {
            last = Some(payload);
        }
        Some(())
    })?;
    Some(last)
}

/// An encoded operation's view id.
pub(super) fn encoded_view_id(op: &[u8]) -> Option<&[u8]> {
    last_field(op, 1)?
}

/// Where [`encoded_op_commits`] and [`encoded_view_commits`] report each id they find,
/// which ends the walk by returning `None`.
type Found<'a, 'f> = dyn FnMut(&'a [u8]) -> Option<()> + 'f;

fn id<'a>(bytes: &'a [u8], found: &mut Found<'a, '_>) -> Option<()> {
    found(bytes)
}

/// A singular id field of the message `bytes`, which prost decodes as empty when absent,
/// and jj then takes for a commit.
fn required_id<'a>(bytes: &'a [u8], number: u32, found: &mut Found<'a, '_>) -> Option<()> {
    id(last_field(bytes, number)?.unwrap_or_default(), found)
}

/// In the message `bytes`, each field `number`, through `each`.
fn field<'a>(
    bytes: &'a [u8],
    number: u32,
    found: &mut Found<'a, '_>,
    each: fn(&'a [u8], &mut Found<'a, '_>) -> Option<()>,
) -> Option<()> {
    each_field(bytes, |n, payload| {
        if n == number {
            each(payload, found)?;
        }
        Some(())
    })
}

/// `RefConflict.Term` and `RefTargetTerm`: an id, if present.
fn term<'a>(bytes: &'a [u8], found: &mut Found<'a, '_>) -> Option<()> {
    field(bytes, 1, found, id)
}

/// `RefTarget`: an id (legacy), a `RefConflictLegacy` of ids, or a `RefConflict` of terms,
/// its removes and adds alike.
fn target<'a>(bytes: &'a [u8], found: &mut Found<'a, '_>) -> Option<()> {
    each_field(bytes, |number, payload| match number {
        1 => id(payload, found),
        2 => each_field(payload, |number, payload| match number {
            1 | 2 => id(payload, found),
            _ => Some(()),
        }),
        3 => each_field(payload, |number, payload| match number {
            1 | 2 => term(payload, found),
            _ => Some(()),
        }),
        _ => Some(()),
    })
}

/// Calls `found` with every commit id an encoded operation holds: its recorded predecessors
/// (`CommitPredecessors`), with the fields this jj-lib's `simple_op_store.proto` gives them.
/// An id is reported as jj decodes it, so an absent one that jj decodes as empty is reported
/// empty, for the caller to refuse.
pub(super) fn encoded_op_commits<'a>(op: &'a [u8], found: &mut Found<'a, '_>) -> Option<()> {
    each_field(op, |number, payload| match number {
        4 => {
            required_id(payload, 1, found)?;
            field(payload, 2, found, id)
        }
        _ => Some(()),
    })
}

/// [`encoded_op_commits`] for an encoded view, with legacy fields included: every commit
/// that jj's decoding of it refers to, and none it doesn't in what this jj-lib writes (see
/// the test `encoded_commits_are_referenced_commits`).
pub(super) fn encoded_view_commits<'a>(view: &'a [u8], found: &mut Found<'a, '_>) -> Option<()> {
    each_field(view, |number, payload| match number {
        // `head_ids`.
        1 => id(payload, found),
        // The legacy `wc_commit_id` and `git_head_legacy`, which jj reads only if not empty.
        2 | 7 if !payload.is_empty() => id(payload, found),
        // `wc_commit_ids`, a map entry with the id as its value.
        8 => required_id(payload, 2, found),
        // `Bookmark`: its local target, and its `RemoteBookmark`s' (legacy).
        5 => each_field(payload, |number, payload| match number {
            2 => target(payload, found),
            3 => field(payload, 2, found, target),
            _ => Some(()),
        }),
        // `Tag`, and `GitHead`.
        6 | 13 => field(payload, 2, found, target),
        // `RemoteView`: its bookmarks' and tags' `RemoteRef`s, each with its terms.
        11 => each_field(payload, |number, payload| match number {
            2 | 3 => field(payload, 2, found, term),
            _ => Some(()),
        }),
        // `GitRef`: a target, or without one its id (legacy).
        3 => match last_field(payload, 3)? {
            Some(_) => field(payload, 3, found, target),
            None => required_id(payload, 2, found),
        },
        // The legacy `git_head`.
        9 => target(payload, found),
        _ => Some(()),
    })
}

/// Every commit a view refers to, as jj decodes it. It is taken apart field by field, so that
/// a jj-lib with more of them fails to build here, and whoever upgrades it checks
/// [`encoded_view_commits`] against the new schema.
pub(super) fn view_commit_ids(view: &View) -> impl Iterator<Item = &CommitId> {
    let View {
        head_ids,
        local_bookmarks,
        local_tags,
        remote_views,
        git_refs,
        git_heads,
        wc_commit_ids,
    } = view;
    let remote_targets = remote_views
        .values()
        .flat_map(|RemoteView { bookmarks, tags }| {
            bookmarks
                .values()
                .chain(tags.values())
                .map(|RemoteRef { target, state: _ }| target)
        });
    let targets = local_bookmarks
        .values()
        .chain(local_tags.values())
        .chain(git_refs.values())
        .chain(git_heads.values())
        .chain(remote_targets);
    head_ids
        .iter()
        .chain(targets.flat_map(|target| target.iter().flatten()))
        .chain(wc_commit_ids.values())
}

/// [`view_commit_ids`] for an operation: its recorded predecessors.
pub(super) fn op_commit_ids(op: &Operation) -> impl Iterator<Item = &CommitId> {
    let Operation {
        view_id: _,
        parents: _,
        metadata: _,
        commit_predecessors,
    } = op;
    commit_predecessors
        .iter()
        .flatten()
        .flat_map(|(commit, predecessors)| std::iter::once(commit).chain(predecessors))
}

/// Whether `encoded`, walked by `walk`, names exactly the commits that jj's decoding of it
/// refers to, as everything this jj-lib encodes does. Reading stored views' and operations'
/// commits from their encodings (see [`super::CanonicalStore::required_commits`]) relies on it, so
/// nothing else is stored: a peer's encoding that jj reads differently, such as one with a
/// legacy field contradicting its replacement, would otherwise stand for the view's id.
pub(super) fn names_decoded_commits<'a, 'b>(
    encoded: &'a [u8],
    walk: fn(&'a [u8], &mut Found<'a, '_>) -> Option<()>,
    decoded: impl Iterator<Item = &'b CommitId>,
) -> bool {
    let mut named = vec![];
    if walk(encoded, &mut |id| {
        named.push(id);
        Some(())
    })
    .is_none()
    {
        return false;
    }
    let mut decoded: Vec<&[u8]> = decoded.map(|id| id.as_bytes()).collect();
    for ids in [&mut named, &mut decoded] {
        ids.sort_unstable();
        ids.dedup();
    }
    named == decoded
}

/// The top-level fields of a protobuf message, each with its number and its encoding,
/// key included, in order.
fn top_level_fields(mut bytes: &[u8]) -> Option<Vec<(u32, &[u8])>> {
    let mut fields = vec![];
    while !bytes.is_empty() {
        let start = bytes;
        let (key, _) = next_field(&mut bytes)?;
        let number = u32::try_from(key >> 3).ok()?;
        fields.push((number, &start[..start.len() - bytes.len()]));
    }
    Some(fields)
}
