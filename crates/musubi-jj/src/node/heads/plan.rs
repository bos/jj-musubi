//! What musubi decides about op heads it moved or will move, from the op heads, what it watches
//! and what it read of the operations, with no files and no jj: the Lean model's
//! `OpHeads.lean`, which the conformance test in `heads_conformance.rs` checks it against
//! (docs/internals/conformance.md, "Moving op heads").
//!
//! An operation is an `Id`; [`Graph`] says what musubi reads of one.

use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::Hash;

/// An op head musubi took out, with what it put in its place. Kept while one of those is still
/// an op head, since until then a `jj op abandon` that read the op heads before can still put
/// its rewrite of this one beside them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::node) struct Replaced<Id = crate::op_id::LocalOp> {
    /// The op head as it was.
    pub(in crate::node) head: Id,
    /// Its content but for its parents (`join::fingerprint`), which jj's rewrite of it keeps.
    pub(in crate::node) fingerprint: String,
    /// What musubi rewrote it to, op heads or not.
    pub(in crate::node) images: Vec<Id>,
    /// The op heads musubi put in its place: those of `images`, and what it put in on them,
    /// as a merge of them or a realization on one.
    pub(in crate::node) by: Vec<Id>,
}

/// What musubi reads of an operation.
pub(in crate::node) struct Node<Id> {
    pub(in crate::node) parents: Vec<Id>,
    /// The operation's content but for its parents.
    pub(in crate::node) fingerprint: String,
}

/// The operations musubi reads.
pub(in crate::node) trait Graph<Id> {
    type Error;

    fn read(&self, id: &Id) -> Result<Node<Id>, Self::Error>;

    /// Whether the translation cache knows the operation: musubi made it, or has translated
    /// it, so it is none of jj's rewrites.
    fn known(&self, id: &Id) -> bool;
}

/// What [`look`] takes out and puts back, worked out from the op heads `heads`.
#[derive(Debug, PartialEq, Eq)]
pub(in crate::node) struct Retiring<Id> {
    pub(in crate::node) heads: Vec<Id>,
    pub(in crate::node) out: Vec<Id>,
    pub(in crate::node) back: Vec<Id>,
    /// The watch as it is once they move.
    pub(in crate::node) kept: Vec<Replaced<Id>>,
    /// How many op heads jj rewrote.
    pub(in crate::node) rewritten: usize,
}

/// What to do about the op heads beside which a rewrite sits.
#[derive(Debug, PartialEq, Eq)]
pub(in crate::node) enum Look<Id> {
    /// Nothing; this is what musubi goes on watching.
    Nothing {
        kept: Vec<Replaced<Id>>,
    },
    Retire(Retiring<Id>),
}

/// Whether `a` and `b` are the same op heads, in any order: the check before a move, which
/// moves nothing unless the op heads are those musubi read, and after it.
pub(in crate::node) fn same<Id: Eq + Hash>(a: &[Id], b: &[Id]) -> bool {
    let a: HashSet<&Id> = a.iter().collect();
    let b: HashSet<&Id> = b.iter().collect();
    a == b
}

/// `ops` without duplicates, the first of each kept.
fn dedup<Id: Clone + Eq + Hash>(ops: impl IntoIterator<Item = Id>) -> Vec<Id> {
    let mut seen = HashSet::new();
    ops.into_iter()
        .filter(|op| seen.insert(op.clone()))
        .collect()
}

/// What replacing the op heads `read` with `new` takes out, as `from` rewrote them, and what it
/// puts in their place: for each of `old`, those of `read` not in `new`, its images among `new`
/// and what else of `new` is on them. Only operations of `new` that weren't read, which musubi
/// made, count. An op head with nothing put in its place isn't watched.
pub(in crate::node) fn entries<Id, G>(
    old: &[&Id],
    from: &HashMap<Id, Vec<Id>>,
    new: &[Id],
    read: &[Id],
    graph: &G,
) -> Result<Vec<Replaced<Id>>, G::Error>
where
    Id: Clone + Eq + Hash,
    G: Graph<Id>,
{
    let mut parents = vec![];
    for op in dedup(new.iter().filter(|op| !read.contains(op)).cloned()) {
        let node = graph.read(&op)?;
        parents.push((op, node.parents));
    }
    let mut replaced = vec![];
    for head in old {
        let images = from.get(*head).cloned().unwrap_or_default();
        let by: Vec<Id> = parents
            .iter()
            .filter(|(op, on)| images.contains(op) || on.iter().any(|p| images.contains(p)))
            .map(|(op, _)| op.clone())
            .collect();
        if by.is_empty() {
            continue;
        }
        replaced.push(Replaced {
            head: (*head).clone(),
            fingerprint: graph.read(head)?.fingerprint,
            images,
            by,
        });
    }
    Ok(replaced)
}

/// Watches `replaced` as well as `watched`; where one of `replaced` is itself what musubi put in
/// place of one it watches already, what replaced it takes its place there too.
pub(in crate::node) fn compose<Id: Clone + Eq + Hash>(
    mut watched: Vec<Replaced<Id>>,
    replaced: Vec<Replaced<Id>>,
) -> Vec<Replaced<Id>> {
    if replaced.is_empty() {
        return watched;
    }
    for earlier in &mut watched {
        for now in &replaced {
            for (ops, with) in [
                (&mut earlier.images, &now.images),
                (&mut earlier.by, &now.by),
            ] {
                if ops.contains(&now.head) {
                    ops.retain(|op| *op != now.head);
                    ops.extend(with.iter().cloned());
                    *ops = dedup(std::mem::take(ops));
                }
            }
        }
    }
    watched.extend(replaced);
    watched
}

/// What musubi does about the op heads `heads`, given what it `watched`: takes out the op heads
/// it put in place of one that `jj op abandon` rewrote since, and puts back what a merge or
/// realization it takes out was on.
///
/// An entry whose replacements are no longer op heads is forgotten: jj's rewrite of it, now,
/// would be beside a jj command's, as it would be on one machine. Of the rest, an entry is
/// *rewritten* if an op head that is none of what musubi put in has its fingerprint and another
/// id, and the translation cache doesn't know it. What is
/// taken out is every op head that is a replacement of a rewritten one. Of a merge or
/// realization taken out, the op heads it was on that are none of what musubi put in place of a
/// rewritten head, and not on one, go back: the rewrites of an op head the abandon left as it
/// was, or another machine's work.
pub(in crate::node) fn look<Id, G>(
    heads: &[Id],
    mut watched: Vec<Replaced<Id>>,
    graph: &G,
) -> Result<Look<Id>, G::Error>
where
    Id: Clone + Eq + Hash,
    G: Graph<Id>,
{
    watched.retain(|replaced| replaced.by.iter().any(|op| heads.contains(op)));
    let put: HashSet<&Id> = watched.iter().flat_map(|r| &r.by).collect();
    let beside: Vec<&Id> = heads.iter().filter(|h| !put.contains(h)).collect();
    let rewritten = if beside.is_empty() {
        HashSet::new()
    } else {
        rewritten(&watched, &beside, graph)?
    };
    if rewritten.is_empty() {
        return Ok(Look::Nothing { kept: watched });
    }
    let (stale, mut kept): (Vec<Replaced<Id>>, Vec<Replaced<Id>>) = watched
        .into_iter()
        .partition(|replaced| rewritten.contains(&replaced.head));
    let stale_images: HashSet<&Id> = stale.iter().flat_map(|r| &r.images).collect();
    let stale_by: HashSet<&Id> = stale.iter().flat_map(|r| &r.by).collect();
    let out: Vec<Id> = heads
        .iter()
        .filter(|head| stale_by.contains(head))
        .cloned()
        .collect();
    let mut back: Vec<Id> = vec![];
    for op in out.iter().filter(|op| !stale_images.contains(op)) {
        for parent in graph.read(op)?.parents {
            if stale_images.contains(&parent)
                || stale_by.contains(&parent)
                || heads.contains(&parent)
                || back.contains(&parent)
            {
                continue;
            }
            if graph
                .read(&parent)?
                .parents
                .iter()
                .all(|p| !stale_images.contains(p))
            {
                back.push(parent);
            }
        }
    }
    for replaced in &mut kept {
        replaced.by.retain(|op| !out.contains(op));
        replaced.by.extend(
            back.iter()
                .filter(|op| replaced.images.contains(op))
                .cloned(),
        );
    }
    Ok(Look::Retire(Retiring {
        heads: heads.to_vec(),
        out,
        back,
        kept,
        rewritten: stale.len(),
    }))
}

/// The heads among `watched` that jj rewrote: those an op head in `beside`, which musubi didn't put
/// in, is a rewrite of. jj's rewrite is new, so the translation cache knows no operation it just
/// wrote. Only the op heads themselves are compared: below one, an operation with the replaced
/// head's fingerprint may be what the head was rewritten from.
fn rewritten<Id, G>(
    watched: &[Replaced<Id>],
    beside: &[&Id],
    graph: &G,
) -> Result<HashSet<Id>, G::Error>
where
    Id: Clone + Eq + Hash,
    G: Graph<Id>,
{
    let mut found = HashSet::new();
    for head in beside.iter().filter(|head| !graph.known(head)) {
        let print = graph.read(head)?.fingerprint;
        for replaced in watched {
            if replaced.fingerprint == print && replaced.head != **head {
                found.insert(replaced.head.clone());
            }
        }
    }
    Ok(found)
}
