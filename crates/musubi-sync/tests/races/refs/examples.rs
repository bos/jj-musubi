//! Regression examples: each replays a case through the same scenarios and checks as the
//! generated rules, so a failure here is a minimal case of one the state machine found.

use futures::executor::block_on;
use jj_lib::backend::CommitId;
use jj_lib::op_store::RefTarget;

use super::Commits;
use super::HERE;
use super::Machine;
use super::Realization;
use super::Ref;
use super::RefCommand;
use super::Refs;
use super::THERE;
use super::merged_expected;
use super::read;
use super::slot;
use crate::refs_model::Slot;

/// A pending git move leaves this machine's record behind while the other machine exports
/// a concurrent fetch's conflict. Its next command sees an unchanged physical ref and keeps
/// that conflict, even though importing against this machine's record would resolve it.
#[test]
fn a_pending_git_move_does_not_change_the_other_machines_import_record() {
    let mut refs = Refs::new();
    let Commits {
        root,
        base,
        one,
        two,
        three,
    } = refs.commits.clone();
    refs.git_moves_to(Ref::Origin, base.clone());
    refs.jj_sets(Ref::X, one);
    refs.git_moves_to(Ref::Origin, two);
    refs.musubi_realizes_with(Realization::concurrent(RefCommand::Fetches(three)));
    let (here, _) = read(&refs.fixture.load(HERE), Ref::Origin);
    let (there, git) = read(&refs.fixture.load(THERE), Ref::Origin);
    assert_eq!(here.r, there.r);
    assert!(!there.r.is_resolved());
    assert_eq!(there.k, git);
    assert_ne!(here.k, there.k);
    refs.musubi_realizes_with(Realization::following(RefCommand::Sets(Ref::X, root)));
    assert!(!refs.model.get(Ref::Origin).v.r.is_resolved());
}

/// Undoing a move from the root restores `x` there even though jj can't export it.
/// `git_refs` still matches `.git`, so the next ordinary command imports nothing.
#[test]
fn undo_of_an_unexportable_bookmark_keeps_it() {
    let mut refs = Refs::new();
    let Commits { root, two, .. } = refs.commits.clone();
    refs.jj_sets(Ref::X, root.clone());
    refs.jj_sets(Ref::X, two);
    refs.jj_restores_to(None);
    assert!(refs.model.get(Ref::X).restored);
    let y = refs.imported(Ref::Y);
    refs.jj_sets(Ref::Y, y);
    assert_eq!(refs.model.get(Ref::X).v.l, root);
}

/// Concurrent fetches conflict `y@origin`; a fetch here settles it, then a restore brings
/// back the conflict. Both machines keep the fetched value in `.git`. Ordinary commands
/// keep the conflict; an explicit fetch resolves it even though the physical ref is unchanged.
#[test]
fn restore_of_a_conflicted_remote_bookmark_waits_for_a_fetch() {
    let mut refs = Refs::new();
    let Commits {
        base,
        one,
        two,
        three,
        ..
    } = refs.commits.clone();
    refs.jj_fetches_from(two);
    refs.musubi_realizes_with(Realization::concurrent(RefCommand::Fetches(three)));
    assert!(!refs.model.get(Ref::Origin).v.r.is_resolved());
    let conflicted = refs.head();
    refs.jj_fetches_from(base.clone());
    refs.jj_restores_to(Some(conflicted));
    let origin = refs.model.get(Ref::Origin);
    assert!(!origin.v.r.is_resolved() && !origin.restored, "{origin:?}");
    assert_eq!(origin.g, base);
    let x = refs.model.get(Ref::X).v.l.clone();
    let moved = if x == base { one } else { base.clone() };
    refs.musubi_realizes_with(Realization::following(RefCommand::Sets(Ref::X, moved)));
    let y = refs.imported(Ref::Y);
    refs.jj_sets(Ref::Y, y);
    let origin = refs.model.get(Ref::Origin);
    assert!(!origin.v.l.is_resolved() && !origin.v.r.is_resolved());
    assert_eq!(origin.g, base);
    refs.jj_fetches_from(base.clone());
    let origin = refs.model.get(Ref::Origin);
    assert_eq!((&origin.v.l, &origin.v.r), (&base, &base));
}

/// A fetch beside a realization of a conflict, as Hegel found: after both machines have
/// `two`, this machine fetches `base` while the other, behind, fetches `one`, so that the
/// merge conflicts `y@origin`, with `one` as its expected value, and `jj undo` here brings the
/// conflict back once the undo's import has resolved it. Meanwhile the other machine, behind
/// again, fetches `base`, a term of the conflict, then realizes the undo beside its fetch,
/// and merges the two, keeping the fetch. musubi must leave `base` in that machine's `.git`:
/// had it written `one` for the realization, the other machine's next command, which moves
/// `x`, would import that as a move made with git, and move `y` back to `one`.
#[test]
fn realization_beside_a_fetch_keeps_the_fetch() {
    let mut refs = Refs::new();
    let Commits {
        root,
        base,
        one,
        two,
        ..
    } = refs.commits.clone();
    refs.musubi_realizes_with(Realization::following(RefCommand::Fetches(two)));
    refs.jj_fetches_from(base.clone());
    refs.musubi_realizes_with(Realization::concurrent(RefCommand::Fetches(one)));
    refs.jj_restores_to(None);
    assert!(!refs.model.get(Ref::Origin).v.r.is_resolved());
    refs.musubi_realizes_with(Realization::concurrent(RefCommand::Fetches(base.clone())));
    let (there, g) = read(&refs.fixture.load(THERE), Ref::Origin);
    assert_eq!((&there.r, &there.k, &g), (&base, &base, &base));
    refs.musubi_realizes_with(Realization::following(RefCommand::Sets(Ref::X, root)));
}

/// A resolved merge has its own expected value even if neither parent had it: absence
/// included, where there is no conflict side to choose. jj's merge that produces this is
/// pinned by `ref_laws::a_fetch_can_resolve_a_conflict_to_neither_side`.
#[test]
fn a_resolved_merge_is_its_own_expected_value() {
    let present = RefTarget::normal(CommitId::from_bytes(&[1; 20]));
    let parent = Machine {
        v: Slot {
            l: present.clone(),
            r: present.clone(),
            k: present.clone(),
            tr: true,
        },
        g: present.clone(),
        e: present.clone(),
        moved: false,
        restored: false,
    };
    for target in [
        RefTarget::absent(),
        RefTarget::normal(CommitId::from_bytes(&[2; 20])),
    ] {
        assert_eq!(
            merged_expected(
                |_| panic!("a resolved merge needs no side"),
                &target,
                [&parent, &parent],
                true
            ),
            target,
        );
    }
}

/// A fetch here beside a realization of a conflict, `beside_keeps_fetch` as musubi does it:
/// `y@origin` conflicts as in `restore_of_a_conflicted_remote_bookmark_waits_for_a_fetch`, a
/// fetch of `base` here resolves it, and both machines sync. This machine then restores the
/// conflict, whose expected value is `base`, and while the other machine, behind, moves `t` and
/// merges that with the restore, keeping the conflict, this machine fetches `two`, a term of
/// it. musubi realizes the other machine's merge beside the fetch, and must leave `two` in
/// `.git`, as the merge of the two keeps it: written for the realization alone, `base` would
/// be in `.git` and `two` in the record.
#[test]
fn realization_beside_a_fetch_here_keeps_the_fetch() {
    let mut refs = Refs::new();
    let Commits {
        base,
        one,
        two,
        three,
        ..
    } = refs.commits.clone();
    refs.jj_fetches_from(two.clone());
    refs.musubi_realizes_with(Realization::concurrent(RefCommand::Fetches(three)));
    assert!(!refs.model.get(Ref::Origin).v.r.is_resolved());
    let conflicted = refs.head();
    refs.jj_fetches_from(base.clone());
    // The other machine moves `x` from where it is, `one`, so that both sync.
    assert_eq!(refs.model.get(Ref::X).v.l, one);
    refs.musubi_realizes_with(Realization::following(RefCommand::Sets(
        Ref::X,
        base.clone(),
    )));
    refs.jj_restores_to(Some(conflicted));
    assert!(!refs.model.get(Ref::Origin).v.r.is_resolved());
    let fetch = RefCommand::Fetches(two.clone());
    refs.musubi_realizes_with(
        Realization::concurrent(RefCommand::Sets(Ref::T, two.clone())).beside(fetch),
    );
    let parents = refs.parents(&refs.head());
    assert_eq!(parents.len(), 2, "merged beside the fetch");
    let repo = refs.fixture.load(HERE);
    let conflicted = parents.iter().any(|op| {
        let op = block_on(repo.loader().load_operation(op)).unwrap();
        let view = block_on(op.view()).unwrap();
        !slot(view.store_view(), Ref::Origin).r.is_resolved()
    });
    assert!(conflicted, "the realization keeps the conflict");
    let origin = refs.model.get(Ref::Origin);
    assert_eq!((&origin.v.r, &origin.v.k, &origin.g), (&two, &two, &two));
}

/// jj exports a bookmark selected by the native merge even when physical refs match the
/// merged import records. Its ordinary import phase has no changes to publish first.
#[test]
fn an_unchanged_import_exports_a_bookmark_selected_by_a_merge() {
    let mut refs = Refs::new();
    let Commits {
        base, one, three, ..
    } = refs.commits.clone();
    refs.musubi_realizes_with(
        Realization::following(RefCommand::Fetches(three))
            .beside(RefCommand::Fetches(base.clone())),
    );
    refs.jj_sets_at_older_op(Ref::Y, one);
}

/// Non-head commands leave Git unchanged, even if their bookmark could be exported. A root
/// bookmark beside a move to `base` merges to a local conflict, while Git and both records
/// retain `one`. Simulating an export by the non-head command fails the native comparison.
#[test]
fn non_head_commands_leave_git_refs_unexported() {
    let mut refs = Refs::new();
    let Commits {
        root, base, one, ..
    } = refs.commits.clone();
    let id = |target: &RefTarget| target.as_normal().unwrap().clone();
    let conflict = RefTarget::from_legacy_form([id(&one)], [id(&root), id(&base)]);
    let (initial, git) = read(&refs.fixture.load(HERE), Ref::X);
    assert_eq!(
        initial,
        Slot {
            l: one.clone(),
            r: one.clone(),
            k: one.clone(),
            tr: true,
        }
    );
    assert_eq!(git, one);
    refs.jj_sets_at_older_op(Ref::X, root);
    refs.jj_sets_at_older_op(Ref::X, base);
    let (actual, git) = read(&refs.fixture.load(HERE), Ref::X);
    assert_eq!(
        actual,
        Slot {
            l: conflict,
            r: one.clone(),
            k: one.clone(),
            tr: true,
        }
    );
    assert_eq!(git, one);
}

/// A restore first exports what an earlier export left undone, as any head command
/// does, in a shorter form of the case Hegel found. `x` moves to the root, which jj can't
/// export, then the other machine moves it to `base`, which musubi realizes here while git's
/// lock on `refs/heads/x` is held, so that `.git` and the record keep `one`. `jj op restore`
/// to the operation with `x` at the root first writes `base` to `.git` and the record, then
/// restores `x` to the root and `x@git` to `one`, and can't export the root, so `.git` keeps
/// `base`, as jj does on one machine.
#[test]
fn a_restore_first_exports_what_a_lock_held_back() {
    let mut refs = Refs::new();
    let Commits {
        root, base, one, ..
    } = refs.commits.clone();
    refs.jj_sets(Ref::X, root.clone());
    refs.musubi_realizes_with(
        Realization::following(RefCommand::Sets(Ref::X, base.clone())).with_locked_export(),
    );
    let x = refs.model.get(Ref::X);
    assert_eq!((&x.v.l, &x.v.r, &x.v.k, &x.g), (&base, &one, &one, &one));
    refs.jj_restores_to(Some(refs.older.op.clone()));
    let x = refs.model.get(Ref::X);
    assert_eq!((&x.v.l, &x.v.r, &x.v.k, &x.g), (&root, &one, &base, &base));
    assert!(x.restored, "{x:?}");
}
