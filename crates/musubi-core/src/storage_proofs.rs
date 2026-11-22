//! Bounded checks of the production push handler, not a second implementation of it.
//!
//! See docs/internals/bounded-verification.md for the adapter contract, bounds and limits.

use crate::hub::CasOutcome;
use crate::hub::HandledBy;
use crate::hub::HubStorage;
use crate::hub::Push;
use crate::message::Head;
use crate::message::HeadKind;
use crate::message::OpEntry;
use crate::message::Reply;

/// Root 0, operation 1 (parent 0), operation 2 (parent 0 or 1). Each nonroot operation
/// requires its own object. Bits 0 and 1 stand for operations/objects 1 and 2.
struct Storage {
    child: bool,
    ops: u8,
    objects: u8,
    head: u8,
    seq: u64,
    faults: bool,
}

impl Storage {
    fn fail(&self) -> bool {
        self.faults && kani::any()
    }

    fn closed(&self, op: u8) -> bool {
        let required = match op {
            0 => 0,
            1 => 1,
            2 if self.child => 3,
            2 => 2,
            _ => unreachable!("only three operations"),
        };
        self.ops & required == required && self.objects & required == required
    }

    fn descends_from(&self, ancestor: u8, op: u8) -> bool {
        ancestor == 0 || ancestor == op || (ancestor == 1 && op == 2 && self.child)
    }

    /// An import can leave any subset of the offered items on error, including all of
    /// them. Success stores everything offered. It never removes stored content.
    fn import(&self, offered: u8) -> (u8, Result<(), ()>) {
        if self.fail() {
            (offered & kani::any::<u8>(), Err(()))
        } else {
            (offered, Ok(()))
        }
    }
}

impl HubStorage for Storage {
    type Op = u8;
    type Attachment = u8;
    type Error = ();

    fn head(&self) -> Head<u8> {
        Head {
            seq: self.seq,
            head: self.head,
        }
    }

    fn set_head(&mut self, seq: u64, head: &u8) -> Result<(), ()> {
        if self.fail() {
            return Err(());
        }
        // These are caller obligations, not assumptions that discard failing paths.
        assert_eq!(seq, self.seq + 1);
        assert!(self.closed(*head));
        assert!(self.descends_from(self.head, *head));
        self.seq = seq;
        self.head = *head;
        Ok(())
    }

    fn store_ops(&mut self, ops: &[u8], attachment: &u8) -> Result<(), ()> {
        assert_eq!(ops, &[1, 2]);
        assert_eq!(*attachment, 3);
        let (stored, result) = self.import(*attachment);
        self.ops |= stored;
        result
    }

    fn store_objects(&mut self, _: &[u8], attachment: &u8) -> Result<(), ()> {
        let (stored, result) = self.import(*attachment);
        self.objects |= stored;
        result
    }

    fn is_closed(&self, op: &u8) -> Result<bool, ()> {
        if self.fail() {
            Err(())
        } else {
            Ok(self.closed(*op))
        }
    }

    fn descends(&self, ancestor: &u8, op: &u8) -> Result<bool, ()> {
        if self.fail() {
            Err(())
        } else {
            Ok(self.descends_from(*ancestor, *op))
        }
    }

    fn ops_since(&self, _: &u8, _: &u8) -> Result<(Vec<OpEntry<u8>>, u8), ()> {
        unreachable!("push does not fetch operations")
    }

    fn objects_for(&self, _: &[u8], _: &u8, _: &u8) -> Result<u8, ()> {
        unreachable!("push does not fetch objects")
    }
}

fn attempt(storage: &mut Storage, expected: u8, objects: u8) {
    let before = storage.head();
    let result: Result<(CasOutcome, HandledBy<Storage>), ()> = Push {
        ops: &[1, 2],
        ops_attachment: &3,
        objects: &objects,
        expected: &expected,
        new: &2,
    }
    .answer(storage);

    kani::cover!(
        result.is_err() && before == (1, 1) && storage.objects & 2 != 0,
        "an error retains uploaded objects before acceptance"
    );
    assert!(storage.closed(storage.head));
    assert!(storage.descends_from(before.head, storage.head));
    // The only possible transition is 1 -> 2, once, even after an error or a replay.
    assert_eq!(storage.seq, u64::from(storage.head));
    assert!(storage.head == 1 || storage.head == 2);
    match result {
        Err(()) => assert_eq!(storage.head(), before),
        Ok((outcome, handled)) => {
            kani::cover!(outcome == CasOutcome::Incomplete, "an incomplete upload");
            kani::cover!(outcome == CasOutcome::Rejected, "a rejected push");
            kani::cover!(outcome == CasOutcome::Accepted, "a new acceptance");
            kani::cover!(outcome == CasOutcome::Idempotent, "an idempotent retry");
            let Reply::Head { kind, seq, head } = handled.reply else {
                panic!("a push is answered with a head");
            };
            assert_eq!(Head { seq, head }, storage.head());
            assert_eq!(kind == HeadKind::Accepted, storage.head == 2);
            if objects == 3 && storage.head != 2 {
                assert_eq!(kind, HeadKind::Rejected);
                assert_eq!(outcome, CasOutcome::Rejected);
            }
            if outcome == CasOutcome::Accepted {
                assert_eq!(before, Head { seq: 1, head: 1 });
                assert_eq!(expected, before.head);
                assert_eq!(handled.publish, Some(Head { seq, head }));
            } else {
                assert_eq!(storage.head(), before);
                assert!(handled.publish.is_none());
            }
        }
    }
}

/// Two possibly failing attempts, a complete fault-free retry, and its replay. Every
/// fallible call chooses independently; incomplete objects, stale expected heads and a
/// sibling rather than a descendant are also checked.
#[kani::proof]
#[kani::unwind(4)]
fn push_storage_retries() {
    let mut storage = Storage {
        child: kani::any(),
        ops: 1,
        objects: 1,
        head: 1,
        seq: 1,
        faults: true,
    };
    let expected = if kani::any() { 0 } else { 1 };
    let objects = kani::any::<u8>() & 3;
    for _ in 0..2 {
        attempt(&mut storage, expected, objects);
    }
    storage.faults = false;
    attempt(&mut storage, expected, 3);
    // With a matching expected head and a descendant, one complete retry suffices.
    assert_eq!(storage.head == 2, storage.child && expected == 1);
    let accepted = storage.head();
    attempt(&mut storage, expected, 3);
    assert_eq!(storage.head(), accepted);
}
