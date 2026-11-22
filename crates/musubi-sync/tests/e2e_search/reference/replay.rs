//! jj's own merge of operations, and its application of one operation to another's result,
//! in the reference's repository.

use std::sync::Arc;

use futures::executor::block_on;
use jj_lib::op_store::View;
use jj_lib::operation::Operation;
use jj_lib::repo::ReadonlyRepo;

use super::Reference;

/// An operation the reference made, with its view.
pub(super) struct Replayed {
    pub(super) op: Operation,
    pub(super) view: View,
}

impl Replayed {
    pub(super) fn of(repo: &Arc<ReadonlyRepo>) -> Self {
        Self {
            op: repo.operation().clone(),
            view: repo.view().store_view().clone(),
        }
    }
}

impl Reference {
    /// jj's merge of `parents`, in their order.
    pub(super) fn merge(&self, parents: Vec<&Operation>) -> Replayed {
        let ops: Vec<Operation> = parents.into_iter().cloned().collect();
        let merged = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            block_on(self.loader.merge_operations(
                ops,
                None,
                Some("reconcile divergent operations"),
                [],
            ))
        }));
        let repo = match merged {
            Ok(Ok((repo, _))) => repo,
            Ok(Err(err)) => panic!("the reference's merge failed: {err}"),
            Err(_) => panic!("jj panicked merging the reference's operations"),
        };
        Replayed::of(&repo)
    }

    /// `op`, made at `base`, applied to `onto` as jj applies a concurrent operation: its
    /// view's changes from `base`, merged three-way, then descendants of what it rewrote
    /// rebased.
    pub(super) fn apply(&self, base: &Operation, op: &Operation, onto: &Operation) -> Replayed {
        block_on(async {
            let base = self.loader.load_at(base).await.unwrap();
            let other = self.loader.load_at(op).await.unwrap();
            let mut tx = self.loader.load_at(onto).await.unwrap().start_transaction();
            tx.repo_mut().merge(&base, &other).await.unwrap();
            tx.repo_mut().rebase_descendants().await.unwrap();
            let repo = tx
                .write(op.metadata().description.clone())
                .await
                .unwrap()
                .leave_unpublished();
            Replayed::of(&repo)
        })
    }
}
