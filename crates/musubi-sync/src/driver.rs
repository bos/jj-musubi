//! Runs a node's policy against a remote hub.

use musubi_core::message::HeadKind;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_core::node::LocalRepo as _;
use musubi_core::node::NodeCore;
use musubi_core::node::Step;
use musubi_jj::node::NodeRepo;

use crate::OpId;
use crate::node::NodeAdapter;
use crate::remote::RemoteHub;
use crate::wire::HeadNotice;

pub struct NodeDriver {
    adapter: NodeAdapter,
    core: NodeCore<OpId>,
    remote: RemoteHub,
}

impl NodeDriver {
    pub fn new(repo: NodeRepo, remote: RemoteHub) -> anyhow::Result<Self> {
        let root = repo.canonical_store().root_operation_id().clone();
        Ok(Self {
            adapter: NodeAdapter::new(repo)?,
            core: NodeCore::new(root),
            remote,
        })
    }

    pub fn adapter(&self) -> &NodeAdapter {
        &self.adapter
    }

    pub fn known(&self) -> &(u64, OpId) {
        self.core.known()
    }

    /// Asks the hub for its head and anything new, then runs the policy until there is
    /// nothing left to do. Returns how many steps that took.
    pub async fn sync(&mut self) -> anyhow::Result<usize> {
        // Settings changed here go up with this sync, and once the node has the hive's head,
        // the hive's settings apply here.
        self.adapter.reconcile_settings(true)?;
        // Op heads may have changed since the last step: a fetch's haves should say so.
        self.adapter.heads()?;
        let poll = self.core.poll(&self.adapter)?;
        self.deliver(poll).await?;
        let mut steps = 0;
        loop {
            match self.core.step(&mut self.adapter)? {
                Step::Idle => {
                    // Both run; either may write an operation to upload.
                    let settings = self.adapter.reconcile_settings(false)?;
                    let workspaces = self.adapter.show_other_workspaces()?;
                    if settings || workspaces {
                        continue;
                    }
                    return Ok(steps);
                }
                Step::Send(requests) => {
                    for request in requests {
                        self.deliver(request).await?;
                    }
                }
                Step::Merged | Step::Realized(_) | Step::Advanced(_) => {}
            }
            steps += 1;
        }
    }

    async fn deliver(&mut self, request: Request<OpId, crate::Attachment>) -> anyhow::Result<()> {
        let reply = self.remote.call(request).await?;
        let attachments = match &reply {
            Reply::Fetched {
                ops_attachment,
                objects,
                ..
            } => vec![ops_attachment.clone(), objects.clone()],
            Reply::Objects { attachment, .. } => vec![attachment.clone()],
            Reply::Head { .. } => vec![],
        };
        let result = self.core.handle(&mut self.adapter, reply);
        for attachment in &attachments {
            self.remote.release(attachment);
        }
        result?;
        Ok(())
    }

    /// Takes a head announcement. A newer head makes the next `sync` fetch it.
    pub fn notice(&mut self, notice: HeadNotice) -> anyhow::Result<()> {
        let reply = Reply::Head {
            kind: HeadKind::Notify,
            seq: notice.seq,
            head: OpId::new(notice.head),
        };
        self.core.handle(&mut self.adapter, reply)?;
        Ok(())
    }

    /// Starts over with `repo`, a fresh handle on the same repository, as after a crash.
    /// jj-lib and gix cache what they read from the repository, so a handle can keep
    /// failing after the repository changed under it (colocation turned on or off), or
    /// after git's object store outgrew what gix sized for it.
    pub fn reopen(&mut self, repo: NodeRepo) -> anyhow::Result<()> {
        self.adapter = NodeAdapter::new(repo)?;
        self.restart();
        Ok(())
    }

    /// Forgets volatile protocol state, as after a crash.
    pub fn restart(&mut self) {
        let root = self
            .adapter
            .repo()
            .canonical_store()
            .root_operation_id()
            .clone();
        self.core.restart(root);
    }
}
