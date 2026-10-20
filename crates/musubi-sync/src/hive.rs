//! A hub and nodes in one process, delivering every message directly: the real protocol
//! core over real repositories and hub storage, without a transport. For tests.

use std::path::Path;

use musubi_core::hub;
use musubi_core::message::HeadKind;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_core::node::LocalRepo as _;
use musubi_core::node::NodeCore;
use musubi_core::node::Step;
use musubi_hub::store::Backend;
use musubi_jj::node::NodeRepo;

use crate::Attachment;
use crate::OpId;
use crate::hub::HubAdapter;
use crate::node::NodeAdapter;

pub struct Member {
    pub adapter: NodeAdapter,
    pub core: NodeCore<OpId>,
    /// Bytes of attachments this node has sent and received: what a transport would carry.
    pub uploaded: u64,
    pub downloaded: u64,
}

pub struct Hive {
    pub hub: HubAdapter,
    pub members: Vec<Member>,
    hub_dir: std::path::PathBuf,
}

impl Hive {
    pub fn new(hub_dir: &Path, backend: Backend) -> anyhow::Result<Self> {
        Ok(Self {
            hub: HubAdapter::init(hub_dir, backend)?,
            members: vec![],
            hub_dir: hub_dir.to_owned(),
        })
    }

    /// Restarts the hub from its directory, as after a crash.
    pub fn restart_hub(&mut self) -> anyhow::Result<()> {
        self.hub = HubAdapter::open(&self.hub_dir)?;
        Ok(())
    }

    /// Adds a node; returns its index.
    pub fn add(&mut self, repo: NodeRepo) -> anyhow::Result<usize> {
        let root = repo.canonical_store().root_operation_id().clone();
        self.members.push(Member {
            adapter: NodeAdapter::new(repo)?,
            core: NodeCore::new(root),
            uploaded: 0,
            downloaded: 0,
        });
        Ok(self.members.len() - 1)
    }

    /// Restarts a node's protocol state, as after a crash.
    pub fn restart(&mut self, node: usize) {
        let member = &mut self.members[node];
        let root = member
            .adapter
            .repo()
            .canonical_store()
            .root_operation_id()
            .clone();
        member.core.restart(root);
    }

    fn request(&mut self, node: usize, request: Request<OpId, Attachment>) -> anyhow::Result<()> {
        if let Request::Push {
            ops_attachment,
            objects,
            ..
        } = &request
        {
            self.members[node].uploaded +=
                attachment_size(ops_attachment)? + attachment_size(objects)?;
        }
        let handled = hub::handle(&mut self.hub, request)?;
        match &handled.reply {
            Reply::Fetched {
                ops_attachment,
                objects,
                ..
            } => {
                self.members[node].downloaded +=
                    attachment_size(ops_attachment)? + attachment_size(objects)?;
            }
            Reply::Objects { attachment, .. } => {
                self.members[node].downloaded += attachment_size(attachment)?;
            }
            Reply::Head { .. } => {}
        }
        self.reply(node, handled.reply)?;
        if let Some((seq, head)) = handled.publish {
            for target in 0..self.members.len() {
                let notify = Reply::Head {
                    kind: HeadKind::Notify,
                    seq,
                    head: head.clone(),
                };
                self.reply(target, notify)?;
            }
        }
        Ok(())
    }

    fn reply(&mut self, node: usize, reply: Reply<OpId, Attachment>) -> anyhow::Result<()> {
        let member = &mut self.members[node];
        member.core.handle(&mut member.adapter, reply)?;
        Ok(())
    }

    /// Polls the hub, then runs the node's policy until it has nothing left to do. Returns
    /// how many steps it took.
    pub fn sync(&mut self, node: usize) -> anyhow::Result<usize> {
        self.members[node].adapter.reconcile_settings(true)?;
        let member = &mut self.members[node];
        member.adapter.heads()?;
        let poll = member.core.poll(&member.adapter)?;
        self.request(node, poll)?;
        for steps in 0..10_000 {
            let member = &mut self.members[node];
            match member.core.step(&mut member.adapter)? {
                Step::Idle => {
                    // Both run; either may write an operation to upload.
                    let settings = member.adapter.reconcile_settings(false)?;
                    let workspaces = member.adapter.show_other_workspaces()?;
                    if settings || workspaces {
                        continue;
                    }
                    return Ok(steps);
                }
                Step::Send(requests) => {
                    for request in requests {
                        self.request(node, request)?;
                    }
                }
                Step::Merged | Step::Realized(_) | Step::Advanced(_) => {}
            }
        }
        anyhow::bail!("node {node} did not settle")
    }

    /// Syncs every node, repeatedly, until a whole round changes nothing.
    pub fn sync_all(&mut self) -> anyhow::Result<()> {
        for _ in 0..20 {
            let mut steps = 0;
            for node in 0..self.members.len() {
                steps += self.sync(node)?;
            }
            if steps == 0 {
                return Ok(());
            }
        }
        anyhow::bail!("the hive did not converge")
    }

    pub fn hub_head(&self) -> OpId {
        self.hub.store().head().1.clone()
    }
}

fn attachment_size(attachment: &Attachment) -> anyhow::Result<u64> {
    Ok(match attachment {
        Attachment::Bundle(_) | Attachment::File(_) => {
            std::fs::metadata(attachment.bundle_path()?)?.len()
        }
        Attachment::None | Attachment::Haves(_) => 0,
    })
}
