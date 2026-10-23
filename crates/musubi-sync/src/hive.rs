//! A hub and nodes in one process, delivering every message directly: the real protocol
//! core over real repositories and hub storage, without a transport. For tests.

use std::path::Path;

use musubi_core::hub;
use musubi_core::message::HeadKind;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_core::node::NodeCore;
use musubi_core::node::Step;
use musubi_jj::node::NodeRepo;
use musubi_jj::objects::Backend;

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

    /// The hive whose hub is in `hub_dir`, with no nodes yet: they are added again, each
    /// knowing nothing of the hub, as after a restart.
    pub fn open(hub_dir: &Path) -> anyhow::Result<Self> {
        Ok(Self {
            hub: HubAdapter::open(hub_dir)?,
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
        let adapter = NodeAdapter::new(repo)?;
        self.members.push(Member {
            core: NodeCore::new(adapter.root().clone()),
            adapter,
            uploaded: 0,
            downloaded: 0,
        });
        Ok(self.members.len() - 1)
    }

    /// Restarts a node's protocol state, as after a crash.
    pub fn restart(&mut self, node: usize) {
        let member = &mut self.members[node];
        member.core.restart();
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
        let member = &mut self.members[node];
        member
            .core
            .handle_reply(&mut member.adapter, handled.reply)?;
        if let Some((seq, head)) = handled.publish {
            for member in &mut self.members {
                let notify = Reply::Head {
                    kind: HeadKind::Notify,
                    seq,
                    head: head.clone(),
                };
                member.core.handle(&mut member.adapter, notify)?;
            }
        }
        Ok(())
    }

    /// Polls the hub, then runs the node's policy until it has nothing left to do. Returns
    /// how many steps it took.
    pub fn sync(&mut self, node: usize) -> anyhow::Result<usize> {
        let member = &mut self.members[node];
        member.adapter.before_sync()?;
        let poll = member.core.poll(&member.adapter)?;
        self.request(node, poll)?;
        for steps in 0..10_000 {
            let member = &mut self.members[node];
            match member.core.step(&mut member.adapter)? {
                Step::Idle => {
                    if member.adapter.when_idle()? {
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

    /// Has the node record its settings changes, as a sync starts by doing, without reaching
    /// the hub, as a machine that is offline does. Returns whether it recorded one.
    pub fn record_settings(&mut self, node: usize) -> anyhow::Result<bool> {
        self.members[node].adapter.reconcile_settings(false)
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
