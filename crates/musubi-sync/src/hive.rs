//! A hub and nodes in one process, delivering every message directly: the real protocol
//! core over real repositories and hub storage, without a transport. For tests.

use std::path::Path;

use musubi_core::hub;
use musubi_core::hub::Handled;
use musubi_core::message::Head;
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

/// What a node gets in place of each of the hub's replies to it.
pub type Through<'a> =
    dyn FnMut(&Request<OpId, Attachment>, Reply<OpId, Attachment>) -> Reply<OpId, Attachment> + 'a;

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

    /// Restarts the hub having lost every head it accepted after the `seq`th, as a power cut
    /// can make it.
    pub fn hub_goes_back(&mut self, seq: u64) -> anyhow::Result<()> {
        let path = self.hub_dir.join("heads");
        let text = std::fs::read_to_string(&path)?;
        let kept: String = text
            .split_inclusive('\n')
            .take(usize::try_from(seq)? + 1)
            .collect();
        std::fs::write(&path, kept)?;
        self.restart_hub()
    }

    /// Makes the hive again, empty, as a hub does whose store is corrupt.
    pub fn remake_hub(&mut self) -> anyhow::Result<()> {
        let backend = self.hub.store().backend();
        std::fs::remove_dir_all(&self.hub_dir)?;
        self.hub = HubAdapter::init(&self.hub_dir, backend)?;
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

    fn request(
        &mut self,
        node: usize,
        request: Request<OpId, Attachment>,
        through: &mut Through<'_>,
    ) -> anyhow::Result<()> {
        if let Request::Push {
            ops_attachment,
            objects,
            ..
        } = &request
        {
            self.members[node].uploaded +=
                attachment_size(ops_attachment)? + attachment_size(objects)?;
        }
        let handled = self.handle(request.clone())?;
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
            .handle_reply(&mut member.adapter, through(&request, handled.reply))?;
        if let Some(Head { seq, head }) = handled.publish {
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

    /// Has the hub handle `request`.
    pub fn handle(
        &mut self,
        request: Request<OpId, Attachment>,
    ) -> anyhow::Result<Handled<OpId, Attachment>> {
        hub::handle(&mut self.hub, request)
    }

    /// Polls the hub, then runs the node's policy until it has nothing left to do. Returns
    /// how many steps it took.
    pub fn sync(&mut self, node: usize) -> anyhow::Result<usize> {
        self.sync_through(node, &mut |_, reply| reply)
    }

    /// As [`Self::sync`], with each of the hub's replies to the node passed through
    /// `through`, with the request it answers, which may give the node another in its
    /// place. The hub's notifications reach every node as they are.
    pub fn sync_through(
        &mut self,
        node: usize,
        through: &mut Through<'_>,
    ) -> anyhow::Result<usize> {
        self.begin_sync(node, through)?;
        for steps in 0..10_000 {
            if !self.step_through(node, through)? && !self.members[node].adapter.when_idle()? {
                return Ok(steps);
            }
        }
        anyhow::bail!("node {node} did not settle")
    }

    /// Polls the hub and runs at most `steps` of the node's policy steps, as a sync cut short
    /// does, with each reply passed through `through`, as in [`Self::sync_through`]. Returns
    /// how many it took.
    pub fn sync_steps(
        &mut self,
        node: usize,
        steps: usize,
        through: &mut Through<'_>,
    ) -> anyhow::Result<usize> {
        self.begin_sync(node, through)?;
        for taken in 0..steps {
            if !self.step_through(node, through)? {
                return Ok(taken);
            }
        }
        Ok(steps)
    }

    /// Polls the hub, as a sync starts by doing, and takes in what it sends, staging the
    /// operations and objects it fetches, without realizing them.
    pub fn fetch(&mut self, node: usize) -> anyhow::Result<()> {
        self.begin_sync(node, &mut |_, reply| reply)
    }

    /// Polls first, then prepares the node, as the daemon does (`Driver::sync`).
    fn begin_sync(&mut self, node: usize, through: &mut Through<'_>) -> anyhow::Result<()> {
        let member = &mut self.members[node];
        let poll = member.adapter.poll(&member.core)?;
        self.request(node, poll, through)?;
        self.members[node].adapter.before_sync()
    }

    /// Takes one policy step and delivers its requests. Returns false if the core is idle;
    /// the caller decides whether to reconcile idle state or stop at this boundary.
    fn step_through(&mut self, node: usize, through: &mut Through<'_>) -> anyhow::Result<bool> {
        let member = &mut self.members[node];
        match member.core.step(&mut member.adapter)? {
            Step::Idle => return Ok(false),
            Step::Send(requests) => {
                for request in requests {
                    self.request(node, request, through)?;
                }
            }
            Step::Merged | Step::Realized(_) | Step::Advanced(_) => {}
        }
        Ok(true)
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
