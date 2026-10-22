//! Runs a node's policy against a remote hub.

use musubi_core::message::HeadKind;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_core::node::Handled;
use musubi_core::node::NodeCore;
use musubi_core::node::Step;
use musubi_jj::node::NodeRepo;

use crate::OpId;
use crate::node::NodeAdapter;
use crate::remote::RemoteHub;
use crate::short;
use crate::wire::HeadNotice;

pub struct NodeDriver {
    adapter: NodeAdapter,
    core: NodeCore<OpId>,
    remote: RemoteHub,
    /// What the current `sync` has done, for its log line.
    tally: Tally,
}

#[derive(Default)]
struct Tally {
    pushed: usize,
    realized: usize,
}

impl NodeDriver {
    pub fn new(repo: NodeRepo, remote: RemoteHub) -> anyhow::Result<Self> {
        let adapter = NodeAdapter::new(repo)?;
        Ok(Self {
            core: NodeCore::new(adapter.root().clone()),
            adapter,
            remote,
            tally: Tally::default(),
        })
    }

    pub fn known(&self) -> &(u64, OpId) {
        self.core.known()
    }

    /// Asks the hub for its head and anything new, then runs the policy until there is
    /// nothing left to do. Returns how many steps that took.
    pub async fn sync(&mut self) -> anyhow::Result<usize> {
        self.adapter.before_sync()?;
        self.tally = Tally::default();
        let poll = self.core.poll(&self.adapter)?;
        self.deliver(poll).await?;
        let mut steps = 0;
        loop {
            match self.core.step(&mut self.adapter)? {
                Step::Idle => {
                    if self.adapter.when_idle()? {
                        continue;
                    }
                    // Learning the head alone, as after a restart, changes nothing here.
                    let Tally { pushed, realized } = self.tally;
                    if pushed > 0 || realized > 0 {
                        let (seq, head) = self.core.known();
                        tracing::info!(
                            "synced: {pushed} operations pushed, {realized} realized; \
                             the hive is at {seq} ({})",
                            short(head)
                        );
                    }
                    return Ok(steps);
                }
                Step::Send(requests) => {
                    for request in requests {
                        self.deliver(request).await?;
                    }
                }
                Step::Merged => tracing::debug!("merged the op heads"),
                Step::Realized(op) => {
                    self.tally.realized += 1;
                    tracing::debug!("realized {}", short(&op));
                }
                Step::Advanced(op) => tracing::debug!("advanced to {}", short(&op)),
            }
            steps += 1;
        }
    }

    async fn deliver(&mut self, request: Request<OpId, crate::Attachment>) -> anyhow::Result<()> {
        let pushing = match &request {
            Request::Fetch { base, .. } => {
                tracing::debug!("fetching what follows {}", short(base));
                0
            }
            Request::GetObjects { for_ops, .. } => {
                tracing::debug!("asking for the objects of {} operations", for_ops.len());
                0
            }
            Request::Push {
                ops, expected, new, ..
            } => {
                tracing::debug!(
                    "pushing {} operations to move the head from {} to {}",
                    ops.len(),
                    short(expected),
                    short(new)
                );
                ops.len()
            }
        };
        let reply = self.remote.call(request).await?;
        let incomplete = matches!(
            reply,
            Reply::Head {
                kind: HeadKind::Incomplete,
                ..
            }
        );
        // Handling the reply imports its bundles, which go once it is dropped.
        let handled = self.core.handle(&mut self.adapter, reply)?;
        if let Handled::Learned {
            kind: HeadKind::Accepted,
            ..
        } = handled
        {
            self.tally.pushed += pushing;
        }
        log_handled(&handled);
        // Pushing again would send the same, and get the same answer.
        anyhow::ensure!(
            !incomplete,
            "the hub can't accept this machine's work: it still lacks objects that the work \
             requires, after this machine sent what it had (the hub's log names them)"
        );
        Ok(())
    }

    /// Takes a head announcement. A newer head makes the next `sync` fetch it.
    pub fn notice(&mut self, notice: HeadNotice) -> anyhow::Result<()> {
        let reply = Reply::Head {
            kind: HeadKind::Notify,
            seq: notice.seq,
            head: OpId::new(notice.head),
        };
        log_handled(&self.core.handle(&mut self.adapter, reply)?);
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
        self.core.restart(self.adapter.root().clone());
    }
}

fn log_handled(handled: &Handled<OpId>) {
    match handled {
        Handled::Learned { kind, seq, head } => {
            let kind = format!("{kind:?}").to_lowercase();
            tracing::debug!("learned the hive's head ({kind}): {seq} ({})", short(head));
        }
        Handled::Fetched { learned, staged } => match learned {
            Some((seq, head)) => tracing::debug!(
                "staged {} fetched operations; the hive is at {seq} ({})",
                staged.len(),
                short(head)
            ),
            None => tracing::debug!("staged {} fetched operations", staged.len()),
        },
        Handled::StagedObjects(ops) => {
            tracing::debug!("staged the objects of {} operations", ops.len());
        }
        Handled::Ignored => tracing::debug!("nothing new"),
    }
}
