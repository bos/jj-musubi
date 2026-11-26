//! Runs a node's policy against a remote hub.

use musubi_core::message::Head;
use musubi_core::message::HeadKind;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_core::node::Handled;
use musubi_core::node::NodeCore;
use musubi_core::node::Step;
use musubi_jj::node::NodeRepo;

use crate::OpId;
use crate::node::Gate;
use crate::node::NodeAdapter;
use crate::progress::Activity;
use crate::remote::RemoteHub;
use crate::short;
use crate::wire::HeadNotice;

pub struct NodeDriver {
    adapter: NodeAdapter,
    /// Kept to give each adapter that reopening makes.
    gate: Option<Gate>,
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
            gate: None,
            remote,
            tally: Tally::default(),
        })
    }

    /// Calls `gate` before each step that would write any of the hive's history to the
    /// repository: realizing its operations, or advancing the op heads to one. A step it
    /// fails, fails, having written nothing, and so does the sync.
    ///
    /// Until the first such step, a sync writes none of the hive's history where jj shows it:
    /// what a fetch stages is objects jj doesn't reach, and what it writes before syncing, as
    /// a merge of the op heads, is operations of this machine's own. So a caller that ends a
    /// sync while `gate` fails, as at any await, or as a crash would, has applied none of the
    /// hive's history to the repository.
    pub fn before_applying(
        &mut self,
        gate: impl Fn() -> anyhow::Result<()> + Send + Sync + 'static,
    ) {
        let gate: Gate = std::sync::Arc::new(gate);
        self.adapter.set_gate(Some(gate.clone()));
        self.gate = Some(gate);
    }

    pub fn known(&self) -> &Head<OpId> {
        self.core.known()
    }

    /// The settings this handle opened its repository with, so a long-running caller can
    /// reopen it when the configuration changes, including its signer and Git executable.
    pub fn settings(&self) -> &jj_lib::settings::UserSettings {
        self.adapter.repo().loader().settings()
    }

    /// Asks the hub for its head and anything new, then runs the policy until there is
    /// nothing left to do. Returns how many steps that took.
    pub async fn sync(&mut self) -> anyhow::Result<usize> {
        self.tally = Tally::default();
        // Polled first: what the hub sends says whether it took this node's last push, which
        // reading the op heads must know, to notice an abandon of it.
        let poll = self.adapter.poll(&self.core)?;
        self.deliver(poll).await?;
        self.adapter.before_sync()?;
        let mut steps = 0;
        loop {
            // Cleanup cannot race the approval check or an attachment upload. jj commands
            // remain independent; every outgoing request names immutable operations.
            let _publication = musubi_jj::node::publication_lock(self.adapter.repo().repo_path())?;
            match self.core.step(&mut self.adapter)? {
                Step::Idle => {
                    if self.adapter.when_idle()? {
                        continue;
                    }
                    // Learning the head alone, as after a restart, changes nothing here.
                    let Tally { pushed, realized } = self.tally;
                    if pushed > 0 || realized > 0 {
                        let Head { seq, head } = self.core.known();
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
                Step::Merged => {
                    #[cfg(feature = "antithesis")]
                    antithesis_sdk::assert_reachable!("a machine merges its work with the hive's");
                    tracing::debug!("merged the op heads");
                }
                Step::Realized(op) => {
                    self.tally.realized += 1;
                    self.remote.progress().set(Activity::Applying {
                        done: self.tally.realized as u64,
                    });
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
        self.remote.progress().set(Activity::Asking);
        let reply = self.remote.call(request).await?;
        let went_back = self.core.hub_went_back(&reply);
        if went_back {
            let Head { seq, head } = self.core.known();
            tracing::warn!(
                "the hub has gone back from {seq} ({}), having lost heads it accepted: \
                 starting over from where it is",
                short(head)
            );
        }
        #[cfg(feature = "antithesis")]
        if pushing > 0
            && !went_back
            && let Reply::Head {
                kind: HeadKind::Rejected,
                seq,
                ..
            } = &reply
        {
            antithesis_sdk::assert_reachable!(
                "the hub rejects a push because another came first",
                &antithesis_sdk::serde_json::json!({ "seq": seq, "ops": pushing })
            );
        }
        let incomplete = matches!(
            reply,
            Reply::Head {
                kind: HeadKind::Incomplete,
                ..
            }
        );
        // Handling the reply imports its bundles, which go once it is dropped.
        let handled = self.core.handle_reply(&mut self.adapter, reply)?;
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
            "the hub refused this machine's work: it lacks something the work needs, or repeats \
             an operation the hive has (the hub's log says which)"
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
    pub fn reopen(&mut self, mut repo: NodeRepo) -> anyhow::Result<()> {
        repo.keep_found(self.adapter.repo());
        self.adapter = NodeAdapter::new(repo)?;
        self.adapter.set_gate(self.gate.clone());
        self.restart();
        Ok(())
    }

    /// Forgets volatile protocol state, as after a crash.
    pub fn restart(&mut self) {
        self.core.restart();
    }
}

fn log_handled(handled: &Handled<OpId>) {
    match handled {
        Handled::Learned { kind, seq, head } => {
            tracing::debug!("learned the hive's head ({kind}): {seq} ({})", short(head));
        }
        Handled::Fetched { learned, staged } => match learned {
            Some(Head { seq, head }) => tracing::debug!(
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
