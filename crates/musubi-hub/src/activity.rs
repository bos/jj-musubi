//! What a hub has seen of its hives since it started, for `musubi top`: the bytes that came
//! and went, the heads it accepted and what they brought, the pushes it turned away, the
//! requests that failed, and what each machine last said of its syncing. It lives in memory
//! only: a hub that starts again knows nothing of what came before, and needn't.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::time::Duration;
use std::time::Instant;

use jj_lib::op_store::OperationId;
use musubi_jj::workspaces;
use serde::Deserialize;
use serde::Serialize;

use crate::hub_dir::HiveInfo;
use crate::store::HubStore;
use crate::store::StoreError;

/// How many of each hive's latest heads to show.
pub const RECENT: usize = 16;

/// How many heads' times of acceptance to keep, to tell how long a machine has been behind.
const ACCEPTED_TIMES: usize = 256;

/// The longest text kept from a peer, or an operation: an error, a description.
const TEXT_LIMIT: usize = 300;

/// How long to remember a machine's report. A machine that leaves a hive, or whose copy is
/// deleted, says nothing more: after this long it is no longer taken for one offline.
pub const REPORTS_KEPT: Duration = Duration::from_secs(24 * 3600);

/// What a machine's daemon tells the hub after each sync with it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Report {
    /// The machine's key, `name#suffix`.
    pub machine: String,
    /// The hub's head as the sync left the machine knowing it.
    pub seq: u64,
    /// Why the sync failed, if it did.
    pub error: Option<String>,
    /// The machine's release of musubi.
    pub version: String,
}

/// A head the hub accepted, and what it brought.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Accepted {
    /// Seconds since the hub accepted it, when asked.
    pub age: u64,
    pub seq: u64,
    /// The operations it brought.
    pub ops: u64,
    /// The commits those operations wrote, new or rewritten.
    pub commits: u64,
    /// The host and description of its newest operation, as `jj op log` shows them.
    pub host: String,
    pub description: String,
}

/// Running totals for a hive since the hub started.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Traffic {
    /// Bytes of requests received, and of replies sent.
    pub received: u64,
    pub sent: u64,
    /// Operations, and the commits they wrote, in the heads accepted.
    pub ops_in: u64,
    pub commits_in: u64,
    /// Operations sent to machines catching up.
    pub ops_out: u64,
    /// Pushes that moved the head, that found another head first, and that lacked what
    /// they needed.
    pub accepted: u64,
    pub rejected: u64,
    pub incomplete: u64,
    /// Requests the hub failed to answer.
    pub failures: u64,
}

/// What a request for a hive did, as far as the activity cares.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Outcome {
    #[default]
    Other,
    Accepted,
    Rejected,
    Incomplete,
    /// Operations sent to a machine catching up.
    Sent(u64),
}

/// The latest trouble the hub had with a hive.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Failure {
    /// Seconds since it happened.
    pub age: u64,
    pub message: String,
    /// Whether a request failed, rather than the hub having trouble of its own.
    pub request: bool,
}

/// A machine in a hive, as the hub sees it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MachineActivity {
    pub key: String,
    /// Its name, as `musubi list` shows it.
    pub name: String,
    /// Whether the hive's head has a workspace of it.
    pub in_view: bool,
    /// Seconds since it last reported, and what it said.
    pub heard: Option<u64>,
    pub report: Option<Report>,
    /// Seconds since the hub accepted the first head the machine lacks, as far as it knows.
    pub behind: Option<u64>,
}

/// A hive's activity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HiveActivity {
    pub info: HiveInfo,
    /// The hive's head, once a request has opened its store.
    pub head: Option<u64>,
    pub traffic: Traffic,
    pub failure: Option<Failure>,
    /// Its latest heads, newest first.
    pub recent: Vec<Accepted>,
    pub machines: Vec<MachineActivity>,
}

/// The hub's activity, as `musubi top` asks for it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HubActivity {
    /// The hub's release of musubi.
    pub version: String,
    /// Seconds since the hub started.
    pub uptime: u64,
    pub hives: Vec<HiveActivity>,
}

pub struct Activity {
    started: Instant,
    hives: HashMap<String, HiveTrack>,
}

#[derive(Default)]
struct HiveTrack {
    head: Option<u64>,
    traffic: Traffic,
    failure: Option<(Instant, String, bool)>,
    /// Newest first, as many as [`RECENT`].
    recent: VecDeque<(Instant, Accepted)>,
    /// When each recent head was accepted, oldest first.
    accepted_at: VecDeque<(u64, Instant)>,
    reports: BTreeMap<String, (Instant, Report)>,
}

impl Default for Activity {
    fn default() -> Self {
        Self::new()
    }
}

impl Activity {
    pub fn new() -> Self {
        Self {
            started: Instant::now(),
            hives: HashMap::new(),
        }
    }

    fn hive(&mut self, id: &str) -> &mut HiveTrack {
        self.hives.entry(id.to_owned()).or_default()
    }

    /// Counts one request for hive `id` and its reply, and what it did, at `now`; `head` is
    /// the hive's head after it.
    pub fn served(
        &mut self,
        id: &str,
        received: usize,
        sent: usize,
        head: u64,
        outcome: Outcome,
        now: Instant,
    ) {
        let hive = self.hive(id);
        hive.head = Some(head);
        let traffic = &mut hive.traffic;
        traffic.received += received as u64;
        traffic.sent += sent as u64;
        match outcome {
            Outcome::Other => {}
            Outcome::Accepted => {
                traffic.accepted += 1;
                hive.accepted_at.push_back((head, now));
                if hive.accepted_at.len() > ACCEPTED_TIMES {
                    hive.accepted_at.pop_front();
                }
            }
            Outcome::Rejected => traffic.rejected += 1,
            Outcome::Incomplete => traffic.incomplete += 1,
            Outcome::Sent(ops) => traffic.ops_out += ops,
        }
    }

    /// Records what a head the hub accepted for hive `id` brought, at `now`.
    pub fn summarized(&mut self, id: &str, accepted: Accepted, now: Instant) {
        let hive = self.hive(id);
        hive.traffic.ops_in += accepted.ops;
        hive.traffic.commits_in += accepted.commits;
        hive.recent.push_front((now, accepted));
        hive.recent.truncate(RECENT);
    }

    /// Counts a request for hive `id` that failed, at `now`, and its reply.
    pub fn failed(&mut self, id: &str, received: usize, sent: usize, message: &str, now: Instant) {
        let hive = self.hive(id);
        hive.traffic.received += received as u64;
        hive.traffic.sent += sent as u64;
        hive.traffic.failures += 1;
        hive.failure = Some((now, clip(message), true));
    }

    /// Records trouble the hub had with hive `id` at `now`, though no request failed.
    pub fn troubled(&mut self, id: &str, message: &str, now: Instant) {
        self.hive(id).failure = Some((now, clip(message), false));
    }

    /// Records what a machine said of its sync with hive `id`, at `now`.
    pub fn report(&mut self, id: &str, mut report: Report, now: Instant) {
        report.machine = clip(&report.machine);
        report.version = clip(&report.version);
        report.error = report.error.as_deref().map(clip);
        let hive = self.hive(id);
        hive.reports.insert(report.machine.clone(), (now, report));
        hive.reports
            .retain(|_, (at, _)| now.saturating_duration_since(*at) < REPORTS_KEPT);
    }

    /// Forgets hive `id`, as when it is removed.
    pub fn forget(&mut self, id: &str) {
        self.hives.remove(id);
    }

    /// The activity of `hives`, each with the keys of the machines its head has workspaces
    /// of, as at `now`.
    pub fn snapshot(
        &self,
        hives: Vec<(HiveInfo, BTreeSet<String>)>,
        version: &str,
        now: Instant,
    ) -> HubActivity {
        let age = |then: Instant| now.saturating_duration_since(then).as_secs();
        let empty = HiveTrack::default();
        let hives = hives
            .into_iter()
            .map(|(info, in_view)| {
                let hive = self.hives.get(&info.id).unwrap_or(&empty);
                let reports: BTreeMap<&String, &(Instant, Report)> = hive
                    .reports
                    .iter()
                    .filter(|(_, (at, _))| now.saturating_duration_since(*at) < REPORTS_KEPT)
                    .collect();
                let keys: BTreeSet<String> = in_view
                    .iter()
                    .chain(reports.keys().copied())
                    .cloned()
                    .collect();
                let names = workspaces::display_names(&keys, |_| false);
                let machines = keys
                    .iter()
                    .map(|key| {
                        let reported = reports.get(key).copied();
                        let behind = match (reported, hive.head) {
                            (Some((_, report)), Some(head)) if report.seq < head => {
                                Some(age(self.lacked_since(hive, report.seq)))
                            }
                            _ => None,
                        };
                        MachineActivity {
                            key: key.clone(),
                            name: names.get(key).cloned().unwrap_or_else(|| key.clone()),
                            in_view: in_view.contains(key),
                            heard: reported.map(|(at, _)| age(*at)),
                            report: reported.map(|(_, report)| report.clone()),
                            behind,
                        }
                    })
                    .collect();
                HiveActivity {
                    info,
                    head: hive.head,
                    traffic: hive.traffic,
                    failure: hive.failure.as_ref().map(|(at, message, request)| Failure {
                        age: age(*at),
                        message: message.clone(),
                        request: *request,
                    }),
                    recent: hive
                        .recent
                        .iter()
                        .map(|(at, accepted)| Accepted {
                            age: age(*at),
                            ..accepted.clone()
                        })
                        .collect(),
                    machines,
                }
            })
            .collect();
        HubActivity {
            version: version.to_owned(),
            uptime: age(self.started),
            hives,
        }
    }

    /// When the hub accepted the first head after `seq`, or as near as it remembers: the
    /// oldest head it remembers, or when it started.
    fn lacked_since(&self, hive: &HiveTrack, seq: u64) -> Instant {
        hive.accepted_at
            .iter()
            .find(|(accepted, _)| *accepted > seq)
            .or(hive.accepted_at.front())
            .map_or(self.started, |(_, at)| *at)
    }
}

impl HubActivity {
    /// Leaves out some of what it says, for a reply that must be smaller: half of each
    /// hive's latest heads, then once none are left, machines' errors. Returns false if
    /// there was nothing left to leave out.
    pub fn shrink(&mut self) -> bool {
        if self.hives.iter().any(|hive| !hive.recent.is_empty()) {
            for hive in &mut self.hives {
                hive.recent.truncate(hive.recent.len() / 2);
            }
            return true;
        }
        let mut shrunk = false;
        for machine in self.hives.iter_mut().flat_map(|hive| &mut hive.machines) {
            if let Some(error) = machine.report.as_mut().and_then(|r| r.error.as_mut())
                && error != "…"
            {
                "…".clone_into(error);
                shrunk = true;
            }
        }
        shrunk
    }
}

/// What the heads accepted since `before` brought, up to the store's head.
pub fn summarize(store: &HubStore, before: &OperationId) -> Result<Accepted, StoreError> {
    let (seq, head) = store.head();
    let canonical = store.canonical();
    let ops = store.ops_since(head, before)?;
    let mut commits = 0;
    for id in &ops {
        let operation = canonical.read_operation(id)?;
        commits += operation
            .commit_predecessors
            .as_ref()
            .map_or(0, |predecessors| predecessors.len() as u64);
    }
    let newest = canonical.read_operation(head)?;
    Ok(Accepted {
        age: 0,
        seq,
        ops: ops.len() as u64,
        commits,
        host: clip(&newest.metadata.hostname),
        description: clip(&newest.metadata.description),
    })
}

/// `text`, cut short to [`TEXT_LIMIT`] bytes, at a character's end.
fn clip(text: &str) -> String {
    if text.len() <= TEXT_LIMIT {
        return text.to_owned();
    }
    let mut end = TEXT_LIMIT;
    while !text.is_char_boundary(end) {
        end -= 1;
    }
    format!("{}…", &text[..end])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn info(id: &str) -> HiveInfo {
        HiveInfo {
            id: id.to_owned(),
            name: id.to_owned(),
            backend: musubi_jj::objects::Backend::Git,
            urls: vec![],
            machines: vec![],
        }
    }

    fn accepted(seq: u64) -> Accepted {
        Accepted {
            age: 0,
            seq,
            ops: 2,
            commits: 1,
            host: "alpha".to_owned(),
            description: "commit".to_owned(),
        }
    }

    /// Accepts head `seq` at `at`, as the hub's server does.
    fn accept(activity: &mut Activity, seq: u64, at: Instant) {
        activity.served("h", 10, 10, seq, Outcome::Accepted, at);
        activity.summarized("h", accepted(seq), at);
    }

    fn report(machine: &str, seq: u64) -> Report {
        Report {
            machine: machine.to_owned(),
            seq,
            error: None,
            version: "0.1.0".to_owned(),
        }
    }

    /// A machine is behind from when the hub accepted the first head it lacks, however
    /// lately it reported; heads, traffic, and machines in the view or only reporting all
    /// show.
    #[test]
    fn machines_are_behind_from_the_first_head_they_lack() {
        let mut activity = Activity::new();
        let start = activity.started;
        let at = |secs| start + Duration::from_secs(secs);
        activity.served("h", 100, 10, 0, Outcome::Other, at(0));
        accept(&mut activity, 1, at(10));
        accept(&mut activity, 2, at(20));
        activity.served("h", 0, 50, 2, Outcome::Sent(3), at(20));
        activity.served("h", 5, 5, 2, Outcome::Rejected, at(20));
        activity.report("h", report("alpha#1", 2), at(21));
        activity.report("h", report("beta#2", 0), at(25));
        let keys = BTreeSet::from(["alpha#1".to_owned(), "gamma#3".to_owned()]);
        let snapshot = activity.snapshot(vec![(info("h"), keys)], "0.1.0", at(30));
        assert_eq!(snapshot.uptime, 30);
        let hive = &snapshot.hives[0];
        assert_eq!(hive.head, Some(2));
        assert_eq!(
            hive.traffic,
            Traffic {
                received: 125,
                sent: 85,
                ops_in: 4,
                commits_in: 2,
                ops_out: 3,
                accepted: 2,
                rejected: 1,
                ..Traffic::default()
            }
        );
        let seqs: Vec<(u64, u64)> = hive.recent.iter().map(|a| (a.seq, a.age)).collect();
        assert_eq!(seqs, [(2, 10), (1, 20)]);
        let machines: Vec<(&str, bool, Option<u64>, Option<u64>)> = hive
            .machines
            .iter()
            .map(|m| (m.name.as_str(), m.in_view, m.heard, m.behind))
            .collect();
        assert_eq!(
            machines,
            [
                ("alpha", true, Some(9), None),
                ("beta", false, Some(5), Some(20)),
                ("gamma", true, None, None),
            ]
        );
    }

    /// Past the heads it remembers, a machine is behind since the oldest it does; with none,
    /// since the hub started.
    #[test]
    fn forgotten_heads_count_from_the_oldest_remembered() {
        let mut activity = Activity::new();
        let start = activity.started;
        let at = |secs| start + Duration::from_secs(secs);
        activity.served("h", 0, 0, 7, Outcome::Other, at(0));
        activity.report("h", report("alpha#1", 3), at(1));
        let keys = BTreeSet::new();
        let behind = |activity: &Activity| {
            activity
                .snapshot(vec![(info("h"), keys.clone())], "", at(100))
                .hives[0]
                .machines[0]
                .behind
        };
        assert_eq!(behind(&activity), Some(100));
        for seq in 8..8 + ACCEPTED_TIMES as u64 + 1 {
            accept(&mut activity, seq, at(seq));
        }
        assert_eq!(behind(&activity), Some(100 - 9));
        assert_eq!(activity.hives["h"].recent.len(), RECENT);
    }

    /// A head whose summary failed still counts, so its machines aren't taken for behind.
    #[test]
    fn unsummarized_heads_count() {
        let mut activity = Activity::new();
        let start = activity.started;
        let at = |secs| start + Duration::from_secs(secs);
        accept(&mut activity, 1, at(1));
        activity.served("h", 0, 0, 2, Outcome::Accepted, at(50));
        activity.report("h", report("alpha#1", 1), at(51));
        let snapshot = activity.snapshot(vec![(info("h"), BTreeSet::new())], "", at(60));
        let hive = &snapshot.hives[0];
        assert_eq!((hive.traffic.accepted, hive.recent.len()), (2, 1));
        assert_eq!(hive.machines[0].behind, Some(10));
    }

    /// A machine silent for a day is forgotten: it may have left the hive.
    #[test]
    fn reports_are_forgotten_after_a_day() {
        let mut activity = Activity::new();
        let start = activity.started;
        activity.report("h", report("alpha#1", 0), start);
        let keys = BTreeSet::new();
        let later = |activity: &Activity, after: Duration| {
            activity
                .snapshot(vec![(info("h"), keys.clone())], "", start + after)
                .hives[0]
                .machines
                .len()
        };
        assert_eq!(later(&activity, REPORTS_KEPT / 2), 1);
        assert_eq!(later(&activity, REPORTS_KEPT), 0);
        activity.report("h", report("beta#2", 0), start + REPORTS_KEPT);
        assert_eq!(activity.hives["h"].reports.len(), 1);
    }

    /// Shrinking leaves out latest heads first, then errors, then says it can't.
    #[test]
    fn activity_shrinks_to_nothing_more() {
        let mut activity = Activity::new();
        let start = activity.started;
        for seq in 1..=4 {
            accept(&mut activity, seq, start);
        }
        let mut failing = report("alpha#1", 0);
        failing.error = Some("broken".to_owned());
        activity.report("h", failing, start);
        let mut snapshot = activity.snapshot(vec![(info("h"), BTreeSet::new())], "", start);
        let mut recent = vec![];
        while snapshot.shrink() {
            recent.push(snapshot.hives[0].recent.len());
        }
        assert_eq!(recent, [2, 1, 0, 0]);
        let error = snapshot.hives[0].machines[0]
            .report
            .as_ref()
            .unwrap()
            .error
            .clone();
        assert_eq!(error.as_deref(), Some("…"));
    }

    #[test]
    fn long_text_is_clipped_at_a_character() {
        let long = "é".repeat(TEXT_LIMIT);
        let clipped = clip(&long);
        assert!(clipped.len() <= TEXT_LIMIT + '…'.len_utf8());
        assert!(clipped.ends_with('…'));
        assert_eq!(clip("short"), "short");
    }
}
