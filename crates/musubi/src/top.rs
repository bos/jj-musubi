//! `musubi top`: what flows through this machine's hubs, and what is wrong, refreshed as it
//! goes.
//!
//! Each refresh asks every hub for its activity (`musubi_hub::activity`): the bytes its
//! hives' requests and replies carried, the heads it accepted, its failures, and what each
//! machine's daemon last reported. Rates come from the difference between two refreshes. A
//! thread of its own asks, so that a hub slow to answer never holds up the keyboard.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::io::IsTerminal as _;
use std::io::Write as _;
use std::sync::mpsc;
use std::time::Duration;
use std::time::Instant;

use musubi_hub::activity::HiveActivity;
use musubi_hub::activity::HubActivity;
use musubi_hub::activity::MachineActivity;
use musubi_hub::activity::REPORTS_KEPT;
use musubi_sync::wire::HubWideReply;
use musubi_sync::wire::HubWideRequest;
use ratatui::Frame;
use ratatui::crossterm::event;
use ratatui::crossterm::event::Event;
use ratatui::crossterm::event::KeyCode;
use ratatui::crossterm::event::KeyEventKind;
use ratatui::crossterm::event::KeyModifiers;
use ratatui::layout::Constraint;
use ratatui::layout::Layout;
use ratatui::style::Style;
use ratatui::style::Stylize as _;
use ratatui::text::Line;
use ratatui::widgets::Paragraph;
use ratatui::widgets::Row;
use ratatui::widgets::Table;
use ratatui::widgets::TableState;

use crate::config::UserState;
use crate::control;
use crate::daemon;
use crate::hub;
use crate::socket::Socket;
use crate::ui::Ui;

/// A daemon reports after every sync, and syncs at least this often (see
/// `daemon::POLL_INTERVAL`), so one silent for four times as long is offline, or stopped.
const SILENT: u64 = 120;
/// A machine syncs as soon as it hears of a new head; one still without it after this long
/// is stuck.
const BEHIND: u64 = 60;
/// How long a failure of the hub's stays among the issues.
const RECENT_FAILURE: u64 = 600;
/// The shortest and longest refresh `+` and `-` choose.
const FASTEST: Duration = Duration::from_secs(1);
const SLOWEST: Duration = Duration::from_secs(60);
/// The latest heads to show of each hive, without a terminal.
const RECENT_PRINTED: usize = 5;
/// The most lines of issues to show on the terminal.
const MOST_ISSUES: usize = 8;

pub struct Args {
    pub hub: Option<String>,
    pub interval: Duration,
    pub once: bool,
}

pub fn run(ui: &Ui, args: Args, socket: anyhow::Result<Socket>) -> anyhow::Result<()> {
    let hubs = match args.hub {
        Some(hub) => vec![hub::absolute(&hub)],
        None => known_hubs()?,
    };
    if hubs.is_empty() {
        crate::no_hubs(ui)?;
        return Ok(());
    }
    let socket = socket.map_err(|err| format!("{err:#}"));
    let mut sampler = Sampler::new(hubs, socket)?;
    if args.once || !std::io::stdout().is_terminal() {
        let sample = sampler.sample();
        let plain = View::new(&sample, None, None).plain();
        ui.stdout().write_all(plain.as_bytes())?;
        return Ok(());
    }
    interactive(sampler, args.interval)
}

/// The default hub, and the hubs of this machine's copies.
fn known_hubs() -> anyhow::Result<Vec<String>> {
    let state = UserState::load()?;
    Ok(UserState::known_hubs(
        state.default_hub()?,
        &state.memberships(),
    ))
}

/// What every hub, and this machine's daemon, said at one refresh.
struct Sample {
    hubs: Vec<HubSample>,
    /// The number of repositories the daemon serves, if it is running.
    daemon: Result<Option<usize>, String>,
}

/// What a hub said, and when it said it.
struct HubSample {
    hub: String,
    at: Instant,
    activity: Result<HubActivity, String>,
}

/// How long to wait before connecting again to a hub it couldn't connect to, rather than
/// wait for it at every refresh.
const RECONNECT: Duration = Duration::from_secs(30);

/// Where it is with a hub.
enum Link {
    Connected(hub::Connection),
    /// It couldn't connect, at this time, for this reason.
    Failed(Instant, String),
}

/// Asks the hubs, keeping a connection to each that it reached.
struct Sampler {
    hubs: Vec<String>,
    socket: Result<Socket, String>,
    links: HashMap<String, Link>,
    runtime: tokio::runtime::Runtime,
}

impl Sampler {
    fn new(hubs: Vec<String>, socket: Result<Socket, String>) -> anyhow::Result<Self> {
        Ok(Self {
            hubs,
            socket,
            links: HashMap::new(),
            runtime: tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()?,
        })
    }

    /// Asks every hub at once, so that one slow to answer holds up only itself.
    fn sample(&mut self) -> Sample {
        let asks = self.hubs.iter().map(|hub| {
            let link = self.links.remove(hub);
            async move {
                let (link, activity) = ask(hub, link).await;
                let at = Instant::now();
                (
                    link,
                    HubSample {
                        hub: hub.clone(),
                        at,
                        activity,
                    },
                )
            }
        });
        let asked = self.runtime.block_on(futures::future::join_all(asks));
        let mut hubs = vec![];
        for (link, sample) in asked {
            self.links.insert(sample.hub.clone(), link);
            hubs.push(sample);
        }
        let daemon = match &self.socket {
            Ok(socket) => self.runtime.block_on(serving(socket)),
            Err(err) => Err(err.clone()),
        };
        Sample { hubs, daemon }
    }
}

/// The activity of `hub`, connecting to it first if need be and it's time to try again.
async fn ask(hub: &str, link: Option<Link>) -> (Link, Result<HubActivity, String>) {
    let connection = match link {
        Some(Link::Connected(connection)) => connection,
        Some(Link::Failed(at, why)) if at.elapsed() < RECONNECT => {
            return (Link::Failed(at, why.clone()), Err(why));
        }
        _ => {
            // Over ssh, through a ProxyCommand, connecting takes a while.
            let limit = Duration::from_secs(if hub::is_local(hub) { 3 } else { 15 });
            match hub::connect(hub, limit).await {
                Ok(connection) => connection,
                Err(err) => {
                    let why = format!("{err:#}");
                    return (Link::Failed(Instant::now(), why.clone()), Err(why));
                }
            }
        }
    };
    let activity = activity(&connection, hub)
        .await
        .map_err(|err| format!("{err:#}"));
    (Link::Connected(connection), activity)
}

async fn activity(connection: &hub::Connection, hub: &str) -> anyhow::Result<HubActivity> {
    // Once connected, the transport connects again by itself; until it has, say why not.
    if !connection.transport.connected()
        && let Some(why) = connection.out_of_reach().await
    {
        anyhow::bail!("{why}");
    }
    let limit = Duration::from_secs(10);
    match hub::ask_within(connection, hub, HubWideRequest::Activity, limit).await? {
        HubWideReply::Activity(activity) => Ok(activity),
        other => anyhow::bail!("unexpected reply from the hub: {other:?}"),
    }
}

/// How many repositories this machine's daemon serves, or `None` if it isn't running.
async fn serving(socket: &Socket) -> Result<Option<usize>, String> {
    let client = match daemon::running(socket).await {
        Ok(Some(client)) => client,
        Ok(None) => return Ok(None),
        Err(err) => return Err(format!("{err:#}")),
    };
    match client
        .status(control::context(Duration::from_secs(5)))
        .await
    {
        Ok(repos) => Ok(Some(repos.len())),
        Err(err) => Err(format!("{err}")),
    }
}

/// What the sampling thread is told.
enum Wake {
    /// Refresh now.
    Now,
    /// Refresh every so often from now on, starting now.
    Every(Duration),
}

fn interactive(sampler: Sampler, interval: Duration) -> anyhow::Result<()> {
    let (samples_tx, samples) = mpsc::channel();
    let (wake, woken) = mpsc::channel();
    std::thread::Builder::new()
        .name("top sampler".to_owned())
        .spawn(move || sample_until_told(sampler, interval, &samples_tx, &woken))?;
    let mut app = App {
        interval,
        latest: None,
        previous: None,
        selected: TableState::default().with_selected(0),
    };
    let mut terminal = ratatui::try_init()?;
    let result = (|| -> anyhow::Result<()> {
        loop {
            while let Ok(sample) = samples.try_recv() {
                app.previous = app.latest.replace(sample);
            }
            terminal.draw(|frame| app.draw(frame))?;
            if !event::poll(Duration::from_millis(250))? {
                continue;
            }
            let Event::Key(key) = event::read()? else {
                continue;
            };
            if key.kind != KeyEventKind::Press {
                continue;
            }
            match key.code {
                KeyCode::Char('q') | KeyCode::Esc => return Ok(()),
                KeyCode::Char('c') if key.modifiers.contains(KeyModifiers::CONTROL) => {
                    return Ok(());
                }
                KeyCode::Up | KeyCode::Char('k') => app.selected.select_previous(),
                KeyCode::Down | KeyCode::Char('j') => app.selected.select_next(),
                KeyCode::Char('r') => {
                    wake.send(Wake::Now).ok();
                }
                KeyCode::Char('+') => {
                    app.interval = (app.interval + FASTEST).min(SLOWEST);
                    wake.send(Wake::Every(app.interval)).ok();
                }
                KeyCode::Char('-') => {
                    app.interval = app.interval.saturating_sub(FASTEST).max(FASTEST);
                    wake.send(Wake::Every(app.interval)).ok();
                }
                _ => {}
            }
        }
    })();
    ratatui::restore();
    result
}

/// Samples every `interval`, or when woken, until nobody listens.
fn sample_until_told(
    mut sampler: Sampler,
    mut interval: Duration,
    samples: &mpsc::Sender<Sample>,
    woken: &mpsc::Receiver<Wake>,
) {
    loop {
        if samples.send(sampler.sample()).is_err() {
            return;
        }
        match woken.recv_timeout(interval) {
            Ok(Wake::Now) | Err(mpsc::RecvTimeoutError::Timeout) => {}
            Ok(Wake::Every(every)) => interval = every,
            Err(mpsc::RecvTimeoutError::Disconnected) => return,
        }
    }
}

struct App {
    interval: Duration,
    latest: Option<Sample>,
    previous: Option<Sample>,
    selected: TableState,
}

impl App {
    fn draw(&mut self, frame: &mut Frame<'_>) {
        let Some(latest) = &self.latest else {
            frame.render_widget(Paragraph::new("Asking the hubs…"), frame.area());
            return;
        };
        let view = View::new(latest, self.previous.as_ref(), Some(self.interval));
        if let Some(selected) = self.selected.selected()
            && selected >= view.hives.len()
        {
            self.selected
                .select(Some(view.hives.len().saturating_sub(1)));
        }
        view.draw(frame, &mut self.selected);
    }
}

/// One refresh, made into text: the same for the terminal and for printing.
struct View {
    status: Vec<String>,
    issues: Vec<String>,
    /// Whether to show which hub each hive is on.
    several_hubs: bool,
    hives: Vec<HiveView>,
}

struct HiveView {
    hub: String,
    /// The hive's row: name, head, bytes in and out a second, operations and commits in,
    /// machines up to date, issues.
    row: Vec<String>,
    issues: usize,
    /// Its totals since the hub started.
    totals: String,
    /// Each machine's name, when last heard, head, release, and state, and whether that is
    /// an issue.
    machines: Vec<(Vec<String>, bool)>,
    /// Its latest heads: how long ago, head, host, operations, commits, description.
    recent: Vec<Vec<String>>,
}

const HIVE_HEADER: [&str; 8] = [
    "HIVE", "HEAD", "IN/s", "OUT/s", "OPS", "COMMITS", "MACHINES", "ISSUES",
];
const MACHINE_HEADER: [&str; 5] = ["MACHINE", "HEARD", "AT", "MUSUBI", "STATE"];
const RECENT_HEADER: [&str; 6] = ["AGO", "HEAD", "FROM", "OPS", "COMMITS", "WHAT"];

impl View {
    /// The view of `sample`, with rates from `previous`, refreshed every `interval`, if it
    /// is.
    fn new(sample: &Sample, previous: Option<&Sample>, interval: Option<Duration>) -> Self {
        let mut status = vec![];
        let mut issues = vec![];
        let hub_count = sample.hubs.len();
        let mut title = format!(
            "musubi top: {} {}",
            hub_count,
            if hub_count == 1 { "hub" } else { "hubs" }
        );
        if let Some(interval) = interval {
            write!(title, ", every {}", duration(interval.as_secs())).ok();
        }
        status.push(title);
        match &sample.daemon {
            Ok(Some(repos)) => status.push(format!(
                "This machine's daemon is running, serving {repos} {}.",
                if *repos == 1 {
                    "repository"
                } else {
                    "repositories"
                }
            )),
            Ok(None) => issues.push(
                "This machine's daemon isn't running; `musubi daemon start` starts it.".to_owned(),
            ),
            Err(err) => issues.push(format!("This machine's daemon: {}", one_line(err))),
        }
        let mut hives = vec![];
        for HubSample { hub, at, activity } in &sample.hubs {
            let activity = match activity {
                Ok(activity) => activity,
                Err(err) => {
                    issues.push(format!("Hub {hub}: {}", one_line(err)));
                    continue;
                }
            };
            status.push(format!(
                "Hub {hub}: up {}, musubi {}, {} {}.",
                duration(activity.uptime),
                activity.version,
                activity.hives.len(),
                if activity.hives.len() == 1 {
                    "hive"
                } else {
                    "hives"
                }
            ));
            let before = previous.and_then(|previous| {
                let earlier = previous.hubs.iter().find(|h| &h.hub == hub)?;
                let activity_then = earlier.activity.as_ref().ok()?;
                // A hub that started again counts from nothing.
                (activity_then.uptime <= activity.uptime).then_some((earlier.at, activity_then))
            });
            for hive in &activity.hives {
                let earlier = before.and_then(|(then, earlier)| {
                    let hive = earlier.hives.iter().find(|h| h.info.id == hive.info.id)?;
                    Some((at.saturating_duration_since(then), hive))
                });
                let (view, hive_issues) = HiveView::new(hub, hive, activity, earlier);
                issues.extend(hive_issues);
                hives.push(view);
            }
        }
        Self {
            status,
            issues,
            several_hubs: hub_count > 1,
            hives,
        }
    }

    fn hive_header(&self) -> Vec<&'static str> {
        let mut header = HIVE_HEADER.to_vec();
        if self.several_hubs {
            header.insert(1, "HUB");
        }
        header
    }

    fn hive_row(&self, hive: &HiveView) -> Vec<String> {
        let mut row = hive.row.clone();
        if self.several_hubs {
            row.insert(1, hive.hub.clone());
        }
        row
    }

    /// The view as text, for printing without a terminal.
    fn plain(&self) -> String {
        let mut out = String::new();
        for line in &self.status {
            writeln!(out, "{line}").ok();
        }
        if self.issues.is_empty() {
            writeln!(out, "No issues.").ok();
        } else {
            writeln!(out, "Issues:").ok();
            for issue in &self.issues {
                writeln!(out, "  {issue}").ok();
            }
        }
        if self.hives.is_empty() {
            return out;
        }
        let rows: Vec<Vec<String>> = self.hives.iter().map(|h| self.hive_row(h)).collect();
        writeln!(out).ok();
        out.push_str(&columns(&self.hive_header(), &rows, ""));
        for hive in &self.hives {
            writeln!(out, "\n{} {}", hive.row[0], hive.totals).ok();
            let machines: Vec<Vec<String>> = hive.machines.iter().map(|(m, _)| m.clone()).collect();
            if !machines.is_empty() {
                out.push_str(&columns(&MACHINE_HEADER, &machines, "  "));
            }
            if !hive.recent.is_empty() {
                writeln!(out).ok();
                let recent = &hive.recent[..hive.recent.len().min(RECENT_PRINTED)];
                out.push_str(&columns(&RECENT_HEADER, recent, "  "));
            }
        }
        out
    }

    fn draw(&self, frame: &mut Frame<'_>, selected: &mut TableState) {
        // Past this many, a line says how many more.
        let shown_issues = if self.issues.len() > MOST_ISSUES {
            MOST_ISSUES - 1
        } else {
            self.issues.len()
        };
        let issue_lines = if self.issues.is_empty() {
            0
        } else {
            self.issues.len().min(MOST_ISSUES) + 1
        };
        let hive_lines = self.hives.len().max(1) + 1;
        let [status, issues, hives, gap, detail, keys] = Layout::vertical([
            Constraint::Length(self.status.len() as u16),
            Constraint::Length(issue_lines as u16),
            Constraint::Length(hive_lines.min(12) as u16),
            Constraint::Length(1),
            Constraint::Fill(1),
            Constraint::Length(1),
        ])
        .areas(frame.area());
        let _ = gap;
        frame.render_widget(
            Paragraph::new(
                self.status
                    .iter()
                    .map(|s| Line::from(s.as_str()))
                    .collect::<Vec<_>>(),
            ),
            status,
        );
        if !self.issues.is_empty() {
            let mut lines = vec![Line::from("Issues:").bold().red()];
            lines.extend(
                self.issues
                    .iter()
                    .take(shown_issues)
                    .map(|issue| Line::from(format!("  {issue}")).red()),
            );
            let more = self.issues.len() - shown_issues;
            if more > 0 {
                lines.push(Line::from(format!("  and {more} more")).red());
            }
            frame.render_widget(Paragraph::new(lines), issues);
        }
        let header = self.hive_header();
        let rows = self.hives.iter().map(|hive| {
            let row = Row::new(self.hive_row(hive));
            if hive.issues > 0 { row.red() } else { row }
        });
        let mut widths: Vec<Constraint> = vec![
            Constraint::Fill(1),
            Constraint::Length(6),
            Constraint::Length(10),
            Constraint::Length(10),
            Constraint::Length(7),
            Constraint::Length(8),
            Constraint::Length(9),
            Constraint::Length(6),
        ];
        if self.several_hubs {
            widths.insert(1, Constraint::Fill(1));
        }
        let table = Table::new(rows, widths)
            .header(Row::new(header).bold())
            .row_highlight_style(Style::new().reversed());
        frame.render_stateful_widget(table, hives, selected);
        if let Some(hive) = selected.selected().and_then(|i| self.hives.get(i)) {
            hive.draw(frame, detail);
        }
        frame.render_widget(
            Paragraph::new("q quit   ↑↓ choose a hive   r refresh   + slower   - faster").dim(),
            keys,
        );
    }
}

impl HiveView {
    /// The view of `hive`, on `hub`, given what it was `elapsed` ago, and its issues.
    fn new(
        hub: &str,
        hive: &HiveActivity,
        activity: &HubActivity,
        earlier: Option<(Duration, &HiveActivity)>,
    ) -> (Self, Vec<String>) {
        let name = &hive.info.name;
        let traffic = &hive.traffic;
        let rate = |now: u64, then: fn(&HiveActivity) -> u64| match earlier {
            Some((elapsed, earlier)) if !elapsed.is_zero() => {
                let per_second = now.saturating_sub(then(earlier)) as f64 / elapsed.as_secs_f64();
                format!("{}/s", bytes(per_second as u64))
            }
            _ => "—".to_owned(),
        };
        let mut issues = vec![];
        if let Some(failure) = &hive.failure
            && failure.age <= RECENT_FAILURE
        {
            let what = if failure.request {
                "failed a request"
            } else {
                "had trouble"
            };
            issues.push(format!(
                "{name}: the hub {what} {} ago: {}",
                duration(failure.age),
                one_line(&failure.message)
            ));
        }
        let mut machines = vec![];
        let mut up_to_date = 0;
        for machine in &hive.machines {
            let (state, issue) = machine_state(machine, hive.head, activity.uptime);
            if issue {
                issues.push(format!("{name}: {} {state}", machine.name));
            } else if machine.report.is_some() && machine.behind.is_none() {
                up_to_date += 1;
            }
            let report = machine.report.as_ref();
            machines.push((
                vec![
                    machine.name.clone(),
                    machine
                        .heard
                        .map_or("—".to_owned(), |heard| format!("{} ago", duration(heard))),
                    report.map_or("—".to_owned(), |r| format!("#{}", r.seq)),
                    report.map_or("—".to_owned(), |r| r.version.clone()),
                    state,
                ],
                issue,
            ));
        }
        let row = vec![
            name.clone(),
            hive.head.map_or("—".to_owned(), |head| format!("#{head}")),
            rate(traffic.received, |h| h.traffic.received),
            rate(traffic.sent, |h| h.traffic.sent),
            traffic.ops_in.to_string(),
            traffic.commits_in.to_string(),
            format!("{up_to_date}/{}", hive.machines.len()),
            if issues.is_empty() {
                String::new()
            } else {
                issues.len().to_string()
            },
        ];
        let mut totals = format!(
            "since the hub started: received {} and sent {}; {} operations, writing {} \
             commits, came in, and {} went out; {} pushes moved the head, and {} found it \
             moved first",
            bytes(traffic.received),
            bytes(traffic.sent),
            traffic.ops_in,
            traffic.commits_in,
            traffic.ops_out,
            traffic.accepted,
            traffic.rejected,
        );
        if traffic.incomplete > 0 {
            write!(totals, "; {} lacked what they needed", traffic.incomplete).ok();
        }
        if traffic.failures > 0 {
            write!(totals, "; {} requests failed", traffic.failures).ok();
        }
        totals.push('.');
        let recent = hive
            .recent
            .iter()
            .map(|accepted| {
                vec![
                    format!("{} ago", duration(accepted.age)),
                    format!("#{}", accepted.seq),
                    accepted.host.clone(),
                    accepted.ops.to_string(),
                    accepted.commits.to_string(),
                    one_line(&accepted.description),
                ]
            })
            .collect();
        let view = Self {
            hub: hub.to_owned(),
            row,
            issues: issues.len(),
            totals,
            machines,
            recent,
        };
        (view, issues)
    }

    fn draw(&self, frame: &mut Frame<'_>, area: ratatui::layout::Rect) {
        let machine_lines = self.machines.len() + 1;
        let [totals, machines, gap, recent] = Layout::vertical([
            Constraint::Length(2),
            Constraint::Length(machine_lines.min(10) as u16),
            Constraint::Length(1),
            Constraint::Fill(1),
        ])
        .areas(area);
        let _ = gap;
        frame.render_widget(
            Paragraph::new(format!("{} {}", self.row[0], self.totals))
                .wrap(ratatui::widgets::Wrap { trim: true }),
            totals,
        );
        let rows = self.machines.iter().map(|(cells, issue)| {
            let row = Row::new(cells.clone());
            if *issue { row.red() } else { row }
        });
        let table = Table::new(
            rows,
            [
                Constraint::Length(16),
                Constraint::Length(9),
                Constraint::Length(7),
                Constraint::Length(8),
                Constraint::Fill(1),
            ],
        )
        .header(Row::new(MACHINE_HEADER).bold());
        frame.render_widget(table, machines);
        let rows = self.recent.iter().map(|cells| Row::new(cells.clone()));
        let table = Table::new(
            rows,
            [
                Constraint::Length(9),
                Constraint::Length(7),
                Constraint::Length(16),
                Constraint::Length(5),
                Constraint::Length(8),
                Constraint::Fill(1),
            ],
        )
        .header(Row::new(RECENT_HEADER).bold());
        frame.render_widget(table, recent);
    }
}

/// What to say of `machine`, in a hive whose head is `head`, on a hub up `uptime` seconds,
/// and whether it is an issue.
fn machine_state(machine: &MachineActivity, head: Option<u64>, uptime: u64) -> (String, bool) {
    let (Some(report), Some(heard)) = (&machine.report, machine.heard) else {
        // It may have left the hive: a machine's working copy stays in the hive's view.
        let state = if uptime < REPORTS_KEPT.as_secs() {
            format!(
                "not heard from since the hub started {} ago",
                duration(uptime)
            )
        } else {
            "not heard from in a day: it may have left the hive".to_owned()
        };
        return (state, false);
    };
    if heard > SILENT {
        return (
            format!(
                "not heard from in {}: offline, or its daemon isn't running",
                duration(heard)
            ),
            true,
        );
    }
    if let Some(error) = &report.error {
        return (format!("sync failing: {}", one_line(error)), true);
    }
    match (machine.behind, head) {
        (Some(behind), Some(head)) => {
            let heads = head.saturating_sub(report.seq);
            let heads = if heads == 1 {
                "1 head".to_owned()
            } else {
                format!("{heads} heads")
            };
            if behind > BEHIND {
                (format!("{heads} behind for {}", duration(behind)), true)
            } else {
                (format!("catching up, {heads} behind"), false)
            }
        }
        _ => ("up to date".to_owned(), false),
    }
}

/// `rows` under `header`, in columns, each line starting with `indent`.
fn columns<S: AsRef<str>>(header: &[&str], rows: &[Vec<S>], indent: &str) -> String {
    let mut widths: Vec<usize> = header.iter().map(|h| h.chars().count()).collect();
    for row in rows {
        for (width, cell) in widths.iter_mut().zip(row) {
            *width = (*width).max(cell.as_ref().chars().count());
        }
    }
    let mut out = String::new();
    let mut line = |cells: Vec<&str>| {
        let mut text = indent.to_owned();
        for (i, (cell, width)) in cells.iter().zip(&widths).enumerate() {
            if i + 1 == cells.len() {
                text.push_str(cell);
            } else {
                write!(text, "{cell:width$}  ").ok();
            }
        }
        writeln!(out, "{}", text.trim_end()).ok();
    };
    line(header.to_vec());
    for row in rows {
        line(row.iter().map(AsRef::as_ref).collect());
    }
    out
}

/// `text` on one line.
fn one_line(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// A number of bytes, in binary units.
fn bytes(n: u64) -> String {
    const UNITS: [&str; 5] = ["B", "KiB", "MiB", "GiB", "TiB"];
    let mut value = n as f64;
    let mut unit = 0;
    while value >= 1024.0 && unit + 1 < UNITS.len() {
        value /= 1024.0;
        unit += 1;
    }
    if unit == 0 {
        format!("{n} B")
    } else if value < 10.0 {
        format!("{value:.1} {}", UNITS[unit])
    } else {
        format!("{value:.0} {}", UNITS[unit])
    }
}

/// A number of seconds, in its largest unit or two.
fn duration(secs: u64) -> String {
    match secs {
        0..60 => format!("{secs}s"),
        60..3600 => format!("{}m", secs / 60),
        3600..86400 => format!("{}h{}m", secs / 3600, secs % 3600 / 60),
        _ => format!("{}d{}h", secs / 86400, secs % 86400 / 3600),
    }
}

#[cfg(test)]
mod tests {
    use musubi_hub::activity::Accepted;
    use musubi_hub::activity::Failure;
    use musubi_hub::activity::Report;
    use musubi_hub::activity::Traffic;
    use musubi_hub::hub_dir::HiveInfo;
    use ratatui::Terminal;
    use ratatui::backend::TestBackend;

    use super::*;

    fn machine(name: &str, heard: Option<u64>, seq: u64, behind: Option<u64>) -> MachineActivity {
        MachineActivity {
            key: format!("{name}#1234"),
            name: name.to_owned(),
            in_view: true,
            heard,
            report: heard.map(|_| Report {
                machine: format!("{name}#1234"),
                seq,
                error: None,
                version: "0.1.0".to_owned(),
            }),
            behind,
        }
    }

    fn activity(received: u64, failing: bool) -> HubActivity {
        let mut failed = machine("delta", Some(3), 9, None);
        if let Some(report) = &mut failed.report {
            report.error = Some("the hub refused:\nincompatible".to_owned());
        }
        HubActivity {
            version: "0.1.0".to_owned(),
            uptime: 3600,
            hives: vec![HiveActivity {
                info: HiveInfo {
                    id: "id".to_owned(),
                    name: "app".to_owned(),
                    backend: musubi_jj::objects::Backend::Git,
                    urls: vec![],
                    machines: vec![],
                },
                head: Some(10),
                traffic: Traffic {
                    received,
                    sent: 2048,
                    ops_in: 12,
                    commits_in: 7,
                    accepted: 5,
                    ..Traffic::default()
                },
                failure: failing.then(|| Failure {
                    age: 30,
                    message: "no blob".to_owned(),
                    request: true,
                }),
                recent: vec![Accepted {
                    age: 4,
                    seq: 10,
                    ops: 1,
                    commits: 2,
                    host: "laptop".to_owned(),
                    description: "rebase commit 1234".to_owned(),
                }],
                machines: vec![
                    machine("laptop", Some(4), 10, None),
                    machine("desktop", Some(600), 8, Some(700)),
                    machine("devbox", Some(5), 8, Some(90)),
                    machine("gone", None, 0, None),
                    failed,
                ],
            }],
        }
    }

    fn sample(at: Instant, received: u64) -> Sample {
        Sample {
            hubs: vec![
                HubSample {
                    hub: "devbox".to_owned(),
                    at,
                    activity: Ok(activity(received, true)),
                },
                HubSample {
                    hub: "elsewhere".to_owned(),
                    at,
                    activity: Err("the hub at elsewhere is out of reach".to_owned()),
                },
            ],
            daemon: Ok(None),
        }
    }

    /// Every kind of trouble is an issue: a daemon not running here, a hub out of reach,
    /// the hub failing, and machines silent, stuck, or failing; but not a machine catching
    /// up, nor one the hub hasn't heard from since it started, which may have left.
    #[test]
    fn issues_are_what_needs_attention() {
        let now = Instant::now();
        let view = View::new(&sample(now, 1024), None, None);
        assert_eq!(
            view.issues,
            [
                "This machine's daemon isn't running; `musubi daemon start` starts it.",
                "app: the hub failed a request 30s ago: no blob",
                "app: desktop not heard from in 10m: offline, or its daemon isn't running",
                "app: devbox 2 heads behind for 1m",
                "app: delta sync failing: the hub refused: incompatible",
                "Hub elsewhere: the hub at elsewhere is out of reach",
            ]
        );
        let states: Vec<&str> = view.hives[0]
            .machines
            .iter()
            .map(|(cells, _)| cells[4].as_str())
            .collect();
        assert_eq!(states[0], "up to date");
        assert_eq!(states[3], "not heard from since the hub started 1h0m ago");
    }

    /// Rates come from two refreshes; printed, the view shows every hive, its machines and
    /// its latest heads.
    #[test]
    fn rates_come_from_two_refreshes() {
        let then = Instant::now();
        let earlier = sample(then, 1024);
        let later = sample(then + Duration::from_secs(2), 1024 + 4096);
        let view = View::new(&later, Some(&earlier), None);
        assert_eq!(view.hives[0].row[2..4], ["2.0 KiB/s", "0 B/s"]);
        let first = View::new(&earlier, None, None);
        assert_eq!(first.hives[0].row[2], "—");
        let plain = view.plain();
        assert!(plain.contains("rebase commit 1234"), "{plain}");
        assert!(plain.contains("HIVE  HUB"), "{plain}");
        assert!(plain.contains("app   devbox  #10"), "{plain}");
        assert!(plain.contains("  laptop   4s ago"), "{plain}");
    }

    #[test]
    fn the_terminal_shows_the_chosen_hive() {
        let now = Instant::now();
        let mut app = App {
            interval: Duration::from_secs(5),
            latest: Some(sample(now, 0)),
            previous: None,
            selected: TableState::default().with_selected(3),
        };
        let mut terminal = Terminal::new(TestBackend::new(120, 40)).unwrap();
        terminal.draw(|frame| app.draw(frame)).unwrap();
        let screen: String = terminal
            .backend()
            .buffer()
            .content()
            .iter()
            .map(|cell| cell.symbol())
            .collect();
        assert_eq!(app.selected.selected(), Some(0));
        for shown in [
            "Issues:",
            "MACHINES",
            "desktop",
            "rebase commit 1234",
            "q quit",
        ] {
            assert!(screen.contains(shown), "{shown} isn't shown:\n{screen}");
        }
    }

    #[test]
    fn units() {
        assert_eq!(bytes(0), "0 B");
        assert_eq!(bytes(1023), "1023 B");
        assert_eq!(bytes(1536), "1.5 KiB");
        assert_eq!(bytes(200 << 20), "200 MiB");
        assert_eq!(duration(59), "59s");
        assert_eq!(duration(61), "1m");
        assert_eq!(duration(3 * 3600 + 120), "3h2m");
        assert_eq!(duration(90000), "1d1h");
    }
}
