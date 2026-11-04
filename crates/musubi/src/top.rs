//! `musubi top`: what flows through this machine's hubs, and what is wrong, refreshed as it
//! goes.
//!
//! Each refresh asks every hub for its activity (`musubi_hub::activity`): the bytes its
//! hives' requests and replies carried, the heads it accepted, its failures, and what each
//! machine's daemon last reported. Rates come from the difference between two refreshes. A
//! thread of its own asks, so that a hub slow to answer never holds up the keyboard.

mod sample;
mod view;

use std::io::IsTerminal as _;
use std::io::Write as _;
use std::sync::mpsc;
use std::time::Duration;

use ratatui::Frame;
use ratatui::crossterm::event;
use ratatui::crossterm::event::Event;
use ratatui::crossterm::event::KeyCode;
use ratatui::crossterm::event::KeyEventKind;
use ratatui::crossterm::event::KeyModifiers;
use ratatui::widgets::Paragraph;
use ratatui::widgets::TableState;

use self::sample::Sample;
use self::sample::Sampler;
use self::sample::known_hubs;
use self::view::View;

use crate::hub;
use crate::socket::Socket;
use crate::ui::Ui;

/// The shortest and longest refresh `+` and `-` choose.
const FASTEST: Duration = Duration::from_secs(1);
const SLOWEST: Duration = Duration::from_secs(60);

pub struct Args {
    pub hub: Option<String>,
    pub interval: Duration,
    pub once: bool,
}

pub fn run(ui: &Ui, args: Args, socket: anyhow::Result<Socket>) -> anyhow::Result<()> {
    let hubs = match args.hub {
        Some(hub) => vec![hub::resolve(&hub)],
        None => known_hubs()?,
    };
    if hubs.is_empty() {
        crate::list::no_hubs(ui)?;
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
        view.draw(frame, &mut self.selected);
    }
}
