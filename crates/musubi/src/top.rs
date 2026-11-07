//! `musubi top`: what flows through this machine's hubs, and what is wrong, refreshed as it
//! goes.
//!
//! Each refresh asks every hub for its activity (`musubi_hub::activity`): the bytes its
//! hives' requests and replies carried, the heads it accepted, its failures, and what each
//! machine's daemon last reported. Rates come from the difference between two refreshes. A
//! thread of its own asks, so that a hub slow to answer never holds up the keyboard.

mod sample;
#[cfg(test)]
mod tests;
mod view;

use std::io::IsTerminal as _;
use std::io::Write as _;
use std::sync::mpsc;
use std::time::Duration;

use ratatui::Frame;
use ratatui::crossterm::event;
use ratatui::crossterm::event::Event;
use ratatui::crossterm::event::KeyCode;
use ratatui::crossterm::event::KeyEvent;
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

/// The shortest and longest refresh, as `--interval` gives it or `+` and `-` choose it.
const FASTEST: Duration = Duration::from_secs(1);
pub const SLOWEST: Duration = Duration::from_secs(60 * 60);

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
    let mut sampler = Sampler::new(hubs, socket);
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?;
    if args.once || !std::io::stdout().is_terminal() {
        let sample = runtime.block_on(sampler.sample());
        let plain = View::new(&sample, None, None).plain();
        ui.stdout().write_all(plain.as_bytes())?;
        return Ok(());
    }
    interactive(sampler, runtime, args.interval)
}

/// What the sampling thread is told.
#[derive(Debug, PartialEq, Eq)]
enum Wake {
    /// Refresh now.
    Now,
    /// Refresh every so often from now on, starting now.
    Every(Duration),
}

fn interactive(
    mut sampler: Sampler,
    runtime: tokio::runtime::Runtime,
    interval: Duration,
) -> anyhow::Result<()> {
    let (samples_tx, samples) = mpsc::channel();
    let (wake, woken) = tokio::sync::mpsc::unbounded_channel();
    std::thread::Builder::new()
        .name("top sampler".to_owned())
        .spawn(move || {
            runtime.block_on(sample_until_told(
                async || sampler.sample().await,
                interval,
                samples_tx,
                woken,
            ));
        })?;
    let mut app = App::new(interval);
    let mut terminal = ratatui::try_init()?;
    let result = (|| -> anyhow::Result<()> {
        loop {
            while let Ok(sample) = samples.try_recv() {
                app.receive(sample);
            }
            terminal.draw(|frame| app.draw(frame))?;
            if !event::poll(Duration::from_millis(250))? {
                continue;
            }
            let Event::Key(key) = event::read()? else {
                continue;
            };
            match app.key(key) {
                Action::Quit => return Ok(()),
                Action::Wake(message) => {
                    wake.send(message).ok();
                }
                Action::None => {}
            }
        }
    })();
    ratatui::restore();
    result
}

/// Samples every `interval`, or when woken, until nobody listens.
async fn sample_until_told(
    mut sample: impl AsyncFnMut() -> Sample,
    mut interval: Duration,
    samples: mpsc::Sender<Sample>,
    mut woken: tokio::sync::mpsc::UnboundedReceiver<Wake>,
) {
    loop {
        if samples.send(sample().await).is_err() {
            return;
        }
        tokio::select! {
            () = tokio::time::sleep(interval) => {}
            message = woken.recv() => match message {
                Some(Wake::Now) => {}
                Some(Wake::Every(every)) => interval = every,
                None => return,
            }
        }
    }
}

struct App {
    interval: Duration,
    latest: Option<Sample>,
    previous: Option<Sample>,
    selected: TableState,
}

#[derive(Debug, PartialEq, Eq)]
enum Action {
    None,
    Quit,
    Wake(Wake),
}

impl App {
    fn new(interval: Duration) -> Self {
        Self {
            interval,
            latest: None,
            previous: None,
            selected: TableState::default().with_selected(0),
        }
    }

    fn receive(&mut self, sample: Sample) {
        self.previous = self.latest.replace(sample);
    }

    fn key(&mut self, key: KeyEvent) -> Action {
        if key.kind != KeyEventKind::Press {
            return Action::None;
        }
        match key.code {
            KeyCode::Char('q') | KeyCode::Esc => return Action::Quit,
            KeyCode::Char('c') if key.modifiers.contains(KeyModifiers::CONTROL) => {
                return Action::Quit;
            }
            KeyCode::Up | KeyCode::Char('k') => self.selected.select_previous(),
            KeyCode::Down | KeyCode::Char('j') => self.selected.select_next(),
            KeyCode::Char('r') => return Action::Wake(Wake::Now),
            KeyCode::Char('+') => {
                self.interval = (self.interval + FASTEST).min(SLOWEST);
                return Action::Wake(Wake::Every(self.interval));
            }
            KeyCode::Char('-') => {
                self.interval = self.interval.saturating_sub(FASTEST).max(FASTEST);
                return Action::Wake(Wake::Every(self.interval));
            }
            _ => {}
        }
        Action::None
    }

    fn draw(&mut self, frame: &mut Frame<'_>) {
        let Some(latest) = &self.latest else {
            frame.render_widget(Paragraph::new("Asking the hubs…"), frame.area());
            return;
        };
        let view = View::new(latest, self.previous.as_ref(), Some(self.interval));
        view.draw(frame, &mut self.selected);
    }
}
