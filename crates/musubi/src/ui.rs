//! What musubi prints, through jj's own formatting: labelled as jj labels what it prints,
//! and coloured as jj's `colors` config says, when `--color` or jj's `ui.color` says to.

use std::error::Error as _;
use std::io;
use std::io::Write;
use std::process::ExitCode;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;

use jj_cli::formatter::Formatter;
use jj_cli::formatter::FormatterExt as _;
use jj_cli::formatter::HeadingLabeledWriter;
use jj_cli::formatter::PlainTextFormatter;
use jj_cli::ui::ColorChoice;
use jj_lib::config::ConfigLayer;
use jj_lib::config::ConfigSource;
use jj_lib::config::StackedConfig;

/// The colours of musubi's own labels, beneath the user's config as jj's own are.
const COLORS: &str = include_str!("colors.toml");

/// The status musubi exits with when whoever reads its output stopped, as jj's does.
const UNREAD_STATUS: u8 = 3;

pub struct Ui {
    ui: jj_cli::ui::Ui,
    /// Whether whoever reads what it prints has stopped, as `head` does in `musubi list |
    /// head`. The command carries on all the same, printing nothing more there.
    unread: AtomicBool,
}

impl Ui {
    /// Prints as jj's config says, with colour as `color` says, if given, in place of
    /// `ui.color`.
    pub fn new(color: Option<ColorChoice>) -> anyhow::Result<Self> {
        let mut config = crate::settings::user_config()?;
        config.add_layer(ConfigLayer::parse(ConfigSource::Default, COLORS)?);
        Self::with_config(config, color)
    }

    /// Prints without colour, reading none of jj's config, which may be what's wrong.
    pub fn plain() -> Self {
        let mut config = StackedConfig::with_defaults();
        config.extend_layers(jj_cli::config::default_config_layers());
        Self::with_config(config, Some(ColorChoice::Never)).expect("jj's defaults are valid")
    }

    fn with_config(mut config: StackedConfig, color: Option<ColorChoice>) -> anyhow::Result<Self> {
        if let Some(color) = color {
            let mut layer = ConfigLayer::empty(ConfigSource::CommandArg);
            layer.set_value("ui.color", color.to_string())?;
            config.add_layer(layer);
        }
        let ui = jj_cli::ui::Ui::with_config(&config).map_err(|err| {
            let mut message = err.error.to_string();
            let mut source = err.error.source();
            while let Some(cause) = source {
                message = format!("{message}: {cause}");
                source = cause.source();
            }
            anyhow::anyhow!(message)
        })?;
        Ok(Self {
            ui,
            unread: AtomicBool::new(false),
        })
    }

    /// Whether what it prints may be coloured.
    pub fn color(&self) -> bool {
        self.ui.color()
    }

    /// What the command prints for its own sake.
    pub fn stdout(&self) -> Box<dyn Formatter + '_> {
        self.ui.new_formatter(Watched {
            output: self.ui.stdout(),
            unread: &self.unread,
        })
    }

    /// What the command says beside it.
    pub fn stderr(&self) -> Box<dyn Formatter + '_> {
        self.ui.new_formatter(Watched {
            output: self.ui.stderr(),
            unread: &self.unread,
        })
    }

    /// A warning, after `Warning: `, on stderr.
    pub fn warning(&self) -> HeadingLabeledWriter<Box<dyn Formatter + '_>, &'static str> {
        self.stderr()
            .into_labeled("warning")
            .with_heading("Warning: ")
    }

    /// A hint, after `Hint: `, on stderr, unless jj's `ui.quiet` is set.
    pub fn hint(&self) -> HeadingLabeledWriter<Box<dyn Formatter + '_>, &'static str> {
        let quiet = self.ui.status_formatter().is_none();
        let formatter = if quiet {
            Box::new(PlainTextFormatter::new(io::sink()))
        } else {
            self.stderr()
        };
        formatter.into_labeled("hint").with_heading("Hint: ")
    }

    /// Prints clap's help, or its error, as jj does, returning the status to exit with.
    pub fn clap_error(&self, err: &clap::Error) -> ExitCode {
        let text = if self.color() {
            err.render().ansi().to_string()
        } else {
            err.render().to_string()
        };
        let mut output = if err.use_stderr() {
            self.stderr()
        } else {
            self.stdout()
        };
        // Raw, as clap styled it, which the formatter would show escaped.
        output.raw().and_then(|mut raw| write!(raw, "{text}")).ok();
        drop(output);
        self.status(ExitCode::from(err.exit_code().try_into().unwrap_or(2)))
    }

    /// Says how the command went, as jj does, returning the status to exit with.
    pub fn finish(&self, result: anyhow::Result<()>) -> ExitCode {
        let Err(err) = result else {
            return self.status(ExitCode::SUCCESS);
        };
        writeln!(self.ui.error_with_heading("Error: "), "{err}")
            .and_then(|()| jj_cli::command_error::print_error_sources(&self.ui, err.source()))
            .ok();
        ExitCode::FAILURE
    }

    /// `status`, unless whoever read the output stopped.
    fn status(&self, status: ExitCode) -> ExitCode {
        if self.unread.load(Ordering::Relaxed) {
            ExitCode::from(UNREAD_STATUS)
        } else {
            status
        }
    }
}

/// Writes to `output`; once whoever reads it has stopped, notes so, and writes nothing more
/// there, so that a command carries on, and does all it would.
struct Watched<'a, W> {
    output: W,
    unread: &'a AtomicBool,
}

impl<W: Write> Watched<'_, W> {
    fn unless_unread<T>(&self, result: io::Result<T>, otherwise: T) -> io::Result<T> {
        match result {
            Err(err) if err.kind() == io::ErrorKind::BrokenPipe => {
                self.unread.store(true, Ordering::Relaxed);
                Ok(otherwise)
            }
            result => result,
        }
    }
}

impl<W: Write> Write for Watched<'_, W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let written = self.output.write(buf);
        self.unless_unread(written, buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        let flushed = self.output.flush();
        self.unless_unread(flushed, ())
    }
}
