//! What musubi prints, through jj's own formatting: labelled as jj labels what it prints,
//! and coloured as jj's `colors` config says, when `--color` or jj's `ui.color` says to.

use std::error::Error;
use std::fmt;
use std::io;
use std::io::Write;
use std::process::ExitCode;
use std::sync::Arc;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;

use jj_cli::cli_util::load_template_aliases;
use jj_cli::command_error::CommandError;
use jj_cli::command_error::ErrorHint;
use jj_cli::command_error::print_parse_diagnostics;
use jj_cli::formatter::Formatter;
use jj_cli::formatter::FormatterExt as _;
use jj_cli::formatter::HeadingLabeledWriter;
use jj_cli::formatter::PlainTextFormatter;
use jj_cli::template_builder;
use jj_cli::template_builder::TemplateLanguage;
use jj_cli::template_parser::TemplateDiagnostics;
use jj_cli::templater::TemplateRenderer;
use jj_cli::templater::WrapTemplateProperty;
use jj_cli::ui::ColorChoice;
use jj_lib::config::ConfigLayer;
use jj_lib::config::ConfigSource;
use jj_lib::config::StackedConfig;
use jj_lib::settings::UserSettings;

/// musubi's defaults in jj's config: its labels' colours, and its templates.
const DEFAULTS: &str = include_str!("defaults.toml");

/// The status musubi exits with when whoever reads its output stopped, as jj's does.
const UNREAD_STATUS: u8 = 3;

pub struct Ui {
    ui: jj_cli::ui::Ui,
    config: StackedConfig,
    /// Whether whoever reads what it prints has stopped, as `head` does in `musubi list |
    /// head`. The command carries on all the same, printing nothing more there.
    unread: AtomicBool,
}

impl Ui {
    /// Prints as jj's config says, with colour as `color` says, if given, in place of
    /// `ui.color`.
    pub fn new(color: Option<ColorChoice>) -> anyhow::Result<Self> {
        let mut config = crate::settings::user_config()?;
        config.add_layer(ConfigLayer::parse(ConfigSource::Default, DEFAULTS)?);
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
        let ui = jj_cli::ui::Ui::with_config(&config).map_err(hinted)?;
        Ok(Self {
            ui,
            config,
            unread: AtomicBool::new(false),
        })
    }

    /// jj's config, as it prints by.
    pub fn config(&self) -> &StackedConfig {
        &self.config
    }

    /// jj's settings, for a template language.
    pub fn settings(&self) -> anyhow::Result<UserSettings> {
        Ok(UserSettings::from_config_and_home_dir(
            self.config.clone(),
            etcetera::home_dir().ok(),
        )?)
    }

    /// `text`, a template in jj's template language, for `language`, with the template
    /// aliases jj's config defines, as jj parses its own; warns of what jj would.
    pub fn parse_template<'a, C, L>(
        &self,
        language: &L,
        text: &str,
    ) -> anyhow::Result<TemplateRenderer<'a, C>>
    where
        C: Clone + 'a,
        L: TemplateLanguage<'a> + ?Sized,
        L::Property: WrapTemplateProperty<'a, C>,
    {
        let aliases = load_template_aliases(&self.ui, &self.config).map_err(hinted)?;
        let mut diagnostics = TemplateDiagnostics::new();
        let template = template_builder::parse(language, &mut diagnostics, text, &aliases)
            .map_err(|err| hinted(err.into()))?;
        print_parse_diagnostics(&self.ui, "In template expression", &diagnostics)?;
        Ok(template)
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
        let hints = err
            .chain()
            .find_map(|cause| cause.downcast_ref::<Hinted>())
            .map_or(&[][..], |hinted| &hinted.hints);
        writeln!(self.ui.error_with_heading("Error: "), "{err}")
            .and_then(|()| jj_cli::command_error::print_error_sources(&self.ui, err.source()))
            .and_then(|()| self.print_hints(hints))
            .ok();
        ExitCode::FAILURE
    }

    /// Prints `hints` after an error, as jj does.
    fn print_hints(&self, hints: &[ErrorHint]) -> io::Result<()> {
        let mut formatter = self.stderr().into_labeled("hint");
        for hint in hints {
            write!(formatter.labeled("heading"), "Hint: ")?;
            match hint {
                ErrorHint::PlainText(text) => writeln!(formatter, "{text}")?,
                ErrorHint::Formatted(recorded) => {
                    recorded.replay(formatter.as_mut())?;
                    if !recorded.data().ends_with(b"\n") {
                        writeln!(formatter)?;
                    }
                }
            }
        }
        Ok(())
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

/// An error of jj's, with the hints jj prints after it.
#[derive(Debug)]
struct Hinted {
    error: Arc<dyn Error + Send + Sync>,
    hints: Vec<ErrorHint>,
}

impl fmt::Display for Hinted {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.error.fmt(f)
    }
}

impl Error for Hinted {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.error.source()
    }
}

fn hinted(err: CommandError) -> anyhow::Error {
    anyhow::Error::new(Hinted {
        error: err.error,
        hints: err.hints,
    })
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
