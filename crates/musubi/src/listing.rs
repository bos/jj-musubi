//! The lines `musubi list` prints, through a template in jj's template language, as jj prints
//! `jj bookmark list`: each hub, each of its hives, and each copy of a hive here, in that
//! order, all one kind of line, whose template says how to show each.

use std::path::Path;
use std::path::PathBuf;

use jj_cli::generic_templater::GenericTemplateLanguage;
use jj_cli::generic_templater::GenericTemplatePropertyKind;
use jj_cli::templater::BoxedTemplateProperty;
use jj_cli::templater::TemplatePropertyExt as _;
use jj_cli::templater::TemplateRenderer;
use jj_cli::templater::WrapTemplateProperty;
use jj_lib::settings::UserSettings;
use musubi_hub::hub_dir::HiveInfo;

use crate::ui::Ui;

/// A line of `musubi list`: a hub, a hive, or a copy of a hive here.
#[derive(Clone, Default, serde::Serialize)]
pub struct Line {
    /// The hub, as `--hub` takes it.
    pub hub: String,
    /// Whether the hub answered.
    pub reached: bool,
    /// The hive's name; empty on a hub's line.
    pub hive: String,
    /// The hive's id; empty on a hub's line.
    pub id: String,
    /// The machines in the hive, as its hub knows them.
    pub machines: Vec<String>,
    /// Where the copy is; none on a hub's line or a hive's.
    pub path: Option<PathBuf>,
    /// How the copy's syncing goes; empty on a hub's line or a hive's.
    pub status: String,
    /// What's wrong, if anything: why the hub is out of reach, that the hive is no longer
    /// on it, or why the copy's syncing fails.
    pub problem: String,
}

impl Line {
    /// The line of `hub`, and why it is out of reach, if it is.
    pub fn hub(hub: &str, unreached: Option<String>) -> Self {
        Self {
            hub: hub.to_owned(),
            reached: unreached.is_none(),
            problem: unreached.unwrap_or_default(),
            ..Self::default()
        }
    }

    /// The line of the hive `info`, on `hub`, which answered.
    pub fn hive(hub: &str, info: &HiveInfo) -> Self {
        Self {
            hub: hub.to_owned(),
            reached: true,
            hive: info.name.clone(),
            id: info.id.clone(),
            machines: info.machines.clone(),
            ..Self::default()
        }
    }
}

type Language = GenericTemplateLanguage<'static, Line>;

impl<'a> WrapTemplateProperty<'a, Line> for GenericTemplatePropertyKind<'a, Line> {
    fn wrap_property(property: BoxedTemplateProperty<'a, Line>) -> Self {
        Self::Self_(property)
    }
}

/// Prints lines through the template given, or else `musubi.templates.list`.
pub struct Lister<'ui> {
    ui: &'ui Ui,
    template: TemplateRenderer<'static, Line>,
}

impl<'ui> Lister<'ui> {
    pub fn new(ui: &'ui Ui, template: Option<&str>, cwd: &Path) -> anyhow::Result<Self> {
        let text = match template {
            Some(text) => text.to_owned(),
            None => ui.config().get::<String>("musubi.templates.list")?,
        };
        let settings =
            UserSettings::from_config_and_home_dir(ui.config().clone(), etcetera::home_dir().ok())?;
        let template = ui.parse_template(&language(&settings, cwd), &text)?;
        Ok(Self { ui, template })
    }

    pub fn print(&self, line: &Line) -> std::io::Result<()> {
        self.template.format(line, self.ui.stdout().as_mut())
    }
}

/// The keywords of a line, as `musubi list --help` gives them.
fn language(settings: &UserSettings, cwd: &Path) -> Language {
    let mut language = Language::new(settings, cwd);
    language.add_keyword("hub", |line| {
        Ok(line.map(|line| line.hub).into_dyn_wrapped())
    });
    language.add_keyword("reached", |line| {
        Ok(line.map(|line| line.reached).into_dyn_wrapped())
    });
    language.add_keyword("hive", |line| {
        Ok(line.map(|line| line.hive).into_dyn_wrapped())
    });
    language.add_keyword("id", |line| Ok(line.map(|line| line.id).into_dyn_wrapped()));
    language.add_keyword("machines", |line| {
        Ok(line.map(|line| line.machines).into_dyn_wrapped())
    });
    language.add_keyword("path", |line| {
        Ok(line.map(|line| line.path).into_dyn_wrapped())
    });
    language.add_keyword("status", |line| {
        Ok(line.map(|line| line.status).into_dyn_wrapped())
    });
    language.add_keyword("problem", |line| {
        Ok(line.map(|line| line.problem).into_dyn_wrapped())
    });
    language
}
