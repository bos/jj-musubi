//! One-time defaults for a new copy. Sync never reads or applies these values.

use std::collections::BTreeMap;
use std::path::Path;

use anyhow::Context as _;
use jj_lib::config::ConfigGetResultExt as _;
use jj_lib::config::ConfigNamePathBuf;
use jj_lib::config::ConfigSource;
use jj_lib::config::ConfigValue;
use jj_lib::config::StackedConfig;

use crate::settings;

/// Whether the destination has explicitly configured a value, including in a conditional
/// scope or through the environment. jj's built-in defaults don't prevent seeding.
fn configured(config: &StackedConfig, name: &ConfigNamePathBuf) -> bool {
    config.layers().iter().rev().any(|layer| {
        layer.source != ConfigSource::Default && layer.look_up_item(name).ok().flatten().is_some()
    })
}

/// Expiry is local even when a selection names its containing table.
fn permitted(name: &ConfigNamePathBuf) -> bool {
    let parts: Vec<_> = name.components().map(|key| key.get()).collect();
    !matches!(
        parts.as_slice(),
        ["musubi"] | ["musubi", "forget-after", ..]
    )
}

/// Captures the creator's selected, effective values, rather than jj's built-in defaults.
pub fn capture(config: &StackedConfig) -> anyhow::Result<BTreeMap<String, String>> {
    let keys = config
        .get::<Vec<String>>("musubi.clone-config")
        .optional()?
        .unwrap_or_else(|| vec!["user.name".to_owned(), "user.email".to_owned()]);
    let mut values = BTreeMap::new();
    for key in keys {
        let name: ConfigNamePathBuf = key.parse().context("invalid key in musubi.clone-config")?;
        // This policy belongs to the new copy and depends on who runs clone.
        if !permitted(&name) {
            anyhow::bail!("musubi.clone-config cannot include musubi.forget-after");
        }
        if configured(config, &name) {
            let mut value = config.get_value(&name)?;
            value.decor_mut().clear();
            values.insert(key, value.to_string());
        }
    }
    Ok(values)
}

/// Validates every supplied key and TOML value before creating the destination, and
/// selects only values not explicitly set there. Returns parsed values for writing once.
pub fn missing(
    config: &StackedConfig,
    defaults: &BTreeMap<String, String>,
) -> anyhow::Result<Vec<(ConfigNamePathBuf, ConfigValue)>> {
    let mut values = Vec::new();
    for (key, text) in defaults {
        let name: ConfigNamePathBuf = key.parse().context("invalid clone config key")?;
        anyhow::ensure!(
            permitted(&name),
            "clone config cannot include musubi.forget-after"
        );
        let value: ConfigValue = text.trim().parse().context("invalid clone config value")?;
        if !configured(config, &name) {
            values.push((name, value));
        }
    }
    Ok(values)
}

/// Rechecks the new copy's resolved config, so its user's values still take precedence
/// if they changed during initialization. No config id or file is created when none is missing.
pub fn seed(destination: &Path, defaults: &BTreeMap<String, String>) -> anyhow::Result<()> {
    let repo = destination.join(".jj/repo");
    let config = settings::load(destination, &repo)?;
    let values = missing(config.config(), defaults)?;
    if values.is_empty() {
        return Ok(());
    }
    let path = settings::repo_config_path(&repo)?.context("new repository has no config path")?;
    let mut file = jj_lib::config::ConfigFile::load_or_empty(ConfigSource::Repo, &path)?;
    for (name, value) in values {
        file.set_value(&name, value)?;
    }
    file.save()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use jj_lib::config::ConfigLayer;

    use super::*;

    /// Selection accepts ordinary TOML values, but never turns jj defaults into overrides.
    /// A destination's own values win even when different, and an empty selection opts out.
    #[test]
    fn selected_defaults_fill_only_missing_values() {
        let mut source = StackedConfig::with_defaults();
        let mut layer = ConfigLayer::empty(ConfigSource::Repo);
        layer.set_value("user.name", "Creator").unwrap();
        layer
            .set_value("user.email", "creator@example.org")
            .unwrap();
        layer
            .set_value("aliases.l", ConfigValue::from_iter(["log", "--no-graph"]))
            .unwrap();
        source.add_layer(layer.clone());
        let defaults = capture(&source).unwrap();
        assert_eq!(defaults.len(), 2);
        let mut destination = StackedConfig::with_defaults();
        assert_eq!(missing(&destination, &defaults).unwrap().len(), 2);
        let mut existing = ConfigLayer::empty(ConfigSource::User);
        existing.set_value("user.name", "Local User").unwrap();
        destination.add_layer(existing);
        let values = missing(&destination, &defaults).unwrap();
        assert_eq!(values.len(), 1);
        assert_eq!(values[0].0.to_string(), "user.email");
        layer
            .set_value("musubi.clone-config", ConfigValue::from_iter(["aliases.l"]))
            .unwrap();
        source.add_layer(layer.clone());
        let selected = capture(&source).unwrap();
        assert_eq!(
            missing(&destination, &selected).unwrap()[0]
                .1
                .as_array()
                .unwrap()
                .len(),
            2
        );
        layer
            .set_value(
                "musubi.clone-config",
                ConfigValue::from_iter(std::iter::empty::<&str>()),
            )
            .unwrap();
        source.add_layer(layer.clone());
        assert!(capture(&source).unwrap().is_empty());
        for key in [
            "musubi.forget-after",
            "musubi",
            "musubi.forget-after.nested",
        ] {
            layer
                .set_value("musubi.clone-config", ConfigValue::from_iter([key]))
                .unwrap();
            source.add_layer(layer.clone());
            assert!(capture(&source).is_err());
            assert!(missing(&destination, &[(key.to_owned(), "{}".to_owned())].into()).is_err());
        }
        assert!(capture(&StackedConfig::with_defaults()).unwrap().is_empty());
    }
}
