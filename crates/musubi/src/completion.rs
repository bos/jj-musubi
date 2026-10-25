//! Shell completion, two ways: a script that `musubi completion` prints, which knows the
//! commands, flags, and paths; and musubi completing each word as it is typed, when the shell
//! runs it with `COMPLETE` set, which also knows the hubs and the default hub's hives.

use std::io::Write as _;
use std::time::Duration;

use clap::CommandFactory as _;
use clap_complete::CompletionCandidate;

use crate::Cli;
use crate::config::HiveConfig;
use crate::config::UserState;
use crate::repo::Located;
use crate::ui::Ui;

/// How long completing a hive's name waits for the hub, while the shell waits on it.
const HUB_LIMIT: Duration = Duration::from_secs(2);

/// What `musubi completion --help` adds, on completing as you type.
pub const AS_YOU_TYPE: &str = "\
To complete hive and hub names as well, have your shell ask musubi as you type: run this in
its startup file, in place of the script.

  bash:        source <(COMPLETE=bash musubi)
  zsh:         source <(COMPLETE=zsh musubi)
  fish:        COMPLETE=fish musubi | source
  elvish:      eval (E:COMPLETE=elvish musubi | slurp)
  powershell:  $env:COMPLETE = \"powershell\"; musubi | Out-String | Invoke-Expression; Remove-Item Env:\\COMPLETE";

/// A shell `musubi completion` prints a script for.
#[derive(Clone, Copy, clap::ValueEnum)]
pub enum Shell {
    Bash,
    Elvish,
    Fish,
    Nushell,
    Powershell,
    Zsh,
}

/// Prints the completion script for `shell`.
pub fn print_script(ui: &Ui, shell: Shell) -> anyhow::Result<()> {
    use clap_complete::Shell as Clap;
    let mut command = Cli::command();
    let name = command.get_name().to_owned();
    let mut script = vec![];
    match shell {
        Shell::Bash => clap_complete::generate(Clap::Bash, &mut command, name, &mut script),
        Shell::Elvish => clap_complete::generate(Clap::Elvish, &mut command, name, &mut script),
        Shell::Fish => clap_complete::generate(Clap::Fish, &mut command, name, &mut script),
        Shell::Nushell => {
            clap_complete::generate(
                clap_complete_nushell::Nushell,
                &mut command,
                name,
                &mut script,
            );
        }
        Shell::Powershell => {
            clap_complete::generate(Clap::PowerShell, &mut command, name, &mut script);
        }
        Shell::Zsh => clap_complete::generate(Clap::Zsh, &mut command, name, &mut script),
    }
    ui.stdout().raw()?.write_all(&script)?;
    Ok(())
}

/// Completes the word being typed, and exits, if the shell is asking.
pub fn complete_if_asked() {
    clap_complete::CompleteEnv::with_factory(Cli::command).complete();
}

/// The hives of this machine's copies, leaving out copies that are gone.
fn memberships(state: &UserState) -> Vec<HiveConfig> {
    state
        .repos
        .iter()
        .filter_map(|workspace| Located::find(workspace).ok())
        .filter_map(|located| HiveConfig::load(&located.repo_path).ok().flatten())
        .collect()
}

/// The hubs this machine knows of, for `--hub`.
pub fn hubs() -> Vec<CompletionCandidate> {
    let Ok(state) = UserState::load() else {
        return vec![];
    };
    let default = state.default_hub().ok().flatten();
    UserState::known_hubs(default.clone(), &memberships(&state))
        .into_iter()
        .map(|hub| {
            let default = default.as_ref() == Some(&hub);
            CompletionCandidate::new(hub).help(default.then(|| "the default hub".into()))
        })
        .collect()
}

/// The default hub's hives, which commands without `--hub` act on; or if it doesn't answer
/// in time, the hives of this machine's copies on it.
pub fn hives() -> Vec<CompletionCandidate> {
    let Ok(state) = UserState::load() else {
        return vec![];
    };
    let Some(hub) = &state.default_hub().ok().flatten() else {
        return vec![];
    };
    let answer =
        crate::block_on(async { tokio::time::timeout(HUB_LIMIT, crate::list_hub(hub)).await? });
    match answer {
        Ok(infos) => infos
            .iter()
            .map(|info| {
                CompletionCandidate::new(&info.name).help(Some(crate::machines(info).into()))
            })
            .collect(),
        Err(_) => memberships(&state)
            .iter()
            .filter(|copy| &copy.hub == hub)
            .map(|copy| CompletionCandidate::new(copy.display_name()))
            .collect(),
    }
}
