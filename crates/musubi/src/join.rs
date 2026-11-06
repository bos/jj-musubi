//! Creating, joining, and cloning hives, and starting their first sync.

use std::io::Write as _;
use std::path::Path;
use std::process::Command as Process;
use std::time::Duration;

use anyhow::Context as _;
use jj_cli::formatter::FormatterExt as _;
use jj_lib::object_id::ObjectId as _;
use musubi_hub::hub_dir::JoinChoice;
use musubi_hub::hub_dir::JoinRequest;
use musubi_hub::hub_dir::Joined;
use musubi_jj::node::NodeRepo;
use musubi_jj::objects::Backend;
use musubi_sync::wire::HubWideReply;
use musubi_sync::wire::HubWideRequest;

use crate::block_on;
use crate::cli::Member;
use crate::clone_config;
use crate::config::Entry;
use crate::config::HiveConfig;
use crate::config::Membership;
use crate::config::UserState;
use crate::control;
use crate::copy;
use crate::daemon;
use crate::daemon::Status;
use crate::hub;
use crate::repo::Located;
use crate::settings;
use crate::socket::Socket;
use crate::ssh;
use crate::sync::daemon_progress;
use crate::sync::sync_directly;
use crate::ui::Ui;

/// Makes the repository at `start` part of a hive: the hub decides which (see
/// `musubi_hub::matching`); then this records the membership and has the daemon serve it.
/// `original` makes a repository the copy of its key that isn't (see [`copy`]).
pub fn join(
    ui: &Ui,
    start: &Path,
    choice: JoinChoice,
    member: &Member,
    original: bool,
    socket: &Socket,
) -> anyhow::Result<()> {
    let Member {
        machine,
        full_history,
        hub,
    } = member;
    let (hub, machine, full_history) = (hub.as_deref(), machine.as_deref(), *full_history);
    let located = Located::find(start)?;
    copy::check_owner(&located.repo_path)?;
    let found = copy::Found::resolve(&located)?;
    let state = UserState::load()?;
    let entry = found.key.as_deref().and_then(|key| state.entry(key));
    let standing = copy::standing_of(&located, &found, entry);
    // `musubi join` in a repository that is part of a hive joins that hive again, made again
    // if its hub has lost it.
    let rejoin = |record: &HiveConfig| -> anyhow::Result<(JoinChoice, String)> {
        let remake = JoinChoice::Remake {
            id: record.hive.to_string(),
            name: record.name.clone(),
        };
        let hub = hub.map_or_else(|| Ok(record.hub.clone()), |hub| UserState::hub(Some(hub)))?;
        Ok((remake, hub))
    };
    let (choice, hub) = match (standing, &found.record, choice) {
        (copy::Standing::Outside, _, choice) => (choice, UserState::hub(hub)?),
        (copy::Standing::Removed, Some(record), JoinChoice::Match) => anyhow::bail!(
            "this repository's hive, {}, was removed from its hub; `musubi join --hive \
             <name>` joins another, and `musubi create` starts a new one",
            record.display_name()
        ),
        (copy::Standing::Removed, _, choice) => (choice, UserState::hub(hub)?),
        // From any of its workspaces, or through a bind mount: one entry serves them all.
        (copy::Standing::Copy, Some(record), JoinChoice::Match) => rejoin(record)?,
        (copy::Standing::Duplicate | copy::Standing::Unknown, Some(record), JoinChoice::Match)
            if original =>
        {
            if let Some(path) = entry.and_then(copy::whereabouts) {
                anyhow::bail!(
                    "the copy of this repository's key is at {}, so this repository isn't it; \
                     `musubi clone` makes another copy",
                    path.display()
                );
            }
            rejoin(record)?
        }
        (copy::Standing::Copy, Some(record), _) => anyhow::bail!(
            "this repository is already part of hive {}; `musubi leave` first to join another",
            record.display_name()
        ),
        (standing, record, _) => {
            anyhow::bail!("{}", copy::not_the_copy(standing, record.as_ref(), entry))
        }
    };
    let remaking = matches!(choice, JoinChoice::Remake { .. });
    configured_forget_after(settings::load(&located.workspace_root, &located.repo_path)?.config())?;
    set_machine_name(&located, machine)?;
    let node = located.open()?;
    let summary = node.join_summary()?;
    let mut remotes = summary.remote_snapshot();
    if let JoinChoice::Remake { id, .. } = &choice {
        node.check_recorded_remote_bindings(id, &mut remotes)?;
    }
    let request = JoinRequest {
        choice,
        backend: summary.backend,
        clone_config: clone_config::capture(node.loader().settings().config())?,
        remote_bindings: remotes.bindings.clone(),
        remotes: summary
            .remotes
            .into_iter()
            .flat_map(|(name, remote)| {
                let urls: Vec<String> = remote.urls().map(str::to_owned).collect();
                urls.into_iter().map(move |url| (name.clone(), url))
            })
            .collect(),
        dir_name: located
            .workspace_root
            .file_name()
            .map(|name| name.to_string_lossy().into_owned())
            .unwrap_or_default(),
        roots: summary.roots.iter().map(|id| id.hex()).collect(),
        remote_targets: summary.remote_targets.iter().map(|id| id.hex()).collect(),
        machine: node.machine().key().to_owned(),
    };
    drop(node);
    let joined = match block_on(ask_preparing(ui, &hub, HubWideRequest::Join(request)))? {
        HubWideReply::Joined(joined) => joined,
        other => anyhow::bail!("unexpected reply from the hub: {other:?}"),
    };
    become_node(
        ui,
        &located,
        &joined,
        &hub,
        full_history,
        found.record.as_ref(),
        &remotes,
    )?;
    let count = joined.hive.machines.len();
    let machines = if count == 1 {
        "1 machine".to_owned()
    } else {
        format!("{count} machines")
    };
    // The daemon may serve the repository with the hub it knew: `start_serving` has it start
    // over.
    let mut out = ui.stdout();
    let name = &joined.hive.name;
    if remaking && joined.created {
        write!(out, "Made hive ")?;
        write!(out.labeled("hive"), "{name}")?;
        writeln!(out, " again from this repository")?;
    } else if remaking {
        write!(out, "Hive ")?;
        write!(out.labeled("hive"), "{name}")?;
        writeln!(out, " is on the hub, and this repository is part of it")?;
    } else if joined.created {
        write!(out, "Created hive ")?;
        writeln!(out.labeled("hive"), "{name}")?;
    } else {
        write!(out, "Joined hive ")?;
        write!(out.labeled("hive"), "{name}")?;
        writeln!(out, " ({}), {machines}", joined.reason)?;
    }
    drop(out);
    start_serving(ui, &located, socket)
}
/// Asks `hub`, over ssh first making sure this machine's key works there.
async fn ask_preparing(
    ui: &Ui,
    hub: &str,
    request: HubWideRequest,
) -> anyhow::Result<HubWideReply> {
    if !hub::is_local(hub) {
        ssh::prepare(ui, hub).await?;
    }
    hub::ask(hub, request).await
}

fn set_machine_name(located: &Located, machine: Option<&str>) -> anyhow::Result<()> {
    if let Some(name) = machine {
        let settings = settings::load(&located.workspace_root, &located.repo_path)?;
        let machine = NodeRepo::name_machine(&located.repo_path, name, &settings)?;
        // The same name again, as when retrying a refused join, is no change.
        anyhow::ensure!(
            machine.name() == musubi_jj::workspaces::sanitize(name),
            "this repository's machine is already named {}",
            machine.name()
        );
    }
    Ok(())
}

/// Records that the repository is part of the hive it `joined`: the join operation (unless
/// replicating full history), its record, and its entry, for the daemon to serve it. A copy
/// whose record named another hive, `before`, forgets the copies its history brings that the
/// hive doesn't have. The first hub joined becomes the user's default.
fn become_node(
    ui: &Ui,
    located: &Located,
    joined: &Joined,
    hub: &str,
    full_history: bool,
    before: Option<&HiveConfig>,
    remotes: &musubi_jj::remote_url::JoinRemotes,
) -> anyhow::Result<()> {
    let hive_id: uuid::Uuid = joined
        .hive
        .id
        .parse()
        .context("the hub sent a malformed hive id")?;
    let mut node = located.open()?;
    let machine = node.machine().name().to_owned();
    let key = node.machine().key().to_owned();
    let description = format!("musubi: {machine} joins the hive");
    if full_history {
        node.mark_joined_with_remotes(&description, &joined.hive.id, remotes)?;
    } else {
        node.create_join_operation_with_remotes(&description, &joined.hive.id, remotes)?;
    }
    // A hive doesn't take on the members of another: they aren't its own until they join it.
    if before.is_none_or(|before| before.hive != hive_id) {
        let keep: std::collections::BTreeSet<String> = joined.present.iter().cloned().collect();
        node.forget_copies_except(&keep)?;
    }
    drop(node);
    // Only joining gives the repository a jj config id, which its record and entry name.
    settings::repo_config_path(&located.repo_path)?;
    let config_id = copy::Found::read(&located.repo_path)?
        .config_id
        .context("jj gave this repository no config id")?;
    // Through the workspace it joined from already, if this is another of the same
    // repository's.
    let path = UserState::load()?
        .entry(&key)
        .filter(|entry| {
            Located::find(&entry.path)
                .is_ok_and(|other| copy::same_directory(&other.repo_path, &located.repo_path))
        })
        .map_or_else(
            || located.workspace_root.clone(),
            |entry| entry.path.clone(),
        );
    // The entry first: a record that names a config id no entry here does would make this
    // repository look like a duplicate, if what follows failed.
    UserState::put_entry(Entry {
        key,
        hive: hive_id,
        config_id: config_id.clone(),
        path,
    })?;
    let config = HiveConfig {
        hive: hive_id,
        name: Some(joined.hive.name.clone()),
        hub: hub.to_owned(),
        node: machine,
        config_id,
        state: Membership::Joined,
    };
    {
        let _lock = HiveConfig::lock(&located.repo_path)?;
        config.save(&located.repo_path)?;
    }
    set_forget_after(ui, located)?;
    UserState::save_default_hub(hub)?;
    Ok(())
}

/// The environment variables that say an agent is running musubi, as the devbox tool
/// detects agents.
const AGENT_VARIABLES: [&str; 3] = [
    "CODEX_THREAD_ID",
    "CODEX_SESSION_ID",
    "CLAUDE_CODE_SESSION_ID",
];

/// How long an agent's copy may go unused before the hive forgets it, by default.
const AGENT_FORGET_AFTER: &str = "6h";

/// Sets `musubi.forget-after` in the repository's config, unless jj's config sets it
/// already: `6h` if an agent is joining, as on a short-lived machine, `never` otherwise. A
/// value in the user's config, as an agent's image might set, wins, and so does the one
/// set when the repository last joined. Says so if it sets `6h`, which a person watching
/// an agent may not expect.
fn set_forget_after(ui: &Ui, located: &Located) -> anyhow::Result<()> {
    let settings = settings::load(&located.workspace_root, &located.repo_path)?;
    if configured_forget_after(settings.config())?.is_some() {
        return Ok(());
    }
    let name: jj_lib::config::ConfigNamePathBuf = musubi_jj::node::FORGET_AFTER_KEY.parse()?;
    let agent = AGENT_VARIABLES
        .iter()
        .any(|var| std::env::var_os(var).is_some());
    let value = if agent { AGENT_FORGET_AFTER } else { "never" };
    let path = settings::repo_config_path(&located.repo_path)?
        .context("this repository has no config of its own")?;
    let mut file =
        jj_lib::config::ConfigFile::load_or_empty(jj_lib::config::ConfigSource::Repo, &path)?;
    file.set_value(&name, value)?;
    file.save()?;
    if agent {
        writeln!(
            ui.stdout(),
            "The hive forgets this copy once it goes unused for {AGENT_FORGET_AFTER}."
        )?;
    }
    Ok(())
}

/// `musubi.forget-after` as `config` sets it, and where: `None` if nothing does. Fails if
/// its value is neither `never` nor a duration, before a command joining a copy writes
/// anything.
fn configured_forget_after(
    config: &jj_lib::config::StackedConfig,
) -> anyhow::Result<Option<(jj_lib::config::ConfigSource, Option<Duration>)>> {
    let key = musubi_jj::node::FORGET_AFTER_KEY;
    let name: jj_lib::config::ConfigNamePathBuf = key.parse()?;
    let Some((source, value)) = config
        .layers()
        .iter()
        .rev()
        .filter(|layer| layer.source != jj_lib::config::ConfigSource::Default)
        .find_map(|layer| {
            let item = layer.look_up_item(&name).ok()??;
            Some((layer.source, item.as_str().map(str::to_owned)))
        })
    else {
        return Ok(None);
    };
    let after = value
        .as_deref()
        .and_then(musubi_jj::presence::parse_forget_after)
        .with_context(|| {
            format!(
                "{key} in your {source} config is neither `never` nor a duration such as `6h`; \
                 fix it and run this again"
            )
        })?;
    Ok(Some((source, after)))
}
/// Has the daemon, started if need be, serve the repository, and reports its first sync.
/// Without a daemon, syncs once.
fn start_serving(ui: &Ui, located: &Located, socket: &Socket) -> anyhow::Result<()> {
    /// How asking the daemon to serve the repository went.
    enum Served {
        /// There was no daemon to ask, nor could one be started.
        NoDaemon(anyhow::Error),
        Synced,
        /// The daemon serves it, but its first sync failed, saying this.
        Failed(String),
    }
    let key = copy::Found::read(&located.repo_path)?
        .key
        .context("this repository has no machine key")?;
    // The client lives on the runtime that made it, so one runtime does it all.
    let served = block_on(async {
        let client = match daemon::ensure(socket).await {
            Ok(client) => client,
            Err(err) => return Ok(Served::NoDaemon(err)),
        };
        let add = client.add(control::context(Duration::from_secs(3600)), key.clone());
        let first = ui
            .while_waiting(add, daemon_progress(&client, &key))
            .await
            .context("asking the daemon to serve this repository")?;
        Ok::<_, anyhow::Error>(match first {
            Ok(_) => Served::Synced,
            Err(message) => Served::Failed(message),
        })
    })?;
    match served {
        Served::NoDaemon(err) => {
            writeln!(
                ui.warning(),
                "Could not start the daemon ({err:#}); syncing once instead."
            )?;
            sync_directly(ui, located)?;
            writeln!(ui.hint(), "Run `musubi daemon` to keep it in sync.")?;
            Ok(())
        }
        Served::Synced => Ok(()),
        // Unless it's a failure no retry gets past, as the daemon recorded before it answered.
        Served::Failed(message)
            if Status::load(&located.repo_path).is_some_and(|status| status.paused) =>
        {
            anyhow::bail!("the first sync failed: {message}")
        }
        Served::Failed(message) => anyhow::bail!(
            "the first sync failed: {message}\nThe daemon keeps trying; `musubi status` shows how \
             it goes."
        ),
    }
}

pub fn clone(
    ui: &Ui,
    destination: &Path,
    hive: &str,
    hub: Option<&str>,
    machine: Option<&str>,
    socket: &Socket,
) -> anyhow::Result<()> {
    check_clone_destination(destination)?;
    let hub = UserState::hub(hub)?;
    configured_forget_after(&settings::user_config()?)?;
    let reply = block_on(ask_preparing(
        ui,
        &hub,
        HubWideRequest::Resolve {
            name: hive.to_owned(),
        },
    ))?;
    let HubWideReply::Hive(info) = reply else {
        anyhow::bail!("unexpected reply from the hub: {reply:?}");
    };
    let remotes = if info.backend == Backend::Git {
        musubi_jj::inherited_remotes::read(&destination.join(".git"))
            .map_err(|err| anyhow::anyhow!("could not read inherited Git configuration: {err}"))?
    } else {
        musubi_jj::remote_url::JoinRemotes::default()
    };
    let resolved_id = musubi_hub::hub_dir::HiveId::from(info.id);
    let reply = block_on(ask_preparing(
        ui,
        &hub,
        HubWideRequest::PrepareClone {
            hive: resolved_id.clone(),
            backend: info.backend,
            remote_bindings: remotes.bindings.clone(),
        },
    ))?;
    let HubWideReply::Hive(info) = reply else {
        anyhow::bail!("unexpected reply from the hub: {reply:?}");
    };
    anyhow::ensure!(
        info.id == resolved_id.as_str(),
        "the hub returned a different hive during clone; run `musubi clone` again"
    );
    clone_config::missing(&jj_lib::config::StackedConfig::empty(), &info.clone_config)?;
    let dest = destination.to_str().context("destination is not UTF-8")?;
    let init: &[&str] = match info.backend {
        Backend::Git => &["git", "init", "--colocate"],
        Backend::Simple => &["debug", "init-simple"],
    };
    // All preflight checks have passed. Make the empty destination too, so jj's conditional
    // scopes see its actual path, including symlink ancestors and relative `..` components.
    std::fs::create_dir_all(destination)
        .with_context(|| format!("making {}", destination.display()))?;
    let workspace = destination.canonicalize()?;
    let destination_settings = settings::load(&workspace, &workspace.join(".jj/repo"))?;
    let defaults = clone_config::missing(destination_settings.config(), &info.clone_config)?;
    let mut jj = Process::new("jj");
    musubi_jj::git_command::without_repository_env(&mut jj);
    // Use the defaults for the initial working-copy commit too. Arguments are passed
    // directly to jj; no shell or source machine config file is involved.
    for (name, value) in defaults {
        jj.arg("--config").arg(format!("{name}={value}"));
    }
    // Contacting the hub may have taken long enough for another process to fill it.
    check_clone_destination(destination)?;
    // Its "Initialized repo in" names the directory relative to wherever this runs, ahead of
    // what musubi says, so it shows only if init fails.
    let output = jj
        .args(init)
        .arg(dest)
        .output()
        .with_context(|| format!("running `jj {}`", init.join(" ")))?;
    anyhow::ensure!(
        output.status.success(),
        "`jj {} {dest}` failed: {}",
        init.join(" "),
        String::from_utf8_lossy(&output.stderr).trim()
    );
    let located = Located::find(destination)?;
    clone_config::seed(&located.workspace_root, &info.clone_config)?;
    set_machine_name(&located, machine)?;
    let joined = Joined {
        hive: info.clone(),
        created: false,
        reason: String::new(),
        present: vec![],
    };
    become_node(ui, &located, &joined, &hub, false, None, &remotes)?;
    start_serving(ui, &located, socket)
        .with_context(|| format!("the new copy at {} didn't sync", destination.display()))?;
    let mut out = ui.stdout();
    write!(out, "Cloned hive ")?;
    write!(out.labeled("hive"), "{}", info.name)?;
    writeln!(out, " into {}", destination.display())?;
    drop(out);
    if let Err(err) = check_out_trunk(&located) {
        writeln!(ui.warning(), "Couldn't check out `trunk()` ({err:#}).")?;
        writeln!(ui.hint(), "`jj new 'trunk()'` checks it out.")?;
    }
    Ok(())
}

/// `jj git init` adopts an existing Git repository and its files, which a clone must not share.
fn check_clone_destination(destination: &Path) -> anyhow::Result<()> {
    match std::fs::read_dir(destination) {
        Ok(mut entries) => anyhow::ensure!(
            entries.next().transpose()?.is_none(),
            "destination {} is not empty; choose a new or empty directory",
            destination.display()
        ),
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => {}
        Err(err) => {
            return Err(err)
                .with_context(|| format!("checking destination {}", destination.display()));
        }
    }
    Ok(())
}

/// Checks out `trunk()` using this machine's jj config in the new copy: a new
/// working-copy commit on it, unless it is the root.
fn check_out_trunk(located: &Located) -> anyhow::Result<()> {
    let jj = |args: &[&str]| {
        let mut jj = Process::new("jj");
        musubi_jj::git_command::without_repository_env(&mut jj);
        jj.args(args).current_dir(&located.workspace_root);
        jj
    };
    let output = jj(&[
        "log",
        // An id, not the colour codes `ui.color = "always"` would wrap it in.
        "--color=never",
        "--ignore-working-copy",
        "--no-graph",
        "-n1",
        "-r",
        "trunk() ~ root()",
        "-T",
        "commit_id",
    ])
    .output()
    .context("running `jj log`")?;
    anyhow::ensure!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr).trim()
    );
    let trunk = String::from_utf8_lossy(&output.stdout);
    // jj prints the id alone today; a newline from a later jj mustn't reach `jj new`.
    let trunk = trunk.trim();
    if trunk.is_empty() {
        return Ok(());
    }
    // jj says where the working copy is now, as `jj git clone` does.
    let status = jj(&["new", trunk]).status().context("running `jj new`")?;
    anyhow::ensure!(status.success(), "`jj new {trunk}` failed");
    Ok(())
}
