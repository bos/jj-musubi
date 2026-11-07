//! Creating, joining, and cloning hives, and starting their first sync.

use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command as Process;
use std::time::Duration;

use anyhow::Context as _;
use jj_cli::formatter::FormatterExt as _;
use jj_lib::config::ConfigLayer;
use jj_lib::config::ConfigSource;
use jj_lib::object_id::ObjectId as _;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::settings::UserSettings;
use jj_lib::workspace::Workspace;
use musubi_hub::hub_dir::JoinChoice;
use musubi_hub::hub_dir::JoinRequest;
use musubi_hub::hub_dir::Joined;
use musubi_jj::node::NodeRepo;
use musubi_jj::objects::Backend;
use musubi_jj::presence::BadForgetAfter;
use musubi_jj::workspaces::Machine;
use musubi_sync::wire::HubWideReply;
use musubi_sync::wire::HubWideRequest;
use pollster::FutureExt as _;

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
        lease,
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
    let settings = settings::load(&located.workspace_root, &located.repo_path)?;
    validate_forget_after(settings.config(), *lease, &located.workspace_root)?;
    if lease.is_some()
        && let Some(key) = found.key.as_deref()
    {
        let serving = serving_workspace(&located, key)?;
        if !copy::same_directory(&serving, &located.workspace_root) {
            validate_forget_after(
                settings::load(&serving, &located.repo_path)?.config(),
                *lease,
                &serving,
            )?;
        }
    }
    // Kept only once the hub takes the join: a join refused, or failing, before then leaves
    // `--machine` free to name it next time.
    let machine = joining_machine(&located, machine, &settings)?;
    let node = located.open_as(&settings, machine.clone())?;
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
        machine: machine.key().to_owned(),
    };
    drop(node);
    let joined = match block_on(ask_preparing(ui, &hub, HubWideRequest::Join(request)))? {
        HubWideReply::Joined(joined) => joined,
        other => anyhow::bail!("unexpected reply from the hub: {other:?}"),
    };
    // The hub took this machine's key: it is the repository's from now on.
    NodeRepo::keep_machine(&located.repo_path, &machine)?;
    become_node(
        &located,
        &joined,
        &hub,
        full_history,
        found.record.as_ref(),
        &remotes,
        *lease,
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

/// The machine the repository at `located` joins a hive as: the one its key names, which
/// `name`, if given, must name, since its key has been part of a hive; else a new one, named
/// `name` or after the host, whose key [`become_node`] keeps.
fn joining_machine(
    located: &Located,
    name: Option<&str>,
    settings: &UserSettings,
) -> anyhow::Result<Machine> {
    let Some(machine) = NodeRepo::machine_of(&located.repo_path)? else {
        let name = name.unwrap_or_else(|| settings.operation_hostname());
        return Ok(NodeRepo::new_machine(name, settings));
    };
    if let Some(name) = name {
        anyhow::ensure!(
            machine.name() == musubi_jj::workspaces::sanitize(name),
            "this repository's machine is already named {}",
            machine.name()
        );
    }
    Ok(machine)
}

/// Records that the repository, with its machine key, is part of the hive it `joined`: the
/// join operation (unless replicating full history), its record, and its entry, for the
/// daemon to serve it. A copy whose record named another hive, `before`, forgets the copies its
/// history brings that the hive doesn't have. The first hub joined becomes the user's default.
fn become_node(
    located: &Located,
    joined: &Joined,
    hub: &str,
    full_history: bool,
    before: Option<&HiveConfig>,
    remotes: &musubi_jj::remote_url::JoinRemotes,
    lease: Option<Duration>,
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
    let path = serving_workspace(located, &key)?;
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
    set_forget_after(located, lease)?;
    UserState::save_default_hub(hub)?;
    Ok(())
}

/// Rejoining through another workspace keeps the workspace the daemon already serves.
/// Lease preflight must inspect the same config that daemon will read.
fn serving_workspace(located: &Located, key: &str) -> anyhow::Result<PathBuf> {
    Ok(UserState::load()?
        .entry(key)
        .filter(|entry| {
            Located::find(&entry.path)
                .is_ok_and(|other| copy::same_directory(&other.repo_path, &located.repo_path))
        })
        .map_or_else(
            || located.workspace_root.clone(),
            |entry| entry.path.clone(),
        ))
}

/// A repo lease cannot override a higher-priority policy in workspace config. Refuse that
/// conflict before joining, rather than report success with a different effective lease.
fn validate_forget_after(
    config: &jj_lib::config::StackedConfig,
    lease: Option<Duration>,
    workspace: &Path,
) -> anyhow::Result<()> {
    if let Some((source, configured)) = configured_forget_after(config)?
        && let Some(lease) = lease
    {
        anyhow::ensure!(
            source <= ConfigSource::Repo || configured == Some(lease),
            "musubi.forget-after in {source} config for {} overrides --lease; unset it and run \
             this again",
            workspace.display()
        );
    }
    Ok(())
}

/// An explicit lease sets this copy's inactivity timeout. Otherwise, keep jj's configured
/// policy, or record `never` when no policy is configured. Who runs the command is irrelevant.
fn set_forget_after(located: &Located, lease: Option<Duration>) -> anyhow::Result<()> {
    let settings = settings::load(&located.workspace_root, &located.repo_path)?;
    if lease.is_none() && configured_forget_after(settings.config())?.is_some() {
        return Ok(());
    }
    let name: jj_lib::config::ConfigNamePathBuf = musubi_jj::node::FORGET_AFTER_KEY.parse()?;
    let value = musubi_jj::presence::format_forget_after(lease);
    let path = settings::repo_config_path(&located.repo_path)?
        .context("this repository has no config of its own")?;
    let mut file = jj_lib::config::ConfigFile::load_or_empty(ConfigSource::Repo, &path)?;
    file.set_value(&name, value)?;
    file.save()?;
    Ok(())
}

/// `musubi.forget-after` as `config` sets it, and where: `None` if nothing does. Fails if
/// its value is neither `never` nor a duration, before a command joining a copy writes
/// anything.
fn configured_forget_after(
    config: &jj_lib::config::StackedConfig,
) -> anyhow::Result<Option<(ConfigSource, Option<Duration>)>> {
    let key = musubi_jj::node::FORGET_AFTER_KEY;
    let name: jj_lib::config::ConfigNamePathBuf = key.parse()?;
    let Some((source, value)) = config
        .layers()
        .iter()
        .rev()
        .filter(|layer| layer.source != ConfigSource::Default)
        .find_map(|layer| {
            let item = layer.look_up_item(&name).ok()??;
            Some((layer.source, item.as_str().map(str::to_owned)))
        })
    else {
        return Ok(None);
    };
    let after = value
        .as_deref()
        .map_or(
            Err(BadForgetAfter::NotADuration),
            musubi_jj::presence::parse_forget_after,
        )
        .map_err(|why| {
            anyhow::anyhow!("{key} in your {source} config {why}; fix it and run this again")
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
    lease: Option<Duration>,
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
    let remotes = if matches!(info.backend, Backend::Git(_)) {
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
    // All preflight checks have passed. Make the empty destination too, so jj's conditional
    // scopes see its actual path, including symlink ancestors and relative `..` components.
    std::fs::create_dir_all(destination)
        .with_context(|| format!("making {}", destination.display()))?;
    let workspace = destination.canonicalize()?;
    let repo_path = workspace.join(".jj/repo");
    let destination_settings = settings::load(&workspace, &repo_path)?;
    validate_forget_after(destination_settings.config(), lease, &workspace)?;
    let defaults = clone_config::missing(destination_settings.config(), &info.clone_config)?;
    // The defaults count for the initial working-copy commit too, as `jj --config` would.
    let mut overrides = ConfigLayer::empty(ConfigSource::CommandArg);
    for (name, value) in defaults {
        overrides.set_value(&name, value)?;
    }
    let settings = settings::load_with(&workspace, &repo_path, Some(overrides))?;
    // Contacting the hub may have taken long enough for another process to fill it.
    check_clone_destination(destination)?;
    init_copy(&settings, &workspace, info.backend)
        .with_context(|| format!("making a repository in {}", destination.display()))?;
    let located = Located::find(destination)?;
    clone_config::seed(&located.workspace_root, &info.clone_config)?;
    let machine = joining_machine(&located, machine, &settings)?;
    let joined = Joined {
        hive: info.clone(),
        created: false,
        reason: String::new(),
        present: vec![],
    };
    NodeRepo::keep_machine(&located.repo_path, &machine)?;
    become_node(&located, &joined, &hub, false, None, &remotes, lease)?;
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

/// Makes an empty repository with `backend` at `workspace`, an empty directory, as `jj git
/// init --colocate` or `jj debug init-simple` would, but with the hive's hash rather than
/// whichever `git.object-hash` sets: a copy's commits must be named as the hive's are.
fn init_copy(settings: &UserSettings, workspace: &Path, backend: Backend) -> anyhow::Result<()> {
    let name = WorkspaceName::DEFAULT;
    match backend {
        Backend::Git(hash) => {
            Workspace::init_colocated_git(settings, workspace, name, hash.kind()).block_on()?;
            // As jj does, so that git ignores jj's directory in a colocated workspace.
            let ignore = workspace.join(".jj/.gitignore");
            std::fs::write(&ignore, "/*\n")
                .with_context(|| format!("writing {}", ignore.display()))?;
        }
        Backend::Simple => {
            Workspace::init_simple(settings, workspace, name).block_on()?;
        }
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
