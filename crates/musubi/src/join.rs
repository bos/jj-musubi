//! Creating, joining, and cloning hives, and starting their first sync.

mod fetch;

use std::io::Write as _;
use std::path::Component;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command as Process;
use std::time::Duration;

use anyhow::Context as _;
use jj_cli::formatter::FormatterExt as _;
use jj_lib::config::ConfigLayer;
use jj_lib::config::ConfigSource;
use jj_lib::object_id::ObjectId as _;
use jj_lib::ref_name::RefName;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::settings::UserSettings;
use jj_lib::workspace::Workspace;
use musubi_hub::hub_dir::HiveId;
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
use crate::control::Cancelled;
use crate::copy;
#[cfg(test)]
use crate::copy::conformance::detach::{Write, after};
use crate::daemon;
use crate::daemon::Status;
use crate::hub;
use crate::interrupt::Interrupts;
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
        fresh,
        hub,
        lease,
    } = member;
    let (hub, machine, full_history, fresh) =
        (hub.as_deref(), machine.as_deref(), *full_history, *fresh);
    let machine_flag = machine;
    // Before anything is written.
    configured_machine_name(machine)?;
    let located = Located::find(start)?;
    copy::check_owner(&located.repo_path)?;
    located.refuse_slashed_workspaces(false)?;
    // From before it looks at what the repository is until it has recorded what it became.
    let joining = HiveConfig::join_lock(ui, &located.repo_path)?;
    let found = copy::Found::resolve(&located)?;
    let state = UserState::load()?;
    let entry = found.key.as_deref().and_then(|key| state.entry(key));
    let standing = copy::standing_of(&located, &found, entry);
    // `musubi join` in a repository that is part of a hive joins that hive again, made again
    // if its hub has lost it.
    let rejoin = |record: &HiveConfig| -> anyhow::Result<(JoinChoice, String)> {
        let remake = JoinChoice::Remake {
            id: HiveId::from(record.hive),
            name: record.name.clone(),
        };
        let hub = hub.map_or_else(|| Ok(record.hub.clone()), |hub| UserState::hub(Some(hub)))?;
        Ok((remake, hub))
    };
    // Its history is the hive's while it is part of one.
    if fresh
        && standing == copy::Standing::Copy
        && let Some(record) = &found.record
    {
        anyhow::bail!(
            "this repository is part of hive {}; `musubi leave` it first",
            record.display_name()
        );
    }
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
    // A record that says the repository left is as none: it joins as a repository part of no
    // hive does, taking up its key again (docs/internals/copies.md, R6).
    let before = found
        .record
        .as_ref()
        .filter(|record| record.state != Membership::Left);
    // Compatibility until 2027-02-25: see `NodeRepo::refuse_retired_keys`. `--fresh` removes
    // what it refuses for, with the history it drops.
    if !fresh {
        NodeRepo::refuse_retired_keys(&located.repo_path)?;
    }
    let (before, dropped) = if fresh {
        start_over(&located, before, found.record.is_none(), entry)?
    } else {
        (before, None)
    };
    discard_history_if(&located, fresh)?;
    // Kept only once the hub takes the join: a join refused, or failing, before then leaves
    // `--machine` free to name it next time.
    let machine = joining_machine(&located, machine, &settings, dropped.as_ref())?;
    let node = located.open_as(&settings, machine.clone())?;
    let summary = node.join_summary()?;
    // What the join carries into the hive, unless it is a hive this history came from.
    let shared = node.shared_history()?;
    let mut remotes = summary.remote_snapshot();
    if let JoinChoice::Remake { id, .. } = &choice {
        node.check_recorded_remote_bindings(id.as_str(), &mut remotes)?;
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
            .repository_root()
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
    // An interrupt from here on stops the first sync, and takes the repository back out of
    // the hive. Only for one that had no record of a hive, or one that says it left: stopping
    // marks the record left, which for one joined or removed would lose what it said.
    let stoppable = before.is_none().then(Stoppable::catch);
    // The hub took this machine's key: it is the repository's from now on.
    keep_join_key(&located, &machine)?;
    remember_machine_name(ui, machine_flag)?;
    become_node(
        &located,
        &joined,
        &hub,
        full_history,
        before,
        &remotes,
        *lease,
    )?;
    drop(joining);
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
    if let Some(shared) = shared.filter(|shared| !shared.hives.contains(joined.hive.id.as_str())) {
        let count = shared.operations;
        let operations = if count == 1 {
            "1 operation".to_owned()
        } else {
            format!("{count} operations")
        };
        writeln!(
            ui.warning(),
            "Sending hive {name} the {operations} of history this repository shared before."
        )?;
        if joined.created && !remaking {
            let name = crate::ui::shell_word(name);
            writeln!(
                ui.hint(),
                "To start the hive without them, run `musubi leave`, `musubi hub remove \
                 --immediately {name}` and `musubi create --fresh {name}`."
            )?;
        } else {
            writeln!(
                ui.hint(),
                "`musubi join --fresh` joins a hive without such history."
            )?;
        }
    }
    start_serving(ui, &located, socket, stoppable)?;
    fetch_join_conflicts(ui, &located, socket)
}

/// Readies the repository at `located` for a `--fresh` join, which drops the history its key
/// worked in, and the key with it ([`discard_history_if`]), so that the hub takes a new one, as
/// for a repository that never joined a hive: takes it out of a hive the hub removed,
/// `before`, as `musubi leave` would, and drops this machine's entry for its key. Returns the
/// record that is left of `before`, and the key, which the new one mustn't be. `unrecorded` is
/// whether the repository had no record, and `entry` this machine's entry for its key.
pub(crate) fn start_over<'a>(
    located: &Located,
    before: Option<&'a HiveConfig>,
    unrecorded: bool,
    entry: Option<&Entry>,
) -> anyhow::Result<(Option<&'a HiveConfig>, Option<Machine>)> {
    let before = match before {
        Some(record) if record.state == Membership::Removed => {
            crate::leave::detach(located, None)?;
            None
        }
        before => before,
    };
    let Some(old) = NodeRepo::machine_of(&located.repo_path)? else {
        return Ok((before, None));
    };
    // Not a key this machine syncs another repository with, as one made from this one's
    // files; this one's own entry, from a join stopped before its record, goes, as does one
    // whose repository is gone.
    let elsewhere = entry.is_some_and(|entry| {
        Located::find(&entry.path)
            .is_ok_and(|other| !copy::same_directory(&other.repo_path, &located.repo_path))
    });
    if unrecorded && elsewhere {
        anyhow::bail!(
            "{}",
            copy::not_the_copy(copy::Standing::Duplicate, None, entry)
        );
    }
    let _lock = HiveConfig::lock(&located.repo_path)?;
    if UserState::load()?.entry(old.key()).is_some() {
        UserState::remove_entry(old.key())?;
        #[cfg(test)]
        after(Write::DropEntry);
    }
    Ok((before, Some(old)))
}

/// If `fresh`, drops the history the repository at `located`, part of no hive, shared with
/// hives before, and its key, so that it joins as a repository that never was part of one.
/// Either way, finishes such a discard that stopped partway, which would otherwise leave the
/// join to carry what was left.
pub(crate) fn discard_history_if(located: &Located, fresh: bool) -> anyhow::Result<()> {
    if fresh || NodeRepo::discarding_shared_history(&located.repo_path) {
        NodeRepo::discard_shared_history(&located.repo_path, |_step| {
            #[cfg(test)]
            after(Write::Discard(_step));
        })?;
    }
    Ok(())
}

/// Independent snapshots may describe different observations of rewritten Git history.
/// Native jj merging already takes forward moves from either copy. For the remaining
/// ambiguity, obtain a fresh observation rather than ranking machines or commit times.
fn fetch_join_conflicts(ui: &Ui, located: &Located, socket: &Socket) -> anyhow::Result<()> {
    let mut node = located.open()?;
    let remotes = node.conflicted_git_bookmarks()?;
    if remotes.is_empty() {
        return Ok(());
    }
    let workspace = node
        .colocated_workspace()
        .map_or_else(|| located.workspace_root.clone(), Path::to_owned);
    drop(node);
    for (remote, bookmarks) in &remotes {
        let mut jj = Process::new("jj");
        musubi_jj::git_command::without_repository_env(&mut jj);
        // Use a verified colocated workspace, if one exists, so native jj takes musubi's
        // Git import/export lock. The primary workspace need not be colocated.
        jj.current_dir(&workspace).args([
            // Joining can leave the checkout stale. Fetch only recorded repository state,
            // preserving the caller's files, including edits not yet snapshotted by jj.
            "--ignore-working-copy",
            "git",
            "fetch",
            "--remote",
            &exact_pattern(remote),
        ]);
        // Override fetch filters only for the conflicted bookmarks. Both flags accept jj
        // string expressions, so stored names must be encoded as exact literal patterns.
        for bookmark in bookmarks {
            jj.args(["--branch", &exact_pattern(bookmark)]);
        }
        // The expected trunk warning disappears when the fetch resolves the bookmark.
        // If it cannot, the warning below gives a retry that selects the affected refs.
        let result = ui.while_blocked(&format!("Fetching from {remote}"), || {
            block_on(async { Ok(fetch::run(jj, Duration::from_secs(30)).await?) })
        });
        if let Err(err) = result
            && err
                .downcast_ref::<std::io::Error>()
                .is_some_and(|err| err.kind() == std::io::ErrorKind::Interrupted)
        {
            return Err(err).context("fetch interrupted; the copy remains joined");
        }
    }
    // A failed native call can retain completed effects. Unless interrupted, sync after
    // failed attempts too, and inspect the resulting state rather than promising resolution.
    crate::sync::sync(ui, &located.workspace_root, socket)?;
    for remote in located.open()?.conflicted_git_bookmarks()?.into_keys() {
        writeln!(
            ui.warning(),
            "Remote bookmarks for {remote} remain conflicted after joining."
        )?;
        writeln!(
            ui.hint(),
            "Run `musubi join` again on a machine with access to that remote."
        )?;
    }
    Ok(())
}

fn exact_pattern(name: &str) -> String {
    format!("exact:{}", RefName::new(name).as_symbol())
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
/// `name`, or as `musubi.machine-name` sets, or after the host, with a key other than
/// `avoiding`'s, which [`keep_join_key`] keeps once the hub accepts the join. `name` must be `musubi.machine-name`, where that is
/// set: the setting names the machine in every repository on it.
pub(crate) fn joining_machine(
    located: &Located,
    name: Option<&str>,
    settings: &UserSettings,
    avoiding: Option<&Machine>,
) -> anyhow::Result<Machine> {
    let configured = configured_machine_name(name)?;
    let Some(machine) = NodeRepo::machine_of(&located.repo_path)? else {
        let name = name
            .or(configured.as_deref())
            .unwrap_or_else(|| settings.operation_hostname());
        return Ok(NodeRepo::new_machine(
            name,
            settings,
            avoiding.map(Machine::key),
        ));
    };
    // Its key names it, until the setting renames it.
    let current = configured.unwrap_or_else(|| machine.name().to_owned());
    if let Some(name) = name
        && current != musubi_jj::workspaces::sanitize(name)
    {
        return Err(renaming_hint(
            anyhow::anyhow!("this repository's machine is named {current}"),
            name,
        ));
    }
    Ok(machine)
}

/// This machine's name as `musubi.machine-name` sets it in its jj config, refusing `--machine`,
/// `given`, if that sets another.
pub(crate) fn configured_machine_name(given: Option<&str>) -> anyhow::Result<Option<String>> {
    let configured = musubi_jj::node::configured_machine_name(&settings::user_config()?);
    if let (Some(given), Some(configured)) = (given, &configured)
        && musubi_jj::workspaces::sanitize(given) != *configured
    {
        return Err(renaming_hint(
            anyhow::anyhow!("this machine is named {configured}"),
            given,
        ));
    }
    Ok(configured)
}

/// `err`, with a hint to rename this machine `name`, which takes a setting, not `--machine`.
fn renaming_hint(err: anyhow::Error, name: &str) -> anyhow::Error {
    crate::ui::with_hint(
        err,
        format!(
            "`jj config set --user {} {}` renames this machine in all its repos at their next sync",
            musubi_jj::node::MACHINE_NAME_KEY,
            crate::ui::shell_word(name)
        ),
    )
}

/// Sets `musubi.machine-name` to `--machine`, `given`, where nothing sets it yet, so that
/// this machine's other repositories, and those it joins later, have the name too. The join
/// has happened by now, so a failure is a warning.
pub(crate) fn remember_machine_name(ui: &Ui, given: Option<&str>) -> anyhow::Result<()> {
    let Some(given) = given else {
        return Ok(());
    };
    let set = || -> anyhow::Result<()> {
        if musubi_jj::node::configured_machine_name(&settings::user_config()?).is_none() {
            settings::set_user_config(musubi_jj::node::MACHINE_NAME_KEY, given)?;
        }
        Ok(())
    };
    if let Err(err) = set() {
        let key = musubi_jj::node::MACHINE_NAME_KEY;
        writeln!(ui.warning(), "Couldn't set {key} ({err:#}).")?;
        writeln!(
            ui.hint(),
            "`jj config set --user {key} {}` gives this machine the name in its other repos.",
            crate::ui::shell_word(given)
        )?;
    }
    Ok(())
}

/// Keeps the machine key accepted by the hub, so retry uses it until membership is saved.
pub(crate) fn keep_join_key(located: &Located, machine: &Machine) -> anyhow::Result<()> {
    NodeRepo::keep_machine(&located.repo_path, machine)?;
    #[cfg(test)]
    after(Write::KeepKey);
    Ok(())
}

/// Records that the repository, with its machine key, is part of the hive it `joined`: the
/// join operation (unless replicating full history), its record, and its entry, for the
/// daemon to serve it. A copy whose record named another hive, `before`, forgets the copies its
/// history brings that the hive doesn't have. The first hub joined becomes the user's default.
pub(crate) fn become_node(
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
        .as_str()
        .parse()
        .context("the hub sent a malformed hive id")?;
    let mut node = located.open()?;
    let machine = node.machine().name().to_owned();
    let key = node.machine().key().to_owned();
    let description = format!("musubi: {machine} joins the hive");
    if full_history {
        node.mark_joined_with_remotes(&description, joined.hive.id.as_str(), remotes)?;
    } else {
        node.create_join_operation_with_remotes(&description, joined.hive.id.as_str(), remotes)?;
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
    // By the workspace the repository was made in, whichever this is, as another may go
    // away; or by the path it joined through already, if that reaches this repository, as a
    // bind mount does.
    let path = serving_workspace(located, &key)?;
    // The entry first: a record that names a config id no entry here does would make this
    // repository look like a duplicate, if what follows failed.
    UserState::put_entry(Entry {
        key,
        hive: hive_id,
        config_id: config_id.clone(),
        path,
    })?;
    #[cfg(test)]
    after(Write::PutEntry);
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
    #[cfg(test)]
    after(Write::JoinRecord);
    set_forget_after(located, lease)?;
    UserState::save_default_hub(hub)?;
    Ok(())
}

/// The workspace the daemon serves this repository through: the one it already serves, if
/// that reaches this repository, else the workspace the repository was made in, whichever
/// this is, as another may go away. Lease preflight must inspect the same config that daemon
/// will read.
fn serving_workspace(located: &Located, key: &str) -> anyhow::Result<PathBuf> {
    Ok(UserState::load()?
        .entry(key)
        .filter(|entry| {
            Located::find(&entry.path)
                .is_ok_and(|other| copy::same_directory(&other.repo_path, &located.repo_path))
        })
        .map_or_else(|| located.repository_root(), |entry| entry.path.clone()))
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
/// That a repository's first sync is to be stoppable: by an interrupt from now on, if they
/// can be caught, and by the command going away, however it ends.
pub(crate) struct Stoppable(Option<Interrupts>);

impl Stoppable {
    /// Catches interrupts from now on: one before the daemon is asked to sync stops the sync
    /// as soon as it is asked.
    pub(crate) fn catch() -> Self {
        Self(Interrupts::catch().ok())
    }
}

/// Has the daemon, started if need be, serve the repository, and reports its first sync.
/// Without a daemon, syncs once. If `stoppable`, stopping the command while the daemon syncs
/// stops the sync, unless the copy has begun applying the hive's history, and the copy leaves
/// its hive.
fn start_serving(
    ui: &Ui,
    located: &Located,
    socket: &Socket,
    stoppable: Option<Stoppable>,
) -> anyhow::Result<()> {
    /// How asking the daemon to serve the repository went.
    enum Served {
        /// There was no daemon to ask, nor could one be started.
        NoDaemon(anyhow::Error),
        Synced,
        /// The daemon serves it, but its first sync failed, saying this.
        Failed(String),
        /// Interrupted before the daemon was asked to serve the copy; with why no running
        /// daemon could be asked, if one couldn't.
        Unasked(Option<anyhow::Error>),
        /// Interrupted: how stopping the sync went.
        Interrupted(anyhow::Result<Cancelled>),
    }
    let key = copy::Found::read(&located.repo_path)?
        .key
        .context("this repository has no machine key")?;
    // Read now, as stopping the first sync drops it.
    let hive =
        HiveConfig::load(&located.repo_path)?.context("this repository is not part of a hive")?;
    // The client lives on the runtime that made it, so one runtime does it all.
    let served = block_on(async {
        // Interrupted already, as while this command recorded the join. No daemon was asked to
        // serve the copy; but one running may serve it all the same, as one that took up its
        // entry: that one is asked, and stopped at once, so that it says whether it has
        // applied any of the hive's history. With none running, nothing syncs it.
        let early = pending(stoppable.as_ref());
        let client = if early {
            match daemon::running(socket).await {
                Ok(Some(client)) => client,
                Ok(None) => return Ok(Served::Unasked(None)),
                Err(err) => return Ok(Served::Unasked(Some(err))),
            }
        } else {
            match daemon::ensure(socket).await {
                Ok(client) => client,
                Err(err) => return Ok(Served::NoDaemon(err)),
            }
        };
        let progress = daemon_progress(&client, &key);
        let Some(Stoppable(interrupts)) = &stoppable else {
            let add = client.add(key.clone(), control::SYNC_LIMIT);
            let first = ui.while_waiting(add, progress).await;
            return Ok(
                match first.context("asking the daemon to serve this repository")? {
                    Ok(_) => Served::Synced,
                    Err(message) => Served::Failed(message),
                },
            );
        };
        // Names this `Join` to the `Cancel` that may follow it.
        let token = uuid::Uuid::new_v4().simple().to_string();
        // On a task of its own, so that it is sent even if an interrupt comes first, as the
        // `Cancel` waits for it. Longer than the connection waits for a request, so that the
        // daemon, not this command, gives up first: this command ending would stop the sync.
        let join = tokio::spawn({
            let (client, key, token) = (client.clone(), key.clone(), token.clone());
            let limit = control::SYNC_LIMIT + Duration::from_secs(60);
            async move { client.join(key, token, limit).await }
        });
        let mut join = std::pin::pin!(async { join.await? });
        let first = tokio::select! {
            biased;
            first = ui.while_waiting(&mut join, progress) => first,
            () = interrupted_or(early, interrupts.as_ref()) => {
                // As long as the daemon takes to get to where it can stop: the end of what it
                // is importing, say. Another interrupt stops this command waiting, as does the
                // `Join` failing, which the `Cancel` would wait for.
                let cancel = client.cancel(key.clone(), token, control::SYNC_LIMIT);
                let cancel = ui.while_doing("Stopping the first sync", cancel);
                let mut cancel = std::pin::pin!(cancel);
                let mut answered = None;
                let stopped = loop {
                    tokio::select! {
                        stopped = &mut cancel => {
                            break stopped.and_then(|stopped| stopped.map_err(anyhow::Error::msg));
                        }
                        first = &mut join, if answered.is_none() => match first {
                            Ok(first) => answered = Some(first),
                            Err(err) => break Err(err),
                        },
                        () = interrupted(interrupts.as_ref()) => {
                            break Err(anyhow::anyhow!("interrupted again before it had stopped"));
                        }
                    }
                };
                match (stopped, answered) {
                    // The sync had answered: as if not interrupted.
                    (Ok(Cancelled::Answered), Some(first)) => Ok(first),
                    (Ok(Cancelled::Answered), None) => join.await,
                    (stopped, _) => return Ok(Served::Interrupted(stopped)),
                }
            }
        };
        Ok::<_, anyhow::Error>(
            match first.context("asking the daemon to serve this repository")? {
                Ok(_) => Served::Synced,
                Err(message) => Served::Failed(message),
            },
        )
    })?;
    match served {
        // Interrupted while the daemon wouldn't start: as before it was asked.
        Served::Unasked(err) => {
            if let Some(err) = err {
                writeln!(ui.warning(), "Couldn't reach the daemon ({err:#}).")?;
            }
            Err(stopped_before_asking(ui, located, &hive)?)
        }
        Served::NoDaemon(_) if pending(stoppable.as_ref()) => {
            Err(stopped_before_asking(ui, located, &hive)?)
        }
        Served::NoDaemon(err) => {
            // An interrupt stops this sync, here, as it stops the command.
            drop(stoppable);
            writeln!(
                ui.warning(),
                "Could not start the daemon ({err:#}); syncing once instead."
            )?;
            sync_directly(ui, located)?;
            writeln!(ui.hint(), "Run `musubi daemon` to keep it in sync.")?;
            Ok(())
        }
        Served::Synced => Ok(()),
        Served::Interrupted(stopped) => Err(interrupted_error(ui, located, &hive, stopped)?),
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

/// Takes the repository at `located` out of its hive, which no daemon was asked to sync it
/// in, as the command was interrupted first, and says so.
fn stopped_before_asking(
    ui: &Ui,
    located: &Located,
    hive: &HiveConfig,
) -> anyhow::Result<anyhow::Error> {
    daemon::unjoin(located, hive)?;
    interrupted_error(ui, located, hive, Ok(Cancelled::Stopped))
}

/// What a command interrupted during the first sync of the repository at `located` in `hive`
/// fails with, as stopping it went.
fn interrupted_error(
    ui: &Ui,
    located: &Located,
    hive: &HiveConfig,
    stopped: anyhow::Result<Cancelled>,
) -> anyhow::Result<anyhow::Error> {
    ui.interrupted();
    let name = hive.display_name();
    // Where to run what the hint says, as after `musubi clone`, if not here.
    let here = std::env::current_dir()
        .and_then(dunce::canonicalize)
        .is_ok_and(|cwd| cwd.starts_with(&located.workspace_root));
    let there = |hint: String| {
        if here {
            hint
        } else {
            format!("In {}, {hint}", located.workspace_root.display())
        }
    };
    Ok(match stopped {
        Ok(Cancelled::Stopped) => crate::ui::with_hint(
            anyhow::anyhow!(
                "stopped the first sync; this repository is no longer part of hive {name}"
            ),
            there(format!(
                "`musubi join --hive {}` joins it again.",
                crate::ui::shell_word(&name)
            )),
        ),
        Ok(Cancelled::TooLate | Cancelled::Answered) => crate::ui::with_hint(
            anyhow::anyhow!(
                "too late to stop the first sync: hive {name}'s history is already going \
                         into this repository"
            ),
            there("`musubi leave` takes it out of the hive once it has synced.".to_owned()),
        ),
        Err(err) => crate::ui::with_hint(
            anyhow::anyhow!("couldn't stop the first sync: {err:#}"),
            there("`musubi status` shows whether it is still part of the hive.".to_owned()),
        ),
    })
}

/// Whether an interrupt came, and hasn't been acted on.
fn pending(stoppable: Option<&Stoppable>) -> bool {
    use futures::FutureExt as _;
    stoppable
        .and_then(|Stoppable(interrupts)| interrupts.as_ref())
        .is_some_and(|interrupts| interrupts.next().now_or_never().is_some())
}

/// Resolves at once if `already` interrupted, else as [`interrupted`].
async fn interrupted_or(already: bool, interrupts: Option<&Interrupts>) {
    if !already {
        interrupted(interrupts).await;
    }
}

/// Resolves at the next interrupt, if they're caught; else never, as one ends the command.
async fn interrupted(interrupts: Option<&Interrupts>) {
    match interrupts {
        Some(interrupts) => interrupts.next().await,
        None => std::future::pending().await,
    }
}

pub fn clone(
    ui: &Ui,
    destination: Option<&Path>,
    hive: &str,
    hub: Option<&str>,
    machine: Option<&str>,
    lease: Option<Duration>,
    socket: &Socket,
) -> anyhow::Result<()> {
    if let Some(destination) = destination {
        check_clone_destination(destination)?;
    }
    configured_machine_name(machine)?;
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
    // Named after the hive the hub resolved, not the prefix or id that chose it.
    let default;
    let destination = match destination {
        Some(destination) => destination,
        None => {
            let hint = format!(
                "`musubi clone {} <dir>` clones into a directory you name",
                crate::ui::shell_word(hive)
            );
            default = default_destination(&info.name).ok_or_else(|| {
                crate::ui::with_hint(
                    anyhow::anyhow!("can't name a directory after hive {:?}", info.name),
                    hint.clone(),
                )
            })?;
            check_clone_destination(&default).map_err(|err| crate::ui::with_hint(err, hint))?;
            &default
        }
    };
    let remotes = if matches!(info.backend, Backend::Git(_)) {
        musubi_jj::inherited_remotes::read(&destination.join(".git"))
            .map_err(|err| anyhow::anyhow!("could not read inherited Git configuration: {err}"))?
    } else {
        musubi_jj::remote_url::JoinRemotes::default()
    };
    let resolved_id = info.id;
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
        info.id == resolved_id,
        "the hub returned a different hive during clone; run `musubi clone` again"
    );
    clone_config::missing(&jj_lib::config::StackedConfig::empty(), &info.clone_config)?;
    // All preflight checks have passed. Make the empty destination too, so jj's conditional
    // scopes see its actual path, including symlink ancestors and relative `..` components.
    std::fs::create_dir_all(destination)
        .with_context(|| format!("making {}", destination.display()))?;
    let workspace = dunce::canonicalize(destination)?;
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
    let machine_flag = machine;
    let machine = joining_machine(&located, machine, &settings, None)?;
    let joined = Joined {
        hive: info.clone(),
        created: false,
        reason: String::new(),
        present: vec![],
    };
    let stoppable = Stoppable::catch();
    keep_join_key(&located, &machine)?;
    remember_machine_name(ui, machine_flag)?;
    become_node(&located, &joined, &hub, false, None, &remotes, lease)?;
    start_serving(ui, &located, socket, Some(stoppable))
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

/// The directory a clone of hive `name` makes when given none: the last part of the name, as
/// `jj git clone` names it after the last part of the URL. A `\` separates parts too, on every
/// platform, so that a name gives the same directory everywhere, and never a subdirectory on
/// Windows.
fn default_destination(name: &str) -> Option<PathBuf> {
    let part = name.rsplit(['/', '\\']).find(|part| !part.is_empty());
    // Not `.`, `..`, or, on Windows, a drive such as `C:`.
    match part.map(Path::new) {
        Some(path)
            if matches!(
                path.components().collect::<Vec<_>>()[..],
                [Component::Normal(_)]
            ) =>
        {
            Some(path.to_owned())
        }
        _ => None,
    }
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

#[cfg(test)]
mod tests {
    use super::default_destination;

    #[test]
    fn a_clone_is_named_after_the_last_part_of_its_hive() {
        let named = default_destination;
        let some = |dir: &str| Some(dir.into());
        assert_eq!(named("dotfiles"), some("dotfiles"));
        assert_eq!(named("bos/dotfiles"), some("dotfiles"));
        assert_eq!(named("github.com/bos/dotfiles/"), some("dotfiles"));
        assert_eq!(named(r"bos\dotfiles"), some("dotfiles"));
        for unnamed in [".", "..", "bos/..", "/"] {
            assert_eq!(named(unnamed), None, "{unnamed}");
        }
    }
}
