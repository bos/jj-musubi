//! Explicit syncs, through the daemon when possible, and their progress reports.

use std::io::Write as _;
use std::path::Path;
use std::time::Duration;

use anyhow::Context as _;
use musubi_sync::progress::Activity;
use musubi_sync::progress::Progress;
use musubi_sync::remote::HiveGone;

use crate::block_on;
use crate::config::HiveConfig;
use crate::config::Membership;
use crate::control;
use crate::control::ControlClient;
use crate::control::Synced;
use crate::daemon;
use crate::repo::Located;
use crate::repo::the_copy;
use crate::socket::Socket;
use crate::ui::Ui;

fn counted(count: usize, noun: &str) -> String {
    format!("{count} {noun}{}", if count == 1 { "" } else { "s" })
}

/// Inspection, scoped approval, and selected snapshot cleanup with an optional dry run.
pub fn publication(
    ui: &Ui,
    start: &Path,
    socket: &Socket,
    approve: Option<&str>,
    prune: &[String],
    dry_run: bool,
) -> anyhow::Result<()> {
    let (located, _, _) = the_copy(ui, start, socket)?;
    // An older daemon does not honor the guard or publication lock.
    block_on(daemon::running(socket))?;
    let lock = musubi_jj::node::publication_lock(&located.repo_path)?;
    let mut node = located.open()?;
    let mut cache = musubi_jj::node::PublicationCache::default();
    if !prune.is_empty() {
        if !dry_run {
            let requested = node.preview_publication_cleanup(prune, &mut cache)?;
            // jj records its arguments on every snapshot. A unique, command-only config
            // argument identifies this invocation without selecting concurrent snapshots.
            let invocation = uuid::Uuid::new_v4().simple().to_string();
            let marker = format!("--config=musubi.prune-snapshot={invocation}");
            // Record current edits and deletions before planning cleanup. Never let stale
            // recovery update files implicitly; the workspace checks below still apply.
            let mut jj = std::process::Command::new("jj");
            musubi_jj::git_command::without_repository_env(&mut jj);
            let output = jj
                .args([
                    "--color=never",
                    "--config=snapshot.auto-update-stale=false",
                    &marker,
                    "util",
                    "snapshot",
                ])
                .current_dir(&located.workspace_root)
                .output()
                .context("running `jj util snapshot` before pruning")?;
            if !output.status.success() {
                let stderr = String::from_utf8_lossy(&output.stderr);
                let message = stderr.trim();
                if message.is_empty() {
                    anyhow::bail!("`jj util snapshot` failed: {}", output.status);
                }
                // musubi adds its own error heading; retain jj's message and recovery hint.
                anyhow::bail!("{}", message.strip_prefix("Error: ").unwrap_or(message));
            }
            node = located.open()?;
            cache = musubi_jj::node::PublicationCache::default();
            // Keep the resolved operation identities if native work changes prefixes meanwhile.
            let mut selected = requested.selected.clone();
            selected.extend(node.publication_snapshots_from(&invocation)?);
            let plan = node.preview_publication_cleanup(&selected, &mut cache)?;
            node.apply_publication_cleanup(&selected, &plan.token, &mut cache)?;
            let count = requested.selected.len();
            writeln!(
                ui.stderr(),
                "Discarded {}; current work is unchanged.",
                counted(count, "unpublished operation")
            )?;
        } else {
            let plan = node.preview_publication_cleanup(prune, &mut cache)?;
            let mut out = ui.stdout();
            writeln!(
                out,
                "Discard {}.",
                counted(plan.selected.len(), "unpublished operation")
            )?;
            writeln!(
                out,
                "Keep all current commits, bookmarks, workspaces and files."
            )?;
            writeln!(
                out,
                "Earlier versions of uncommitted files may become unrecoverable."
            )?;
            writeln!(
                out,
                "Snapshot content: {}, {} bytes -> {}, {} bytes.",
                counted(plan.before.files.len(), "file"),
                plan.before.bytes,
                counted(plan.after.files.len(), "file"),
                plan.after.bytes
            )?;
            if plan.after.held() {
                writeln!(
                    out,
                    "The remaining snapshot content would still exceed the budget."
                )?;
            }
        }
        return Ok(());
    }
    let report = node.outgoing_publication(&mut cache)?;
    if let Some(token) = approve {
        anyhow::ensure!(
            musubi_jj::node::approve_publication(&located.repo_path, &report, token)?,
            "outgoing work changed; run `musubi sync --outgoing` before approving it"
        );
        drop(lock);
        return sync(ui, start, socket);
    }
    let mut out = ui.stdout();
    let approved = musubi_jj::node::publication_approved(&located.repo_path, &report);
    let state = if report.held() && approved {
        "Approved for sending"
    } else if report.held() {
        "Sending held"
    } else {
        "Within publication budget"
    };
    writeln!(
        out,
        "{state}: snapshots retain {}, {} bytes beyond intentional history.",
        counted(report.files.len(), "file"),
        report.bytes
    )?;
    if report.files.is_empty() {
        return Ok(());
    }
    writeln!(
        out,
        "Limits: {} files, {} bytes (0 disables a limit).",
        report.limits.files, report.limits.bytes
    )?;
    writeln!(
        out,
        "\nFiles (versions shared by operations are counted once):"
    )?;
    for file in &report.files {
        writeln!(
            out,
            "  {}  {} bytes, {}",
            file.path.escape_debug(),
            file.bytes,
            counted(file.versions, "version")
        )?;
    }
    writeln!(out, "\nRetaining operations (their byte counts overlap):")?;
    for operation in &report.operations {
        writeln!(
            out,
            "  {}  {}, {} bytes  {}",
            operation.id,
            counted(operation.files, "file"),
            operation.bytes,
            operation.description.escape_debug()
        )?;
    }
    if !approved {
        writeln!(
            out,
            "\nSend this work: musubi sync --approve {}",
            report.token
        )?;
    }
    if report.cleanup_available {
        writeln!(
            out,
            "Preview cleanup: musubi sync --prune <operation>... --dry-run"
        )?;
    } else {
        writeln!(
            out,
            "Cleanup unavailable: jj did not record enough information to preserve an earlier command's changes."
        )?;
    }
    Ok(())
}

/// Syncs once, in this process.
pub fn sync_directly(ui: &Ui, located: &Located) -> anyhow::Result<Synced> {
    let hive =
        HiveConfig::load(&located.repo_path)?.context("this repository is not part of a hive")?;
    let progress = Progress::default();
    let sync = daemon::sync_once(located, &hive, &progress);
    block_on(ui.while_waiting(sync, || async { Some(progress.get()) }))
}

/// Syncs through the daemon when it serves the repository, else directly.
pub fn sync(ui: &Ui, start: &Path, socket: &Socket) -> anyhow::Result<()> {
    let (_, stopped) = sync_quietly(ui, start, socket)?;
    if stopped {
        writeln!(
            ui.warning(),
            "The daemon isn't running, so this synced in its own process, and nothing keeps \
             this repository in sync."
        )?;
        writeln!(ui.hint(), "`musubi daemon start` starts it.")?;
    }
    Ok(())
}

/// [`sync`], saying nothing, and whether it synced here because the daemon that would serve
/// the repository isn't running.
pub fn sync_quietly(ui: &Ui, start: &Path, socket: &Socket) -> anyhow::Result<(Synced, bool)> {
    let (located, hive, entry) = the_copy(ui, start, socket)?;
    let mut stopped = false;
    let through_daemon = block_on(async {
        let Some(client) = daemon::running(socket).await? else {
            stopped = true;
            return Ok(None);
        };
        let sync = client.sync(
            control::context(Duration::from_secs(3600)),
            entry.key.clone(),
        );
        let synced = ui
            .while_waiting(sync, daemon_progress(&client, &entry.key))
            .await?;
        Ok::<_, anyhow::Error>(Some(synced))
    })?;
    let synced = match through_daemon {
        Some(Ok(synced)) => synced,
        Some(Err(message)) => anyhow::bail!("{message}"),
        None => match sync_directly(ui, &located) {
            Ok(synced) => synced,
            // As the daemon would: the hive is over.
            Err(err) if HiveGone::of(&err) == Some(HiveGone::Removed) => {
                daemon::leave_hive(&located, &hive, Membership::Removed)?;
                anyhow::bail!(
                    "{err:#}, so this repository no longer syncs with it; everything it has stays"
                );
            }
            Err(err) => return Err(err),
        },
    };
    Ok((synced, stopped))
}
/// Asks the daemon what its sync of `key`'s copy is doing, each time it is called.
pub fn daemon_progress(
    client: &ControlClient,
    key: &str,
) -> impl FnMut() -> std::pin::Pin<Box<dyn Future<Output = Option<Activity>>>> {
    let (client, key) = (client.clone(), key.to_owned());
    move || {
        let (client, key) = (client.clone(), key.clone());
        Box::pin(async move {
            let context = control::context(Duration::from_secs(1));
            client.progress(context, key).await.ok().flatten()
        })
    }
}
