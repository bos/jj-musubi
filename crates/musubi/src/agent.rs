//! The ssh agent of a daemon that a command starts.
//!
//! Such a daemon outlives the command, and would keep its `SSH_AUTH_SOCK`, which goes stale
//! when the session it came from ends: an ssh login with a forwarded agent, say. Yet jj may
//! need the agent to sign the commits musubi rewrites with a key held there, and ssh may
//! need it to reach a hub through a `ProxyJump` host. So the daemon's `SSH_AUTH_SOCK` names
//! a link in the state directory instead, and every musubi command points the link at its
//! own agent, when that answers: the daemon uses the agent of the latest session to run
//! musubi, not just any that answers, which needn't hold the user's keys.
//!
//! The login service gives the daemon the link on Linux, where a user's service manager
//! rarely has an agent, and launchd's own on macOS. On Windows the agent is a pipe of fixed
//! name, so none of this applies.

use std::path::Path;
use std::path::PathBuf;

use crate::config;
use crate::socket::Socket;

/// The link a started daemon's `SSH_AUTH_SOCK` names, unless its path is too long to be a
/// socket's.
pub fn link() -> anyhow::Result<Option<PathBuf>> {
    if cfg!(windows) {
        return Ok(None);
    }
    let link = config::state_dir()?.join("ssh-agent");
    Ok(Socket::Path(link.clone())
        .too_long()
        .is_none()
        .then_some(link))
}

/// Points the link at this command's agent, if that answers.
pub fn refresh() -> anyhow::Result<()> {
    let (Some(link), Some(agent)) = (link()?, std::env::var_os("SSH_AUTH_SOCK")) else {
        return Ok(());
    };
    point(&link, Path::new(&agent))
}

#[cfg(unix)]
fn point(link: &Path, agent: &Path) -> anyhow::Result<()> {
    // No state directory yet means no daemon yet; starting one makes it, then comes here.
    let Some(dir) = link.parent().filter(|dir| dir.is_dir()) else {
        return Ok(());
    };
    // A child of the daemon can inherit this link as SSH_AUTH_SOCK, possibly through
    // another symlink. Store the resolved socket so a refresh cannot create a cycle,
    // even if another command replaces the link while this one is refreshing it.
    let Ok(target) = agent.canonicalize() else {
        return Ok(());
    };
    // Probe the supplied path: its resolved target can exceed Unix socket address limits.
    if link.canonicalize().is_ok_and(|current| current == target) || !live(agent) {
        return Ok(());
    }
    // Replaced in one step, so that nothing finds it missing.
    let temp = dir.join(format!(".ssh-agent.{}", std::process::id()));
    std::fs::remove_file(&temp).ok();
    std::os::unix::fs::symlink(&target, &temp)?;
    if let Err(err) = std::fs::rename(&temp, link) {
        std::fs::remove_file(&temp).ok();
        return Err(err.into());
    }
    Ok(())
}

#[cfg(windows)]
fn point(_: &Path, _: &Path) -> anyhow::Result<()> {
    Ok(())
}

/// Whether an agent answers at `socket`.
#[cfg(unix)]
fn live(socket: &Path) -> bool {
    std::os::unix::net::UnixStream::connect(socket).is_ok()
}

#[cfg(all(test, unix))]
mod tests {
    use std::os::unix::net::UnixListener;

    use super::*;

    #[test]
    fn the_link_follows_the_latest_agent_that_answers() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().canonicalize().unwrap();
        let link = root.join("ssh-agent");
        let first = root.join("first.sock");
        let second = root.join("second.sock");
        let first_agent = UnixListener::bind(&first).unwrap();
        let _second_agent = UnixListener::bind(&second).unwrap();

        point(&link, &first).unwrap();
        assert_eq!(std::fs::read_link(&link).unwrap(), first);
        point(&link, &second).unwrap();
        assert_eq!(std::fs::read_link(&link).unwrap(), second);
        // A command can inherit the daemon's agent path, directly or through another
        // symlink. Refreshing it must keep the live socket rather than introduce a cycle.
        let alias = dir.path().join("agent-alias");
        std::os::unix::fs::symlink(&link, &alias).unwrap();
        for agent in [&link, &alias] {
            point(&link, agent).unwrap();
            assert_eq!(std::fs::read_link(&link).unwrap(), second);
        }
        // A short alias can reach a socket whose resolved path exceeds sockaddr_un.
        // The daemon's short link can point there too, but the probe needs the alias.
        let long = root.join("long-agent-directory".repeat(8));
        std::fs::create_dir(&long).unwrap();
        let short = root.join("s");
        std::os::unix::fs::symlink(&long, &short).unwrap();
        let socket = short.join("agent.sock");
        let _long_agent = UnixListener::bind(&socket).unwrap();
        point(&link, &socket).unwrap();
        assert_eq!(std::fs::read_link(&link).unwrap(), long.join("agent.sock"));
        assert!(live(&link));
        point(&link, &second).unwrap();
        // An agent that doesn't answer replaces nothing.
        drop(first_agent);
        point(&link, &first).unwrap();
        assert_eq!(std::fs::read_link(&link).unwrap(), second);
        point(&link, &dir.path().join("gone.sock")).unwrap();
        assert_eq!(std::fs::read_link(&link).unwrap(), second);
    }

    #[test]
    fn nothing_happens_without_a_state_directory() {
        let dir = tempfile::tempdir().unwrap();
        let agent = dir.path().join("agent.sock");
        let _agent = UnixListener::bind(&agent).unwrap();
        let link = dir.path().join("missing/ssh-agent");
        point(&link, &agent).unwrap();
        assert!(!link.exists());
    }
}
