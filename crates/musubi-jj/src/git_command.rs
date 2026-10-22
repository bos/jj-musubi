//! The `git` binary as musubi runs it, for a git repository's objects and its remotes.

use std::io;
use std::io::Read as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::ExitStatus;
use std::process::Stdio;
use std::thread;

use thiserror::Error;

/// The variables git sets, for what it runs in a repository such as a hook, to name that
/// repository: the ones `git rev-parse --local-env-vars` lists. No git musubi runs gets
/// them, nor does a daemon a command starts, which serves every repository on the machine;
/// musubi run from a hook would otherwise hand them on.
pub const REPOSITORY_ENV: &[&str] = &[
    "GIT_ALTERNATE_OBJECT_DIRECTORIES",
    "GIT_CONFIG",
    "GIT_CONFIG_PARAMETERS",
    "GIT_CONFIG_COUNT",
    "GIT_OBJECT_DIRECTORY",
    "GIT_DIR",
    "GIT_WORK_TREE",
    "GIT_IMPLICIT_WORK_TREE",
    "GIT_GRAFT_FILE",
    "GIT_INDEX_FILE",
    "GIT_NO_REPLACE_OBJECTS",
    "GIT_REPLACE_REF_BASE",
    "GIT_PREFIX",
    "GIT_SHALLOW_FILE",
    "GIT_COMMON_DIR",
];

#[derive(Debug, Error)]
pub enum GitError {
    #[error("failed to run git {args}")]
    Run { args: String, source: io::Error },
    #[error("git {args} failed: {stderr}")]
    Failed { args: String, stderr: String },
}

/// The git at `executable` as musubi runs it: without [`REPOSITORY_ENV`], running no hooks,
/// and, where git knows `GIT_NO_LAZY_FETCH`, fetching nothing. jj runs no hooks when it
/// writes to `.git`; musubi's `update-ref` and `git remote` would run the repository's
/// `reference-transaction`, and its `gc --auto` `pre-auto-gc`. In a partial clone, which
/// musubi refuses ([`Incompleteness`]), git would fetch what it lacks from the promisor
/// remote.
///
/// [`Incompleteness`]: crate::objects::Incompleteness
pub(crate) fn git(executable: &Path) -> Command {
    let mut command = Command::new(executable);
    without_repository_env(&mut command);
    command.env("GIT_NO_LAZY_FETCH", "1");
    // A path under which no hook can exist.
    command.args(["-c", "core.hooksPath=/dev/null"]);
    command
}

/// Keeps `command` from [`REPOSITORY_ENV`], which would name the repository of whatever ran
/// musubi.
pub fn without_repository_env(command: &mut Command) {
    for name in REPOSITORY_ENV {
        command.env_remove(name);
    }
}

/// The empty tree's id, which git knows without storing it.
const EMPTY_TREE: &str = "4b825dc642cb6eb9a060e54bf8d69288fbee4904";

/// A git repository, driven through the git binary at `executable`.
pub(crate) struct GitRepo {
    executable: PathBuf,
    git_dir: PathBuf,
}

impl GitRepo {
    /// `git_dir` is the `.git` directory, or the repository itself if it is bare.
    pub fn new(executable: &Path, git_dir: &Path) -> Self {
        Self {
            executable: executable.to_owned(),
            git_dir: git_dir.to_owned(),
        }
    }

    pub fn executable(&self) -> &Path {
        &self.executable
    }

    pub fn git_dir(&self) -> &Path {
        &self.git_dir
    }

    /// `git args` in this repository, ready to run.
    pub fn command(&self, args: &[&str]) -> Command {
        let mut command = git(&self.executable);
        // Running inside the repository as well as naming it keeps a mistake from ever
        // touching the caller's working directory.
        command
            .current_dir(&self.git_dir)
            .env("GIT_DIR", &self.git_dir)
            // git 2.43 to 2.45 read a bare repository's attributes from HEAD's tree, and
            // `pack-objects` asks for each path's. Where HEAD names a branch that doesn't
            // exist, as in a hub's repository or a non-colocated jj repository's, every
            // ask tried each way of spelling HEAD as a ref, and failed: a million file
            // lookups for a clone of jj, three times as long as the packing itself. Run here,
            // git has no attributes to read anyway (a colocated `.git` is no working tree),
            // so name the empty tree. Other gits ignore the setting, or use no tree in a bare
            // repository already.
            .args(["-c", &format!("attr.tree={EMPTY_TREE}")])
            .args(args);
        command
    }

    /// Runs `git args` in this repository with `input` on its stdin, and returns its
    /// stdout.
    pub fn run(&self, args: &[&str], input: Option<Vec<u8>>) -> Result<Vec<u8>, GitError> {
        let mut out = vec![];
        self.stream(args, io::Cursor::new(input.unwrap_or_default()), &mut out)?;
        Ok(out)
    }

    /// Runs `git args` in this repository, copying `input` to its stdin, and its stdout to
    /// `out`, as it goes: a pack needn't fit in memory.
    pub fn stream(
        &self,
        args: &[&str],
        mut input: impl io::Read + Send + 'static,
        out: &mut dyn io::Write,
    ) -> Result<(), GitError> {
        let mut child = self
            .command(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|source| run_err(args, source))?;
        let mut stdin = child.stdin.take().expect("stdin is piped");
        let writer = thread::spawn(move || io::copy(&mut input, &mut stdin));
        let mut stderr = child.stderr.take().expect("stderr is piped");
        let errors = thread::spawn(move || {
            let mut bytes = vec![];
            stderr.read_to_end(&mut bytes).map(|_| bytes)
        });
        let mut stdout = child.stdout.take().expect("stdout is piped");
        let copied = io::copy(&mut stdout, out);
        // Closed, so that git, if the copy failed, fails writing more rather than waiting.
        drop(stdout);
        let status = child.wait().map_err(|source| run_err(args, source))?;
        let written = writer.join().expect("stdin writer panicked");
        let stderr = errors.join().expect("stderr reader panicked");
        // The copy's error says why git failed, if it did.
        copied.map_err(|source| run_err(args, source))?;
        // A failing git may close stdin early; its exit status explains why.
        check_status(
            args,
            status,
            &stderr.map_err(|source| run_err(args, source))?,
        )?;
        written.map_err(|source| run_err(args, source))?;
        Ok(())
    }
}

pub(crate) fn run_err(args: &[&str], source: io::Error) -> GitError {
    GitError::Run {
        args: args.join(" "),
        source,
    }
}

pub(crate) fn check_status(
    args: &[&str],
    status: ExitStatus,
    stderr: &[u8],
) -> Result<(), GitError> {
    if status.success() {
        Ok(())
    } else {
        Err(GitError::Failed {
            args: args.join(" "),
            stderr: String::from_utf8_lossy(stderr).into_owned(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn attributes_come_from_the_empty_tree() {
        let command =
            GitRepo::new(Path::new("their-git"), Path::new("unused")).command(&["pack-objects"]);
        assert_eq!(command.get_program(), "their-git");
        let args: Vec<String> = command
            .get_args()
            .map(|arg| arg.to_string_lossy().into_owned())
            .collect();
        assert_eq!(
            args,
            [
                "-c",
                "core.hooksPath=/dev/null",
                "-c",
                &format!("attr.tree={EMPTY_TREE}"),
                "pack-objects"
            ]
        );
    }

    /// The list is git's own, so that a variable a newer git adds is noticed here.
    #[test]
    fn repository_env_is_what_git_lists() {
        let output = Command::new("git")
            .args(["rev-parse", "--local-env-vars"])
            .output()
            .unwrap();
        assert!(output.status.success());
        for name in String::from_utf8(output.stdout).unwrap().lines() {
            assert!(REPOSITORY_ENV.contains(&name), "{name} is missing");
        }
    }
}
