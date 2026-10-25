//! How many files the daemon and the hub may have open.
//!
//! The daemon keeps several files, file-system watches and an ssh connection open for each
//! repository it serves, and the hub several files for each hive. Yet launchd starts a
//! program with a soft limit of 256 open files, which a daemon serving two dozen repositories
//! reached: every sync after failed, unable even to start ssh. The hard limit is far higher, so
//! both raise the soft one as they start.

/// Enough for some nine hundred repositories, yet no more than macOS takes (`OPEN_MAX` in
/// setrlimit(2)), nor than the ssh and git the daemon starts, which inherit it, expect.
#[cfg(unix)]
const ENOUGH: u64 = 10240;

/// Raises this process's soft limit on open files to [`ENOUGH`], or as far as its hard limit
/// allows.
#[cfg(unix)]
pub fn raise() {
    use rustix::process::Resource;
    use rustix::process::Rlimit;

    let limit = rustix::process::getrlimit(Resource::Nofile);
    // `None` is unlimited.
    let soft = limit.maximum.map_or(ENOUGH, |hard| hard.min(ENOUGH));
    if !limit.current.is_some_and(|current| current < soft) {
        return;
    }
    let raised = Rlimit {
        current: Some(soft),
        maximum: limit.maximum,
    };
    if let Err(err) = rustix::process::setrlimit(Resource::Nofile, raised) {
        tracing::warn!(
            "couldn't raise the limit on open files from {:?}: {err}",
            limit.current
        );
    }
}

#[cfg(not(unix))]
pub fn raise() {}

#[cfg(all(test, unix))]
mod tests {
    use rustix::process::Resource;
    use rustix::process::Rlimit;
    use rustix::process::getrlimit;
    use rustix::process::setrlimit;

    use super::*;

    /// As launchd starts the daemon: with a soft limit of 256.
    #[test]
    fn a_low_limit_on_open_files_is_raised() {
        let hard = getrlimit(Resource::Nofile).maximum;
        if hard.is_some_and(|hard| hard <= 256) {
            eprintln!("skipping: the hard limit on open files is {hard:?}, too low to raise");
            return;
        }
        setrlimit(
            Resource::Nofile,
            Rlimit {
                current: Some(256),
                maximum: hard,
            },
        )
        .unwrap();
        raise();
        let expected = hard.map_or(ENOUGH, |hard| hard.min(ENOUGH));
        assert_eq!(getrlimit(Resource::Nofile).current, Some(expected));
    }
}
