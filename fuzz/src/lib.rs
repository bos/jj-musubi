//! What the fuzz targets share.

use std::panic;
use std::panic::AssertUnwindSafe;
use std::path::Path;
use std::sync::Once;
use std::sync::OnceLock;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;

use tempfile::TempDir;

/// A directory for one fuzzing process's files, in memory where Linux keeps one. libFuzzer
/// ends the process without dropping it, so it outlives the run, holding the last input's
/// files: each target writes over its own, rather than adding more.
pub fn scratch() -> &'static Path {
    static DIR: OnceLock<TempDir> = OnceLock::new();
    DIR.get_or_init(|| {
        let mut builder = tempfile::Builder::new();
        builder.prefix("musubi-fuzz-");
        let shm = Path::new("/dev/shm");
        if shm.is_dir() {
            builder.tempdir_in(shm)
        } else {
            builder.tempdir()
        }
        .expect("a scratch directory")
    })
    .path()
}

/// What `import` returns, or `None` if it panicked in jj-lib, or in jj-core, the crate jj-lib
/// is built on, which panic on some malformed input. A panic anywhere else, or in jj outside
/// `import`, is passed on to the fuzzer.
pub fn refusing_jj_lib_panics<T>(import: impl FnOnce() -> T) -> Option<T> {
    // Global rather than per thread: an import may verify views on threads of its own.
    static REFUSING: AtomicBool = AtomicBool::new(false);
    static HOOK: Once = Once::new();
    HOOK.call_once(|| {
        let fuzzer_hook = panic::take_hook();
        panic::set_hook(Box::new(move |info| {
            let refused = REFUSING.load(Ordering::Relaxed)
                && info.location().is_some_and(|at| in_jj(at.file()));
            if !refused {
                fuzzer_hook(info);
            }
        }));
    });
    REFUSING.store(true, Ordering::Relaxed);
    let imported = panic::catch_unwind(AssertUnwindSafe(import));
    REFUSING.store(false, Ordering::Relaxed);
    imported.ok()
}

/// Whether `file` is a source file of jj-lib or jj-core as cargo fetches them from
/// crates.io, under a directory named for the crate and its version. jj from a git or path
/// dependency isn't recognized, so its panics fail the target.
fn in_jj(file: &str) -> bool {
    file.split(['/', '\\']).any(|dir| {
        ["jj-lib-", "jj-core-"].iter().any(|name| {
            dir.strip_prefix(name)
                .is_some_and(|version| version.starts_with(|c: char| c.is_ascii_digit()))
        })
    })
}
