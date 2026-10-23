//! What the fuzz targets share.

use std::path::Path;
use std::sync::OnceLock;

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
