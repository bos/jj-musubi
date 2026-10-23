//! Files replaced whole, as the crates write them (see "Resilience" in AGENTS.md).

use std::io;
use std::io::Write as _;
use std::path::Path;

/// Replaces `path` with `contents`, so that a reader finds the old contents or the new ones,
/// never part of either: through a temporary file in `dir`, on `path`'s filesystem, renamed
/// over it. Written through the temporary file's own handle: a file reopened by name,
/// truncating, ext4 writes out at once as it closes (see `BundleWriter::create`). It writes
/// out at once a file renamed over another too, so on a path that runs often, replace a file
/// only when its contents change. On Unix the temporary file is readable only by its owner,
/// which the rename keeps.
pub fn replace_through(dir: &Path, path: &Path, contents: &[u8]) -> io::Result<()> {
    let mut tmp = tempfile::NamedTempFile::new_in(dir)?;
    tmp.write_all(contents)?;
    tmp.persist(path).map_err(|err| err.error)?;
    Ok(())
}

/// [`replace_through`] a temporary file beside `path`.
pub fn replace(path: &Path, contents: &[u8]) -> io::Result<()> {
    let dir = path
        .parent()
        .filter(|dir| !dir.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    replace_through(dir, path, contents)
}
