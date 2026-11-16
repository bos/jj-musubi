//! Cross-process publication exclusion and approval of one exact report token.
//!
//! Offered-history provenance lives in `offers`; approval only authorizes the content
//! represented by a report whose identity, basis, limits, operations, and bytes still match.

use std::fs;
use std::path::Path;

use super::PublicationReport;

pub const APPROVAL_FILE: &str = "publication-approval";

/// Shared by CLI approval/cleanup and every sender, held before any attachment upload.
pub fn publication_lock(repo: &Path) -> std::io::Result<fs::File> {
    let path = repo.join("musubi/publication.lock");
    let file = fs::OpenOptions::new()
        .create(true)
        .read(true)
        .write(true)
        .truncate(false)
        .open(path)?;
    file.lock()?;
    Ok(file)
}

pub fn approve_publication(
    repo: &Path,
    report: &PublicationReport,
    token: &str,
) -> std::io::Result<bool> {
    if token != report.token {
        return Ok(false);
    }
    crate::files::replace(&repo.join("musubi").join(APPROVAL_FILE), token.as_bytes())?;
    Ok(true)
}

pub fn publication_approved(repo: &Path, report: &PublicationReport) -> bool {
    fs::read_to_string(repo.join("musubi").join(APPROVAL_FILE))
        .is_ok_and(|token| token == report.token)
}
