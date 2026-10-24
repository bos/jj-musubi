//! The crate's integration tests, in one binary: each would otherwise be linked with
//! everything the crate depends on, again after every change to it.

mod format_guard_props;
mod git_executable;
mod join;
mod presence;
mod ref_laws;
mod translation;
mod workspace_merge;
