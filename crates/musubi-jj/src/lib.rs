//! jj-lib integration for jj-musubi: canonical operations, translation, and objects.
//!
//! Internal to jj-musubi, with no stable API.

pub mod canonical;
pub mod files;
pub mod format_guard;
pub mod gc;
pub mod git_command;
pub mod hive_settings;
pub mod node;
pub mod objects;
pub mod presence;
mod protobuf;
pub mod remote_url;
mod translation_map;
pub mod workspaces;

/// The Lean model as an oracle, for tests checking code against it.
#[cfg(test)]
#[path = "../../musubi-core/tests/support/oracle.rs"]
#[allow(dead_code, clippy::unwrap_used)]
mod oracle;
