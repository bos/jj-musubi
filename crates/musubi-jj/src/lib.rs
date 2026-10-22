//! jj-lib integration for jj-musubi: canonical operations, translation, and objects.
//!
//! Internal to jj-musubi, with no stable API.

pub mod canonical;
pub mod format_guard;
pub mod git_command;
pub mod hive_settings;
pub mod merge;
pub mod node;
pub mod objects;
mod protobuf;
pub mod remote_url;
mod translation_map;
pub mod workspaces;
