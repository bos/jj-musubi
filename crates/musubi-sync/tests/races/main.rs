//! The race catalogue (docs/races.md): concurrent changes on different machines, each
//! provoked deliberately against real colocated repositories, synced through the real
//! protocol core and hub storage, and checked for the outcome jj itself would produce had
//! the changes come from concurrent processes on one machine.

#![allow(clippy::unwrap_used)]

mod fixture;

mod bookmarks;
mod changes;
mod config;
mod found;
mod history;
mod remotes;
mod workspaces;
