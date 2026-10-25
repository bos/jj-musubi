//! The race catalogue (docs/internals/races.md): concurrent changes on different machines, each
//! provoked deliberately against real repositories, colocated unless a test says
//! otherwise, synced through the real protocol core and hub storage, and checked for the
//! outcome jj itself would produce had the changes come from concurrent processes on one
//! machine.

#![allow(clippy::unwrap_used)]

mod fixture;

mod bookmarks;
mod changes;
mod config;
mod expiry;
mod forget;
mod found;
mod history;
mod refs;
mod remotes;
mod repositories;
mod restore;
mod workspaces;
