//! The crate's integration tests, in one binary: each would otherwise be linked with
//! everything the crate depends on, again after every change to it.

mod faults;
mod network;
mod serve;
mod server;
mod transfer;
