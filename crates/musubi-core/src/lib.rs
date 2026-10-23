//! Transport- and storage-independent core of the jj-musubi sync protocol.
//!
//! Internal to jj-musubi, with no stable API.
//!
//! The protocol is specified in docs/internals/protocol.md and modeled in Lean in `formal/`;
//! docs/internals/conformance.md describes how this crate is checked against that model.

pub mod hub;
pub mod message;
pub mod node;
