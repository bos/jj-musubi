//! Transport- and storage-independent core of the jj-musubi sync protocol.
//!
//! The protocol is specified in docs/protocol.md and modeled in Lean in `formal/`;
//! docs/conformance.md describes how this crate is checked against that model.

pub mod hub;
pub mod message;
pub mod node;
