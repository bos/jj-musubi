#![no_main]

use libfuzzer_sys::fuzz_target;

#[path = "../../crates/musubi/src/tls/codec.rs"]
mod codec;

fuzz_target!(|data: &[u8]| codec::fuzz(data));
