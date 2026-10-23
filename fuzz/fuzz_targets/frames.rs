//! Frames from a byte stream (`musubi_transport::stream`): reading never panics, and each
//! frame read encodes to exactly the bytes it was read from.

#![no_main]

use libfuzzer_sys::fuzz_target;
use musubi_transport::stream::fuzzing;
use pollster::FutureExt as _;

fuzz_target!(|data: &[u8]| {
    // Small enough that the fuzzer finds frames over it.
    fuzzing::frames(data, 1 << 12).block_on();
});
