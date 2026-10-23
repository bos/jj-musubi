//! What the hub's machine says before the hub greets: waiting for the greeting never
//! panics, and it is found only at the end of a line, within what may come before it.

#![no_main]

use libfuzzer_sys::fuzz_target;
use musubi_transport::stream::GREETING;
use musubi_transport::stream::MAX_BEFORE_GREETING;
use musubi_transport::stream::await_greeting;
use pollster::FutureExt as _;

fuzz_target!(|data: &[u8]| {
    let mut rest = data;
    let greeted = await_greeting(&mut rest).block_on();
    if data.starts_with(GREETING) {
        assert!(greeted.is_ok());
    }
    if greeted.is_ok() {
        let read = &data[..data.len() - rest.len()];
        assert!(read.ends_with(GREETING));
        assert!(read.len() <= MAX_BEFORE_GREETING + GREETING.len());
    }
});
