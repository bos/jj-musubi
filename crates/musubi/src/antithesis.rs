//! The Antithesis build (antithesis/README.md): the SDK, coverage instrumentation, and an
//! assertion that musubi never panics.

use antithesis_instrumentation as _;

/// Starts the SDK and asserts, on any panic, that none happens. A panic inside `musubi_jj`'s
/// `catch_jj_panic` doesn't reach this hook, which that wraps; it asserts there instead that
/// the panic is jj's known one.
pub fn init() {
    antithesis_sdk::antithesis_init();
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        let message = info
            .payload()
            .downcast_ref::<&str>()
            .map(|s| (*s).to_owned())
            .or_else(|| info.payload().downcast_ref::<String>().cloned())
            .unwrap_or_default();
        let details = serde_json::json!({
            "message": message,
            "location": info.location().map(ToString::to_string),
            "args": std::env::args_os()
                .map(|arg| arg.to_string_lossy().into_owned())
                .collect::<Vec<_>>(),
        });
        antithesis_sdk::assert_unreachable!("musubi never panics", &details);
        previous(info);
    }));
}
