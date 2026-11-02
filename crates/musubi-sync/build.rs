//! Names this build of musubi for `wire::RELEASE`: its release, then, for a build deployed from
//! source, what `MUSUBI_BUILD` says, as semver build metadata. `contrib/upgrade-from-source`
//! sets it to when the build was deployed and its commit, as in
//! `0.3.0+20261102153012.4a0db205e1f0`, so that a daemon finds a build deployed later newer
//! (docs/guides/manage.md, "Deploy a build from source").

fn main() {
    println!("cargo::rerun-if-env-changed=MUSUBI_BUILD");
    let release = env!("CARGO_PKG_VERSION");
    let release = match std::env::var("MUSUBI_BUILD") {
        Ok(build) if !build.is_empty() => {
            // Anything else would make a release no daemon can read, and so never upgrade to.
            assert!(
                build.split('.').all(|identifier| {
                    !identifier.is_empty()
                        && identifier
                            .bytes()
                            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
                }),
                "MUSUBI_BUILD={build:?} isn't semver build metadata, such as \
                 20261102153012.4a0db205e1f0"
            );
            format!("{release}+{build}")
        }
        _ => release.to_owned(),
    };
    println!("cargo::rustc-env=MUSUBI_RELEASE={release}");
}
