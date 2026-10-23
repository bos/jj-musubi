# Releasing

A release is a tag on main, a GitHub release with a build for each platform, and the crates
on crates.io, all at one version.

## Prepare the version

1. Check what the release changes for users. `CHANGELOG.md`'s Unreleased section should say
   what breaks and what a user must do on upgrading (see the Compatibility section of
   [AGENTS.md](../../AGENTS.md#compatibility)).
2. If the wire format changed since the latest `v*` tag (`jj tag list`), check that
   `PROTOCOL_VERSION` changed too, so that machines and hubs of the two releases refuse each
   other, saying so.
3. Set the version in `Cargo.toml`, both the workspace's and the one its own crates require of
   each other (the `=0.1.0`s), and run `cargo update --workspace` to put it in `Cargo.lock`.
4. Make the Unreleased heading in `CHANGELOG.md` the version's, if there is one.
5. Run `just check`, and land the change on main.

## Tag and build

Push a tag matching the version:

```sh
jj tag set v0.1.0 -r main
jj git push --remote origin --tag v0.1.0
```

`.github/workflows/release.yml` checks that the tag matches the workspace's version, builds
`musubi` for Linux (static, x86_64 and aarch64), macOS (x86_64 and aarch64), and Windows
(x86_64 and aarch64), with build provenance attestations, and attaches the archives and
their checksums to a draft GitHub release.

Review the draft, put the version's section of `CHANGELOG.md` at the top of its notes, and
publish it. Running the workflow by hand from the Actions tab builds the same archives
without releasing anything.

## Publish the crates

Once the release has built, publish the crates from the tagged commit, with a crates.io
token (`cargo login`). Publishing can't be undone, only yanked:

```sh
jj new v0.1.0
cargo publish --workspace --locked
```
