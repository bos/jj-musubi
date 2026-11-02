# Releasing

A release is a tag on main, a GitHub release with a build for each platform, and the crates
on crates.io, all at one version.

## Prepare the version

1. Check that `CHANGELOG.md`'s Unreleased section says what the release breaks and what a
   user must do on upgrading ([AGENTS.md, "Compatibility"](../../AGENTS.md#compatibility)).
2. If anything machines and hubs must agree on changed since the latest `v*` tag (`jj tag
   list`), check that `PROTOCOL_VERSION` changed too, so that machines and hubs of the two
   releases refuse each other, saying so.
3. In `Cargo.toml`, set the workspace's `version` and the exact versions (`=0.1.0`) its
   crates require of each other, and run `cargo update --workspace` to put it in `Cargo.lock`.
   The version must be above the one the workspace gives now, which every build deployed
   from source since the last release follows, so that machines on those builds take the
   release as newer. Until 1.0, a release that changes `PROTOCOL_VERSION`, or breaks anything
   else, bumps the minor version (0.1.x to 0.2.0), and any other release the patch version.
   Where `CHANGELOG.md` or the guides name the coming release, give them this version.
4. Rename the Unreleased heading in `CHANGELOG.md`, if there is one, to the version.
5. Run `just check`, and land the change on main. Until the tag is pushed, don't deploy main
   (`upgrade-from-source --deploy`): a build deployed from it would be newer than the release.

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
token (`cargo login`). A published version can't be replaced, only yanked:

```sh
jj new v0.1.0
cargo publish --workspace --locked
```
