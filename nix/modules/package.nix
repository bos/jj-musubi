{
  lib,
  self,
  inputs,
  ...
}: let
  # The root Cargo.toml is a workspace; the shared version lives in [workspace.package].
  cargoToml = lib.importTOML ../../Cargo.toml;
  version = cargoToml.workspace.package.version;

  fs = lib.fileset;

  # Everything except Nix files and build output. (crane's cleanCargoSource would be
  # tighter, but it drops non-Rust files the crates embed, such as
  # crates/musubi/src/defaults.toml.)
  src = fs.toSource {
    root = ../../.;
    fileset = fs.difference ../../. (
      fs.unions [
        ../../nix
        ../../flake.nix
        ../../default.nix
        ../../shell.nix
        (fs.maybeMissing ../../flake.lock)
        (fs.maybeMissing ../../target)
        (fs.maybeMissing ../../result)
      ]
    );
  };

  # crates/musubi-sync/build.rs appends MUSUBI_BUILD to the release as semver build
  # metadata (e.g. 0.47.1+20261102153012.4a0db20), so a daemon treats a newer build
  # from source as newer. Taken from the flake's git info when it's available.
  rev = self.shortRev or self.dirtyShortRev or null;
  musubiBuild =
    if rev != null && self ? lastModifiedDate
    then "${self.lastModifiedDate}.${rev}"
    else null;
in {
  perSystem = {
    pkgs,
    self',
    ...
  }: let
    craneLib = inputs.crane.mkLib pkgs;

    # Shared by the dependency build and the package build, so both compile the
    # same dependency graph with the same flags (otherwise cargo rebuilds them).
    commonArgs = {
      pname = "jj-musubi";
      inherit version src;
      strictDeps = true;

      # Build only the binary crate (crates/musubi) and what it depends on.
      cargoExtraArgs = "--locked --package jj-musubi";

      # The test suite drives real git and jj repositories and spawns daemons; run it
      # with `cargo nextest run` in the dev shell rather than inside the Nix sandbox.
      # Off here too, so the dependency build skips dev-dependencies.
      doCheck = false;
    };

    # Only the dependencies, built from Cargo.toml and Cargo.lock alone: this is
    # rebuilt when those change, not when the source does.
    cargoArtifacts = craneLib.buildDepsOnly commonArgs;
  in {
    packages.jj-musubi = craneLib.buildPackage (commonArgs
      // {
        inherit cargoArtifacts;

        # Only on the final package: setting it on the dependency build would
        # rebuild every dependency on every commit.
        env = lib.optionalAttrs (musubiBuild != null) {MUSUBI_BUILD = musubiBuild;};

        nativeBuildInputs = [pkgs.installShellFiles];

        # clap's dynamic completions: the same scripts the docs tell users to source.
        postInstall = lib.optionalString (pkgs.stdenv.buildPlatform.canExecute pkgs.stdenv.hostPlatform) ''
          installShellCompletion --cmd musubi \
            --bash <(COMPLETE=bash $out/bin/musubi) \
            --zsh <(COMPLETE=zsh $out/bin/musubi) \
            --fish <(COMPLETE=fish $out/bin/musubi)
        '';

        meta = {
          description = "Replicate jj repositories between machines";
          homepage = "https://www.serpentine.com/software/jj-musubi";
          changelog = "https://github.com/bos/jj-musubi/blob/main/CHANGELOG.md";
          license = lib.licenses.asl20;
          mainProgram = "musubi";
        };
      });

    packages.default = self'.packages.jj-musubi;
  };
}
