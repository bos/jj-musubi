{
  perSystem = {
    pkgs,
    self',
    ...
  }: {
    devShells.default = pkgs.mkShell {
      # Pulls in cargo, rustc and all of the package's build dependencies.
      inputsFrom = [self'.packages.default];

      packages = with pkgs; [
        rust-analyzer
        clippy
        rustfmt
        cargo-nextest # the repo configures nextest in .config/nextest.toml
        just # the repo's task runner (justfile)
        git # the tests run git
      ];

      RUST_SRC_PATH = "${pkgs.rustPlatform.rustLibSrc}";
    };
  };
}
