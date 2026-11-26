{
  self,
  inputs,
  ...
}: {
  # Adds pkgs.jj-musubi, built against the consumer's nixpkgs (`final`) rather than
  # this flake's, so it shares their toolchain and libraries.
  flake.overlays.default = final: _prev: {
    jj-musubi = final.callPackage ../package.nix {
      craneLib = inputs.crane.mkLib final;
      rev = self.shortRev or self.dirtyShortRev or null;
      lastModifiedDate = self.lastModifiedDate or null;
    };
  };
}
