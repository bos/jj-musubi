{self, ...}: {
  perSystem = {
    pkgs,
    self',
    ...
  }: {
    # The overlay applied to this flake's nixpkgs, so there's one definition of how
    # jj-musubi is built.
    packages.jj-musubi = (pkgs.extend self.overlays.default).jj-musubi;
    packages.default = self'.packages.jj-musubi;
  };
}
