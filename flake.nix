{
  description = "jj-musubi: Keep jj repos in sync across your machines, live";

  inputs = {
    #nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    nixpkgs.url = "https://flakehub.com/f/DeterminateSystems/nixpkgs-weekly/0.1";

    flake-parts.url = "github:hercules-ci/flake-parts";
    flake-parts.inputs.nixpkgs-lib.follows = "nixpkgs";

    import-tree.url = "github:vic/import-tree";

    flake-compat.url = "github:NixOS/flake-compat";
    flake-compat.flake = false;
  };

  # Every .nix file under ./nix/modules is a flake-parts module (paths containing /_ are skipped).
  outputs = inputs: inputs.flake-parts.lib.mkFlake {inherit inputs;} (inputs.import-tree ./nix/modules);
}
