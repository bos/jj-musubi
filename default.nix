(import (
  let
    lock = builtins.fromJSON (builtins.readFile ./flake.lock);
    node = lock.nodes.${lock.nodes.root.inputs.flake-compat}.locked;
  in
    fetchTarball {
      url = node.url or "https://github.com/NixOS/flake-compat/archive/${node.rev}.tar.gz";
      sha256 = node.narHash;
    }
) {src = ./.;}).defaultNix
