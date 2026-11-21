{
  # nixpkgs (and crane) no longer support x86_64-darwin.
  systems = [
    "x86_64-linux"
    "aarch64-linux"
    "aarch64-darwin"
  ];
}
