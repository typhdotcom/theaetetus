{
  description = "theaetetus";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
  };

  outputs =
    {
      self,
      nixpkgs,
      ...
    }:
    let
      inherit (nixpkgs) lib;
      forAllSystems = lib.genAttrs lib.systems.flakeExposed;
    in
    {
      packages = forAllSystems (
        system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in
        {
        }
      );

      nixosModules.default =
        { pkgs, ... }:
        {
          environment.systemPackages = [
          ];
        };

      devShells = forAllSystems (
        system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in
        {
          default = pkgs.mkShell {
            packages = [
              pkgs.nushell
              pkgs.elan
              pkgs.git
              pkgs.curl
            ];

            shellHook = ''
              export ELAN_HOME="''${ELAN_HOME:-$HOME/.elan}"
            '';
          };
        }
      );
    };
}
