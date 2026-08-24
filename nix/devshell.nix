{
  perSystem =
    { pkgs, ... }:
    {
      devShells.default = pkgs.mkShell {
        # elan manages the Lean toolchain named in lean-toolchain; curl and
        # git are what it reaches for when fetching one.
        packages = [
          pkgs.curl
          pkgs.elan
          pkgs.git
          pkgs.nushell
        ];

        shellHook = ''
          export ELAN_HOME="''${ELAN_HOME:-$HOME/.elan}"
        '';
      };
    };
}
