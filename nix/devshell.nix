{
  perSystem =
    { pkgs, ... }:
    {
      devShells.default = pkgs.mkShell {
        # elan manages the Lean toolchain named in lean-toolchain; curl and
        # git are what it reaches for when fetching one. Sage and PARI are the
        # lattice tools for recon/: genus enumeration, isometry, short vectors.
        packages = [
          pkgs.curl
          pkgs.elan
          pkgs.git
          pkgs.nushell
          pkgs.pari
          pkgs.sage
        ];

        shellHook = ''
          export ELAN_HOME="''${ELAN_HOME:-$HOME/.elan}"
        '';
      };
    };
}
