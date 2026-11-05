# Lints report and fail; they never edit the tree, so a false positive costs
# an argument rather than deleted code.
{
  self,
  lib,
  config,
  ...
}:
let
  cfg = config.typh;
in
{
  options.typh = {
    ownedPaths = lib.mkOption {
      type = lib.types.nullOr (lib.types.listOf lib.types.str);
      default = null;
      description = ''
        Paths, relative to the flake root, that the lints and formatters
        cover. `null` covers the whole tree.
      '';
    };

    # A missing owned path fails evaluation here rather than silently
    # narrowing the check to nothing.
    checkRoot = lib.mkOption {
      type = lib.types.path;
      readOnly = true;
      default =
        if cfg.ownedPaths == null then
          self
        else
          lib.fileset.toSource {
            root = ../.;
            fileset = lib.fileset.unions (map (path: ../. + "/${path}") cfg.ownedPaths);
          };
    };
  };

  config.perSystem =
    { pkgs, ... }:
    let
      root = cfg.checkRoot;
      lint =
        name: command:
        pkgs.runCommand "lint-${name}" { } ''
          set -euo pipefail
          ${command}
          touch $out
        '';
    in
    {
      checks = {
        # statix looks for statix.toml from the -c path, defaulting to the cwd,
        # which in the sandbox is the build directory. Without -c a project's
        # statix.toml is silently ignored and every lint stays enabled.
        statix = lint "statix" "${pkgs.statix}/bin/statix check -c ${root} ${root}";
        deadnix = lint "deadnix" "${pkgs.deadnix}/bin/deadnix --fail ${root}";
        gitleaks = lint "gitleaks" "${pkgs.gitleaks}/bin/gitleaks dir --no-banner --redact ${root}";

        # `-exec ... +` does not run at all when nothing matches, so a project with
        # no shell scripts passes rather than erroring on an empty argument list.
        #
        # .envrc is excluded by omission: it is direnv's file, not a standalone
        # script, so it has no shebang and SC2148 would fail every project. shfmt
        # still formats it -- layout is safe to touch where lint advice is not.
        shellcheck = lint "shellcheck" ''
          cd ${root}
          ${pkgs.findutils}/bin/find . -type f \( -name '*.sh' -o -name '*.bash' \) \
            -exec ${pkgs.shellcheck}/bin/shellcheck {} +
        '';

        # Skipping absent directories keeps find from erroring under `set -e`,
        # which matters because most projects have no workflows at all.
        actionlint = lint "actionlint" ''
          cd ${root}
          for dir in .github/workflows .gitea/workflows .forgejo/workflows; do
            [ -d "$dir" ] || continue
            ${pkgs.findutils}/bin/find "$dir" -type f \( -name '*.yml' -o -name '*.yaml' \) \
              -exec ${pkgs.actionlint}/bin/actionlint {} +
          done
        '';

        # rg exits 1 for "no matches" and 2 for a real error, so the status is
        # matched explicitly rather than inverted -- otherwise a broken rg
        # invocation would read as a clean tree.
        markers = lint "markers" ''
          cd ${root}
          set +e
          found=$(${pkgs.ripgrep}/bin/rg \
            --line-number --no-heading --color never --hidden \
            --regexp '(TODO|FIXME):' .)
          status=$?
          set -e
          case $status in
            0)
              # nix keeps only the last log-lines (25 by default) of a failed
              # build, so the count goes last -- it survives truncation and says
              # whether the list above it is complete.
              printf '%s\n' "$found"
              printf '%s unresolved markers -- do what each asks, then delete it.\n' \
                "$(printf '%s\n' "$found" | wc -l)"
              exit 1
              ;;
            1) ;;
            *) exit $status ;;
          esac
        '';
      };
    };
}
