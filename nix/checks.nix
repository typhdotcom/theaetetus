# Lints report and fail; they never edit the tree, so a false positive costs
# an argument rather than deleted code.
{ self, ... }:
{
  perSystem =
    { pkgs, ... }:
    let
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
        statix = lint "statix" "${pkgs.statix}/bin/statix check ${self}";
        deadnix = lint "deadnix" "${pkgs.deadnix}/bin/deadnix --fail ${self}";
        gitleaks = lint "gitleaks" "${pkgs.gitleaks}/bin/gitleaks dir --no-banner --redact ${self}";

        # `-exec ... +` does not run at all when nothing matches, so a project with
        # no shell scripts passes rather than erroring on an empty argument list.
        #
        # .envrc is excluded by omission: it is direnv's file, not a standalone
        # script, so it has no shebang and SC2148 would fail every project. shfmt
        # still formats it -- layout is safe to touch where lint advice is not.
        shellcheck = lint "shellcheck" ''
          cd ${self}
          ${pkgs.findutils}/bin/find . -type f \( -name '*.sh' -o -name '*.bash' \) \
            -exec ${pkgs.shellcheck}/bin/shellcheck {} +
        '';

        # Skipping absent directories keeps find from erroring under `set -e`,
        # which matters because most projects have no workflows at all.
        actionlint = lint "actionlint" ''
          cd ${self}
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
          cd ${self}
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
