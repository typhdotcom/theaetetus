# treefmt owns everything that rewrites files. Only enable formatters whose
# edits are semantics-preserving -- `nix fmt` applies them silently.
#
# Enabling a formatter for a language no project uses costs nothing: treefmt
# matches on filename, so an unused one never runs. The list is therefore
# aspirational rather than a description of what exists today.
{
  inputs,
  lib,
  config,
  ...
}:
let
  inherit (config.typh) ownedPaths checkRoot;
in
{
  perSystem =
    { pkgs, ... }:
    let
      treefmt = inputs.treefmt-nix.lib.evalModule pkgs {
        projectRootFile = "flake.nix";

        # Files a tool generates and rewrites in its own layout have one
        # legitimate writer, and it is not treefmt: formatting them means the
        # two fight on every regeneration, breaking the formatting check.
        # Global rather than per-formatter so the protection outlives
        # formatter changes. Most lockfiles (flake.lock, Cargo.lock, ...) are
        # already safe -- nothing claims the .lock extension; listed here are
        # the generated files a formatter would claim.
        settings.global.excludes = [
          # recon/data is written by the recon scripts at json.dumps(indent=2),
          # which always expands arrays; prettier collapses the short ones.
          "recon/data/*.json"

          ".copier-answers.yml" # copier
          "Manifest.toml" # julia
          "lake-manifest.json"
          "package-lock.json"
          "pnpm-lock.yaml"
          "*.min.js"
          "*.min.css"
        ];

        # Neither treefmt-nix nor nixpkgs packages a Julia formatter. Runic is
        # the configless one, as gofmt is for go; JuliaFormatter has style
        # knobs and a history of breaking changes between majors.
        settings.formatter.runic = {
          command = "${pkgs.julia.withPackages [ "Runic" ]}/bin/julia";
          options = [
            "-m"
            "Runic"
            "--inplace"
          ];
          includes = [ "*.jl" ];
        };

        programs = {
          nixfmt.enable = true;

          # Bare mdformat destroys frontmatter: the fence becomes a horizontal rule
          # and the keys become a heading. Agent-facing markdown is all frontmatter,
          # so the plugin is load-bearing rather than a nicety. It covers TOML as
          # well as YAML, at the cost of dropping TOML comments.
          #
          # `number` keeps ordered lists counting; without it every item is
          # rewritten to "1.", which reads badly in files consumed as raw text.
          mdformat = {
            enable = true;
            plugins = ps: [ ps.mdformat-front-matters ];
            settings.number = true;
          };

          ruff-format.enable = true; # python
          rustfmt.enable = true; # rust
          gofmt.enable = true; # go -- the canonical one; gofumpt adds opinions
          # stylua defaults to tabs at width 4.
          stylua = {
            enable = true; # lua
            settings = {
              indent_type = "Spaces";
              indent_width = 2;
            };
          };

          zig.enable = true; # zig, and .zon
          clang-format.enable = true; # c, c++, glsl
          qmlformat.enable = true; # qml -- ships in kdePackages.qtdeclarative
          cue.enable = true;
          taplo.enable = true; # toml
          xmllint.enable = true; # xml, and .svg
          shfmt.enable = true; # sh, bash, and .envrc
          just.enable = true; # justfiles
          d2.enable = true; # diagram source
          dockerfmt.enable = true;

          # Notebooks are stored with their output cells stripped. This deletes
          # content -- execution results are not recoverable from the file
          # afterwards -- which is the one exception to the rule above, taken
          # because a committed notebook full of base64 images is unreviewable.
          nbstripout.enable = true;

          # Sorts only the regions a file brackets with its start/end directives,
          # so it is inert everywhere the author has not opted in. Naming those
          # directives literally in a comment is enough to trip it, which is why
          # this one talks around them.
          keep-sorted.enable = true;

          # Everything web: js, ts, tsx, jsx, vue, html, css, scss, json, yaml.
          prettier = {
            enable = true;
            # prettier also claims markdown. mdformat is the deliberate choice
            # there, and two formatters on one filetype fight; this settles it.
            excludes = [
              "*.md"
              "*.mdx"
            ];
          };
        };
      };
    in
    {
      # The walker follows the nearest repo: jujutsu where `jj root` answers,
      # git where it does not or where a git repo sits nested inside the jj
      # one, which jujutsu would walk instead. Git reports an untracked nested
      # repo as a single entry, which a formatter then fails to read as a
      # file, so a colocated repo wants the jujutsu walker: it lists tracked
      # files only, so a subrepo stays visible to fd and rg -- which
      # gitignoring it would not -- while staying out of the formatter's way.
      # Once treefmt's `auto` tries jujutsu before git, `--walk auto` can
      # replace this, bar the git-inside-jj case.
      #
      # This belongs on the wrapper rather than in the settings, because the
      # generated config is shared with the formatting check, which runs in a
      # sandbox that git-inits the source. The jujutsu walker has no repo to
      # consult there and exits 1 rather than falling back.
      #
      # Without arguments a project that owns only part of its tree formats
      # just that part, from the repo root so the paths resolve.
      formatter = pkgs.writeShellScriptBin "treefmt" (
        ''
          root=$(jj root --ignore-working-copy 2>/dev/null)
          git=$(git rev-parse --show-toplevel 2>/dev/null)
          if [ -n "$root" ] && [ "''${git#"$root"/}" = "$git" ]; then
            walk=jujutsu
          else
            walk=git root=$git
          fi
        ''
        + lib.optionalString (ownedPaths != null) ''
          if [ $# -eq 0 ]; then
            cd "$root"
            set -- ${lib.escapeShellArgs ownedPaths}
          fi
        ''
        + ''
          exec ${treefmt.config.build.wrapper}/bin/treefmt --walk "$walk" "$@"
        ''
      );

      checks.formatting = treefmt.config.build.check checkRoot;
    };
}
