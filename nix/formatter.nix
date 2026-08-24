# treefmt owns everything that rewrites files. Only enable formatters whose
# edits are semantics-preserving -- `nix fmt` applies them silently.
#
# Enabling a formatter for a language no project uses costs nothing: treefmt
# matches on filename, so an unused one never runs. The list is therefore
# aspirational rather than a description of what exists today.
{ inputs, self, ... }:
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

          "Manifest.toml" # julia
          "lake-manifest.json"
          "package-lock.json"
          "pnpm-lock.yaml"
          "*.min.js"
          "*.min.css"
        ];

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
      # treefmt's `auto` walker picks git in a colocated repo, and git reports an
      # untracked nested repo as a single entry, which a formatter then fails to
      # read as a file. The jujutsu walker lists tracked files only, so a subrepo
      # stays visible to fd and rg -- which gitignoring it would not -- while
      # staying out of the formatter's way.
      #
      # This belongs on the wrapper rather than in the settings, because the
      # generated config is shared with the formatting check, which runs in a
      # sandbox that git-inits the source. The jujutsu walker has no repo to
      # consult there and exits 1 rather than falling back.
      formatter = pkgs.writeShellScriptBin "treefmt" ''
        exec ${treefmt.config.build.wrapper}/bin/treefmt --walk jujutsu "$@"
      '';

      checks.formatting = treefmt.config.build.check self;
    };
}
