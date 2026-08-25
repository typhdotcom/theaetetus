# Conventions

## Tools

### General purpose

`rg`, `fd`, and `jq` are available.

Write scripts & snippets intended for the user to run in idiomatic nushell.
Do not replace your own tool calling with nushell. Your shell is bash.

### uv

For adhoc scripting, prefer python with `uv`.

For a one-off command with third-party packages:

```bash
uv run --with numpy --with mpmath -- python -c '...'
```

For any script saved to disk, declare its dependencies using inline script
metadata.

```bash
uv init --script script.py
uv add --script script.py numpy
uv run script.py
```

Use uvx for Python CLI applications such as `ruff`.

## Nix flakes

For libraries needed for a project, make them available in the devshell. Don't
be conservative- the user appreciates using the best tool for the job.

If a tool is general purpose, consider asking the user to add it to the nixos
config (~/nixos).

## Template

When a Copier update conflicts, understand why the project and template
diverged before resolving the text. Raise anything the conflict reveals beyond
this project.

## Flake layout

`flake.nix` imports every `*.nix` file in `nix/` as a flake-parts module.
Extend the flake by adding a file there, or by editing `nix/devshell.nix`,
which belongs to the project. The other modules come from the project
template; edits to them are legal but merge three-way on `copier update`.

`nix/formatter.nix` provides treefmt. Run with `nix fmt`.

`nix/checks.nix` provides general purpose checks. Run with `nix flake check`:

- `formatting` - treefmt
- `statix`, `deadnix` - linting
- `gitleaks` - secrets
- `shellcheck`, `actionlint` - shell scripts, CI workflows
- `markers` - unfinished-work markers (TODO, etc.)

## VCS

All repos use jujutsu. Edits and renames are tracked automatically.

```bash
jj status
jj diff --git
jj commit -m "foo"  # describe + new, usually desired
```

Trying to call git will result in a permission denial.

Do not explain to the user how jj works, they know already.

In general, commit proactively. It's easier for the user to squash/fix
premature commits than it is to converse about when to commit. Keep
descriptions concise and intent-based (ie don't re-explain what the diff
already says).

### Commit process

- Update the README.md if it's stale.
- Bump any version the change makes stale.
- Run `nix flake check`.
- Commit.

## Documentation

Where a thing is written decides how far it travels. CONVENTIONS.md arrives
from the template and reaches every project through it; AGENTS.md reaches the
agents working in this one, and CLAUDE.md points at it; README.md reaches
whoever reads the repo.

A general convention written into this copy of CONVENTIONS.md reaches only
this project and conflicts on the next update. Where it should reach instead
is the question worth raising — the template, a plugin, the nixos config, a
check that enforces it rather than prose that asks.

Keep the README.md about the project as it exists at time of commit. Don't
use it to record history. Don't treat it like part of a conversation. This also
goes for code comments. Be concise and high signal, code is hard to read if
there's multiline commentary everywhere.

## Tips

- When in doubt about API surfaces, bugs, etc, prefer `--help` flags, man
  pages, and available source over guess-and-check, web searches, etc. If
  you're working with it, it's probably on disk, and the answer within will be
  unambiguous. Do not interpret this as a reason to vet every surface before
  using it, often it's faster to follow instinct and check the result.
- The user does not ask rhetorical questions. If they ask a question, they want
  an answer.
