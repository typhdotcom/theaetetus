# theaetetus tasks
# usage: nu tasks.nu <task>

def main [] {
    print "usage: nu tasks.nu <task>"
    print ""
    print "tasks:"
    print "  check    evaluate the flake, then build the Lean library"
    print "  recon    run reconnaissance self-tests and committed sweeps"
    print "  fmt      rewrite the tree with the flake's formatters"
}

# Evaluate the flake, then build the Lean library
def "main check" [] {
    nix flake check
    lake build
}

# Run reconnaissance self-tests and committed sweeps (evidence, not proof)
def "main recon" [] {
    uv run recon/harness.py all
    uv run recon/q4.py all
    uv run recon/rigidity.py record --write
    uv run recon/logfourier.py sweep --write
}

# Rewrite the tree with the flake's formatters
def "main fmt" [] {
    nix fmt
}
