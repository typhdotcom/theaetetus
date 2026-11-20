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
    uv run recon/q3.py selftest
    uv run recon/q3.py pair --q 2 --bound 4 --write
    uv run recon/q3.py pair --q 3 --bound 6 --write
    uv run recon/q3.py pair --pair as1_as2 --q 2 --bound 80 --write
    uv run recon/q3.py pair --pair as1_as2 --q 13 --bound 200 --write
    uv run recon/q3field.py selftest
    uv run recon/q3field.py sweep --write
    uv run recon/q3roots.py --write
    uv run recon/q3survey.py --write
    uv run recon/q3odd.py --q 3 --bound 8 --write
    sage -python recon/q3genus.py --rank 4 --max-det 2000 --write
}

# Rewrite the tree with the flake's formatters
def "main fmt" [] {
    nix fmt
}
