# theaetetus tasks
# usage: nu tasks.nu <task>

def main [] {
    print "usage: nu tasks.nu <task>"
    print ""
    print "tasks:"
    print "  check    verify the project builds or passes basic checks"
    print "  recon    run reconnaissance self-tests and committed sweeps"
}

# Verify the project builds or passes basic checks
def "main check" [] {
    lake build
}

# Run reconnaissance self-tests and committed sweeps (evidence, not proof)
def "main recon" [] {
    uv run recon/harness.py all
    uv run recon/q4.py all
    uv run recon/rigidity.py record --write
}
