# theaetetus tasks
# usage: nu tasks.nu <task>

def main [] {
    print "usage: nu tasks.nu <task>"
    print ""
    print "tasks:"
    print "  check    verify the project builds or passes basic checks"
}

# Verify the project builds or passes basic checks
def "main check" [] {
    lake build
}
