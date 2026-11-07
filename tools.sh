# Sourced by Blend's scripts: TOOLS, where Blend's tools are (capped.sh,
# count.sh, results.py, kept.py, one_law.py, check_docs.py, check_laws.py),
# its own scripts/ (`blend-own-repository`). Needs BLEND_ROOT, Blend's
# directory.
TOOLS=$BLEND_ROOT/scripts
# no update check: Bend prints a newer release's notice beside each
# output, which the samples compare (2.0.40's, 2026-11-06), and a check
# that asks the network is no repeatable one
export BEND_NO_TELEMETRY=1
