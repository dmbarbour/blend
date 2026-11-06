# Sourced by Blend's scripts: TOOLS, where Blend's tools are (capped.sh,
# count.sh, results.py, kept.py, one_law.py, check_docs.py, check_laws.py):
# its own scripts/, else, in a checkout without them, its parent's.
# Needs BLEND_ROOT, Blend's directory.
if [ -d "$BLEND_ROOT/scripts" ]; then
  TOOLS=$BLEND_ROOT/scripts
else
  TOOLS=$(cd "$BLEND_ROOT/.." && pwd)/scripts
fi
# no update check: Bend prints a newer release's notice beside each
# output, which the samples compare (2.0.40's, 2026-11-06), and a check
# that asks the network is no repeatable one
export BEND_NO_TELEMETRY=1
