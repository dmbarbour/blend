# Sourced by Blend's scripts: TOOLS, where Blend's tools are (capped.sh,
# count.sh, results.py, kept.py, one_law.py, check_docs.py, check_laws.py):
# its own scripts/, else, in a checkout without them, its parent's.
# Needs BLEND_ROOT, Blend's directory.
if [ -d "$BLEND_ROOT/scripts" ]; then
  TOOLS=$BLEND_ROOT/scripts
else
  TOOLS=$(cd "$BLEND_ROOT/.." && pwd)/scripts
fi
