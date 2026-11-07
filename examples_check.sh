#!/bin/sh
# The examples in Blend's docs (blend-guide): each fenced `blend` block
# of README.md and GUIDE.md a whole module, written into
# results/examples/ at the path its fence names (```blend lib/x.blend),
# then all emitted beside, as a user's would be, those holding laws
# checked by Bend. A fragment goes in an indented block. Run by Blend's
# gate (check.sh).
#
#   examples_check.sh
set -u
cd "$(dirname "$0")" || exit 1
BLEND_ROOT=$PWD
. ./tools.sh
BEND=${BEND:-$(command -v bend || echo "$HOME/.bend/bin/bend")}
# emit checks with it (blend-cli.checks)
export BEND
BLEND=$(BEND=$BEND ./build.sh) || { echo "examples: no executable to check with"; exit 1; }
status=0
said=""
for doc in README.md GUIDE.md; do
  d=$PWD/results/examples/${doc%.md}
  mkdir -p "$d/lib" || exit 1
  # each block's path, one a line, its lines written there; a block
  # naming no path, or one outside, refused
  if ! files=$(awk -v d="$d" '
      /^```blend/ { n++; p = $2; on = 1
        if (p !~ /^(lib\/)?[A-Za-z0-9_-]+\.blend$/) { print FILENAME ": block " n " names no path, or one outside (```blend NAME.blend)" > "/dev/stderr"; bad = 1; f = "/dev/null"; next }
        f = d "/" p; print p; printf "" > f; next }
      /^```/ && on { on = 0; if (f != "/dev/null") close(f); next }
      on { print > f }
      END { exit bad }' "$doc"); then
    status=1
    continue
  fi
  [ -n "$files" ] || { said="$said $doc none,"; continue; }
  # shellcheck disable=SC2086 # one argument a file
  if ! got=$(cd "$d" && "$TOOLS/capped.sh" 1000 120 "$BLEND" emit $files 2>&1 >/dev/null); then
    echo "examples: $doc's do not emit and check:"
    echo "$got"
    status=1
  fi
  said="$said $doc $(echo "$files" | wc -l),"
done
[ "$status" -eq 0 ] && echo "examples:${said%,}: emit and check: ok"
exit "$status"
