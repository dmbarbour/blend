#!/bin/sh
# The examples in Blend's docs (blend-guide) are samples: each fenced
# `blend` block of README.md and GUIDE.md names one (```blend
# samples/override.blend) and is that file, whole; each run shown after
# it, an indented `$ blend NAME.blend` and the lines below it, is what the
# sample's .out says it prints. samples/check.sh emits and runs every
# sample, check_generated.sh holds its .bend current. Run by Blend's gate
# (check.sh).
#
#   examples_check.sh
set -u
cd "$(dirname "$0")" || exit 1
status=0
said=""
for doc in README.md GUIDE.md; do
  got=$(awk '
    # whether lines a[1..n] are the file at p, each line; -1 where none
    function same(p, a, n,   l, k, r, ok) {
      k = 0; ok = 1
      while ((r = (getline l < p)) > 0) { k++; if (k > n || l != a[k]) ok = 0 }
      close(p)
      if (r < 0) return -1
      return ok && k == n
    }
    function fail(m) { print FILENAME ":" FNR ": " m; bad = 1 }
    function done_run() {
      if (!run) return
      run = 0
      if (dir == "") { fail("a run before any sample"); return }
      r = same(dir runf ".out", o, m)
      if (r < 0) fail("no " dir runf ".out")
      else if (!r) fail("the run of " runf ".blend prints other than " dir runf ".out")
      runs++
    }
    /^```blend/ { done_run(); on = 1; p = $2; n = 0; next }
    on && /^```/ {
      on = 0
      if (p !~ /^samples\//) { fail("a block names no sample (```blend samples/NAME.blend)"); next }
      r = same(p, b, n)
      if (r < 0) fail("no sample " p)
      else if (!r) fail("the block is not " p ", whole")
      dir = p; sub(/[^\/]*$/, "", dir); last = p; blocks++
      next
    }
    on { b[++n] = $0; next }
    /^    \$ blend [^ ]+\.blend$/ {
      done_run(); run = 1; m = 0; runf = $3; sub(/\.blend$/, "", runf)
      if (last !~ ("/" runf "\\.blend$")) fail("the run of " $3 " follows another sample, " last)
      next
    }
    run && /^    / { o[++m] = substr($0, 5); next }
    run { done_run() }
    END { done_run(); print "=" blocks + 0 " " runs + 0; exit bad }' "$doc")
  st=$?
  echo "$got" | grep -v "^=" || true
  [ "$st" -eq 0 ] || status=1
  counts=$(echo "$got" | sed -n 's/^=\([0-9]*\) \([0-9]*\)$/\1 samples, \2 runs/p')
  said="$said $doc $counts;"
done
[ "$status" -eq 0 ] && echo "examples:${said%;}: ok"
exit "$status"
