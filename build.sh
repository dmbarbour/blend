#!/bin/sh
# Builds Blend natively, once for each version of its sources and of Bend,
# into results/build/ (out of git), and prints the executable's path. A
# run of the executable takes milliseconds, where `bend blend.bend ...`
# checks and compiles the tool again each time (1.3 s a run, 2026-11-04);
# the build takes 13 s and 0.4 GB.
#
# It compiles a copy of Blend's sources staged in results/build/src,
# their stamp written there from the blend.bend copied (blend_stamp.sh
# --of), so that a build carries the version stamp of the very source it
# compiles, whatever the work tree's blend_stamp.bend says, and the work
# tree is never written (`blend-stamps`).
#
#   build.sh          the executable's path, built first if stale
#   build.sh --force  the same, built again whatever the key (`blend
#                     rebuild`)
#   build.sh --stage  the sources staged alone, the staged blend.bend's
#                     path printed, for a run through bend (launcher.sh)
#   run.sh ARGS...    the executable run (run.sh show --resolve F.blend)
set -u
force=0
[ "${1:-}" = --force ] && force=1
cd "$(dirname "$0")" || exit 1
BLEND_ROOT=$PWD
. ./tools.sh
BEND=${BEND:-$(command -v bend || echo "$HOME/.bend/bin/bend")}
out=results/build
# Blend's sources staged: each Bend source but its laws, proofs and stamp
# (LAWS.bend, PROOF.bend: no part of the tool; blend_stamp.bend: written
# from blend.bend), then the stamp
stage() {
  mkdir -p "$out/src" || exit 1
  for f in *.bend; do
    case $f in *LAWS.bend | *PROOF.bend | blend_stamp.bend) ;; *) cp "$f" "$out/src/$f" || exit 1 ;; esac
  done
  ./blend_stamp.sh --of "$out/src/blend.bend" > "$out/src/blend_stamp.bend" || exit 1
}
if [ "${1:-}" = --stage ]; then
  stage
  echo "$PWD/$out/src/blend.bend"
  exit 0
fi
# the key: Bend itself (its version; its executable's size, time and
# inode, cheaper than hashing 80 MB on every run; its Base and effects
# beside it) and every Bend source of Blend's staged, the stamp following
# from blend.bend, so that an update of Bend, in place or not, rebuilds
# the tool
exe=$(command -v "$BEND" 2>/dev/null) || { echo "blend: no bend at $BEND" >&2; exit 1; }
real=$(readlink -f "$exe")
lib=$(dirname "$real")/../bend2
key=$({ "$BEND" version; stat -c '%s %Y %i' "$real"; cat "$lib"/base.bend "$lib"/effs/* 2>/dev/null
  for f in *.bend; do case $f in *LAWS.bend | *PROOF.bend | blend_stamp.bend) ;; *) cat "$f" ;; esac; done; } |
  sha256sum | cut -d' ' -f1)
if [ "$force" = 1 ] || [ ! -x "$out/blend" ] || [ "$(cat "$out/key" 2>/dev/null)" != "$key" ]; then
  echo "blend: building the tool natively, once for each version of Blend and of Bend" >&2
  stage
  "$TOOLS/capped.sh" 1500 300 "$BEND" "$out/src/blend.bend" -o "$out/blend.new" >&2 || {
    echo "blend: the build failed" >&2; exit 1; }
  mv "$out/blend.new" "$out/blend" && echo "$key" > "$out/key" || exit 1
fi
echo "$PWD/$out/blend"
