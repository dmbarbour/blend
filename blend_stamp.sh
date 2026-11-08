#!/bin/sh
# Blend's version stamp (`blend-stamps`): blend.bend's hash, written into
# blend_stamp.bend, which blend.bend imports; the first part of the stamp
# in each file Blend writes. Every change to blend.bend moves it, erring
# toward too many updates: a file Blend wrote is current only for the
# Blend that wrote it. A build stamps the very source it compiles
# (build.sh, through --of), whatever the work tree's blend_stamp.bend
# says, so that a build of sources not yet committed never writes files
# stamped as the Blend committed. The work tree's blend_stamp.bend, for
# the proofs and a run of blend.bend by hand, is generated, never
# edited; the pre-commit hook and the gate verify it, never write it: a
# commit whose stamp is not its blend.bend's is refused until this
# writes it.
#
#   blend_stamp.sh            write blend_stamp.bend for blend.bend as it is
#   blend_stamp.sh --staged   whether the staged one is the staged blend.bend's (the hook)
#   blend_stamp.sh --check    whether it is blend.bend's as it is (the gate)
#   blend_stamp.sh --of FILE  the stamp file for the blend.bend FILE, printed (build.sh)
set -u
sum() { { sha256sum 2>/dev/null || shasum -a 256; } | cut -c1-12; }
text() {
  printf '%s\n' 'import Base' '' \
    "# blend.bend's hash, Blend's version stamp (blend-stamps): generated" \
    '# by blend_stamp.sh, never edited' \
    'def hash() -> String:' "  \"$1\""
}
if [ "${1:-}" = --of ]; then
  [ $# = 2 ] || { echo "usage: blend_stamp.sh --of FILE" >&2; exit 2; }
  h=$(sum < "$2") && [ -n "$h" ] || { echo "blend_stamp.sh: no hash of $2" >&2; exit 1; }
  text "$h"
  exit 0
fi
cd "$(dirname "$0")" || exit 1
f=blend_stamp.bend
case ${1:-} in
  --staged)
    h=$(git show :./blend.bend | sum)
    have=$(git show ":./$f" 2>/dev/null) ;;
  *)
    h=$(sum < blend.bend)
    have=$(cat "$f" 2>/dev/null) ;;
esac
[ -n "$h" ] || { echo "blend_stamp.sh: no hash of blend.bend" >&2; exit 1; }
want=$(text "$h")
[ "$have" = "$want" ] && exit 0
case ${1:-} in
  --staged)
    echo "$f as staged is not the staged blend.bend's hash, $h: run ./blend_stamp.sh, then git add $f"
    exit 1 ;;
  --check)
    echo "$f is not blend.bend's hash, $h: run ./blend_stamp.sh"
    exit 1 ;;
esac
printf '%s\n' "$want" > "$f" || exit 1
