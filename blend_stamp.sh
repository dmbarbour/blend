#!/bin/sh
# Blend's version stamp (`blend-stamps`): blend.bend's hash, written into
# blend_stamp.bend, which blend.bend imports; the first part of the stamp
# in each file Blend writes. Every change to blend.bend moves it, erring
# toward too many updates: a file Blend wrote is current only for the
# Blend that wrote it. blend_stamp.bend is generated, never edited: where
# git finds it changed since the last commit, to other than this writes
# now or wrote last (results/blend_stamp.last, out of git), this refuses,
# the gate with it, so that the change is reviewed, never overwritten.
# The pre-commit hook writes and stages it for blend.bend as staged; the
# gate (check_generated.sh) checks it.
#
#   blend_stamp.sh            write blend_stamp.bend for blend.bend as it is
#   blend_stamp.sh --staged   for blend.bend as staged, and stage it
#   blend_stamp.sh --check    whether blend_stamp.bend is blend.bend's
set -u
cd "$(dirname "$0")" || exit 1
f=blend_stamp.bend
last=results/blend_stamp.last
sum() { { sha256sum 2>/dev/null || shasum -a 256; } | cut -c1-12; }
case ${1:-} in
  --staged) h=$(git show :./blend.bend | sum) ;;
  *) h=$(sum < blend.bend) ;;
esac
[ -n "$h" ] || { echo "blend_stamp.sh: no hash of blend.bend" >&2; exit 1; }
want=$(printf '%s\n' 'import Base' '' \
  "# blend.bend's hash, Blend's version stamp (blend-stamps): generated" \
  '# by blend_stamp.sh, never edited' \
  'def hash() -> String:' "  \"$h\"")
have=$(cat "$f" 2>/dev/null)
if [ "$have" = "$want" ]; then
  [ "${1:-}" = --staged ] && { git add "$f" || exit 1; }
  exit 0
fi
# changed since the last commit, and not by this: a change to review
if [ -e "$f" ] && [ -n "$(git status --porcelain -- "$f" 2>/dev/null)" ] && [ "$have" != "$(cat "$last" 2>/dev/null)" ]; then
  echo "$f has changes since the last commit that blend_stamp.sh did not make: review them (git diff HEAD -- $f); to discard them, git checkout HEAD -- $f, then ./blend_stamp.sh"
  exit 1
fi
if [ "${1:-}" = --check ]; then
  echo "$f is not blend.bend's hash, $h: run ./blend_stamp.sh (the pre-commit hook does)"
  exit 1
fi
printf '%s\n' "$want" > "$f" || exit 1
mkdir -p results && printf '%s\n' "$want" > "$last" || exit 1
[ "${1:-}" = --staged ] && { git add "$f" || exit 1; }
exit 0
