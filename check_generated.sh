#!/bin/sh
# Blend's generated files match what Blend writes now (glam-in-bend's
# `generated-sources`): `blend deps --bytes` emits each sample module in
# memory and compares it with its file, its stamp and its bytes, each
# module's one file, its laws and proofs in it (`blend-laws-in-module`),
# a laws or proofs file of the Blend before, left beside a sample, stale
# too. A file that changed while its stamp stayed as HEAD has it is
# Blend's output changed under one format, which must then be bumped
# (`blend-stamps`). Checks, never writes: a stale file fails, and
# regenerating it is the developer's step. Run by
# Blend's gate (check.sh) and by the pre-commit hooks, Blend's and
# glam-in-bend's. Blend runs built (build.sh): its build, 13 s, comes
# once for each version of its sources.
#
#   check_generated.sh
set -u
cd "$(dirname "$0")" || exit 1
root=$PWD
status=0

# one directory's modules, each current or the step to make it so
blend_check() {
  dir=$1
  shift
  up=$(echo "$dir" | sed 's#[^/][^/]*#..#g')
  got=$(cd "$dir" && "$root/run.sh" deps --bytes "$@" 2>&1) || status=1
  echo "$got" | while read -r state mod; do
    case $state in
      current) echo "$dir/${mod%.blend}.bend: matches blend" ;;
      stale|missing) echo "$dir/$mod is $state: regenerate it (cd $dir && $up/run.sh emit --alone $mod)" ;;
      *) echo "$state $mod" ;;
    esac
  done
  # changed, its stamp as HEAD's: Blend's output changed under one format
  for mod in "$@"; do
    f=$dir/${mod%.blend}.bend
    old=$(git show "HEAD:./$f" 2>/dev/null) || continue
    [ "$(echo "$old" | sed -n 2p)" = "$(sed -n 2p "$f")" ] || continue
    [ "$old" = "$(cat "$f")" ] ||
      { echo "$f changed while its stamp stayed as HEAD has it: Blend's output changed under format $(sed -n 2p "$f" | cut -d' ' -f4); bump blend.format"; status=1; }
  done
}

blend_check samples family.blend nested.blend override.blend prior.blend sharing.blend choice.blend types.blend imports.blend family-nested.blend nested-reach.blend laws.blend laws-imported.blend declares.blend templates.blend monoid.blend namespaces.blend lib/shapes.blend lib/adds.blend lib/dims.blend
exit "$status"
