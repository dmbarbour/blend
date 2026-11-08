#!/bin/sh
# Blend's generated files match what Blend writes now (glam-in-bend's
# `generated-sources`): `blend deps --bytes` emits each sample module in
# memory and compares it with its file, its stamp and its bytes, each
# module's one file, its laws and proofs in it (`blend-laws-in-module`),
# a laws or proofs file of the Blend before, left beside a sample, stale
# too; and blend_stamp.bend, blend.bend's hash (blend_stamp.sh,
# `blend-stamps`), verified as the hook does, so
# that every change to Blend leaves each sample stale until written
# again. Checks, never writes: a stale file fails, and regenerating it is
# the developer's step. Run by
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
      stale|missing) echo "$dir/$mod is $state: regenerate it (cd $dir && $up/run.sh emit --alone --force $mod)" ;;
      *) echo "$state $mod" ;;
    esac
  done
}

./blend_stamp.sh --check || status=1

blend_check samples family.blend nested.blend override.blend prior.blend sharing.blend choice.blend types.blend imports.blend family-nested.blend nested-reach.blend laws.blend laws-imported.blend declares.blend templates.blend monoid.blend namespaces.blend wide.blend lib/shapes.blend lib/adds.blend lib/dims.blend lib/wide.blend
exit "$status"
